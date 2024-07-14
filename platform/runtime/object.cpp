/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/object.h"
#include "runtime/buffer.h"
#include "runtime/debug.h"
#include "runtime/hash.h"
#include "runtime/utf8.h"
#include <algorithm>
#include <cmath>
#include <lean/lean.h>
#include <string>
#include <vector>

// HACK: for unknown reasons, std::isnan(x) fails on msys64 because math.h
// is imported and isnan(x) looks like a macro. On the other hand, isnan(x)
// fails on linux because <cmath> doesn't define it (as expected).
// So we declare isnan(x) as a macro for std::isnan(x) if it doesn't already
// exist.
#ifndef isnan
#define isnan(x) std::isnan(x)
#endif
#ifndef isfinite
#define isfinite(x) std::isfinite(x)
#endif
#ifndef isinf
#define isinf(x) std::isinf(x)
#endif

namespace lean {

extern "C" LEAN_EXPORT void lean_internal_panic(char const *msg) {
  fprintf(stderr, "INTERNAL PANIC: %s\n", msg);
  abort();
}

extern "C" LEAN_EXPORT void lean_internal_panic_out_of_memory() {
  lean_internal_panic("out of memory");
}

extern "C" LEAN_EXPORT void lean_internal_panic_unreachable() {
  lean_internal_panic("unreachable code has been reached");
}

extern "C" LEAN_EXPORT void lean_internal_panic_rc_overflow() {
  lean_internal_panic("reference counter overflowed");
}

extern "C" LEAN_EXPORT object *lean_panic_fn(object *default_val, object *msg) {
  std::exit(1);
  lean_dec(msg);
  return default_val;
}

extern "C" LEAN_EXPORT object *lean_sorry(uint8) {
  lean_internal_panic("executed 'sorry'");
  lean_unreachable();
}

static inline void lean_dealloc(lean_object *o, size_t sz) { free(o); }

extern "C" LEAN_EXPORT void lean_free_object(lean_object *o) {
  switch (lean_ptr_tag(o)) {
  case LeanArray:
    return lean_dealloc(o, lean_array_byte_size(o));
  case LeanScalarArray:
    return lean_dealloc(o, lean_sarray_byte_size(o));
  case LeanString:
    return lean_dealloc(o, lean_string_byte_size(o));
  case LeanMPZ:
    to_mpz(o)->m_value.~mpz();
    return lean_free_small_object(o);
  default:
    return lean_free_small_object(o);
  }
}

static inline lean_object *get_next(lean_object *o) {
  if (sizeof(void *) == 8) {
    size_t header = ((size_t *)o)[0];
    LEAN_BYTE(header, 7) = 0;
    LEAN_BYTE(header, 6) = 0;
    return (lean_object *)(header);
  } else {
    // 32-bit version
    return ((lean_object **)o)[0];
  }
}

static inline void set_next(lean_object *o, lean_object *n) {
  if (sizeof(void *) == 8) {
    size_t new_header = (size_t)n;
    LEAN_BYTE(new_header, 7) = o->m_tag;
    LEAN_BYTE(new_header, 6) = o->m_other;
    ((size_t *)o)[0] = new_header;
    lean_assert(get_next(o) == n);
  } else {
    // 32-bit version
    ((lean_object **)o)[0] = n;
  }
}

static inline void push_back(lean_object *&todo, lean_object *v) {
  set_next(v, todo);
  todo = v;
}

static inline lean_object *pop_back(lean_object *&todo) {
  lean_object *r = todo;
  todo = get_next(todo);
  return r;
}

static inline void dec(lean_object *o, lean_object *&todo) {
  if (lean_is_scalar(o))
    return;
  if (LEAN_LIKELY(o->m_rc > 1)) {
    o->m_rc--;
  } else if (o->m_rc == 1) {
    push_back(todo, o);
  }
}

static void lean_del_core(object *o, object *&todo);

extern "C" LEAN_EXPORT lean_object *lean_alloc_object(size_t sz) {
  void *r = malloc(sz);
  if (r == nullptr)
    lean_internal_panic_out_of_memory();
  return (lean_object *)r;
}

static void lean_del_core(object *o, object *&todo) {
  uint8 tag = lean_ptr_tag(o);
  if (tag <= LeanMaxCtorTag) {
    object **it = lean_ctor_obj_cptr(o);
    object **end = it + lean_ctor_num_objs(o);
    for (; it != end; ++it)
      dec(*it, todo);
    lean_free_small_object(o);
  } else {
    switch (tag) {
    case LeanClosure: {
      object **it = lean_closure_arg_cptr(o);
      object **end = it + lean_closure_num_fixed(o);
      for (; it != end; ++it)
        dec(*it, todo);
      lean_free_small_object(o);
      break;
    }
    case LeanArray: {
      object **it = lean_array_cptr(o);
      object **end = it + lean_array_size(o);
      for (; it != end; ++it)
        dec(*it, todo);
      lean_dealloc(o, lean_array_byte_size(o));
      break;
    }
    case LeanScalarArray:
      lean_dealloc(o, lean_sarray_byte_size(o));
      break;
    case LeanString:
      lean_dealloc(o, lean_string_byte_size(o));
      break;
    case LeanMPZ:
      to_mpz(o)->m_value.~mpz();
      lean_free_small_object(o);
      break;
    case LeanThunk:
      if (object *c = lean_to_thunk(o)->m_closure)
        dec(c, todo);
      if (object *v = lean_to_thunk(o)->m_value)
        dec(v, todo);
      lean_free_small_object(o);
      break;
    case LeanRef:
      if (object *v = lean_to_ref(o)->m_value)
        dec(v, todo);
      lean_free_small_object(o);
      break;
    case LeanExternal:
      lean_to_external(o)->m_class->m_finalize(lean_to_external(o)->m_data);
      lean_free_small_object(o);
      break;
    default:
      lean_unreachable();
    }
  }
}

extern "C" LEAN_EXPORT void lean_dec_ref_cold(lean_object *o) {
  if (o->m_rc == 1) {
    object *todo = nullptr;
    while (true) {
      lean_del_core(o, todo);
      if (todo == nullptr)
        return;
      o = pop_back(todo);
    }
  }
}

// =======================================
// Arrays
static object *g_array_empty = nullptr;

object *array_mk_empty() { return g_array_empty; }

extern "C" object *lean_list_to_array(object *, object *);
extern "C" object *lean_array_to_list(object *, object *);

extern "C" LEAN_EXPORT object *lean_array_mk(lean_obj_arg lst) {
  return lean_list_to_array(lean_box(0), lst);
}

extern "C" LEAN_EXPORT lean_object *lean_array_data(lean_obj_arg a) {
  return lean_array_to_list(lean_box(0), a);
}

extern "C" LEAN_EXPORT lean_obj_res lean_array_get_panic(lean_obj_arg def_val) {
  return lean_panic_fn(def_val, lean_mk_string("Error: index out of bounds"));
}

extern "C" LEAN_EXPORT lean_obj_res lean_array_set_panic(lean_obj_arg a,
                                                         lean_obj_arg v) {
  lean_dec(v);
  return lean_panic_fn(a, lean_mk_string("Error: index out of bounds"));
}

// =======================================
// Thunks

extern "C" LEAN_EXPORT b_obj_res lean_thunk_get_core(b_obj_arg t) {
  object *c = lean_to_thunk(t)->m_closure;
  lean_to_thunk(t)->m_closure = nullptr;
  if (c != nullptr) {
    /* Recall that a closure uses the standard calling convention.
       `thunk_get` "consumes" the result `r` by storing it at
       `to_thunk(t)->m_value`. Then, it returns a reference to this result to
       the caller. The behavior is compatible with `cnstr_obj` with also returns
       a reference to be object stored in the constructor object.

       Recall that `apply_1` also consumes `c`'s RC. */
    object *r = lean_apply_1(c, lean_box(0));
    lean_assert(r != nullptr); /* Closure must return a valid lean object */
    lean_assert(lean_to_thunk(t)->m_value == nullptr);
    // mark_mt(r);
    lean_to_thunk(t)->m_value = r;
    return r;
  } else {
    lean_assert(c == nullptr);
    /* There is another thread executing the closure. We keep waiting for the
       m_value to be set by another thread. */
    while (!lean_to_thunk(t)->m_value) {
    }
    return lean_to_thunk(t)->m_value;
  }
}

// =======================================
// Mark Persistent

extern "C" void lean_mark_persistent(object *o);

static obj_res mark_persistent_fn(obj_arg o) {
  lean_mark_persistent(o);
  return lean_box(0);
}

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#include <sanitizer/lsan_interface.h>
#endif
#endif

extern "C" LEAN_EXPORT void lean_mark_persistent(object *o) {
  buffer<object *> todo;
  todo.push_back(o);
  while (!todo.empty()) {
    object *o = todo.back();
    todo.pop_back();
    if (!lean_is_scalar(o) && lean_has_rc(o)) {
      o->m_rc = 0;
#if defined(__has_feature)
#if __has_feature(address_sanitizer)
      // do not report as leak
      // NOTE: Most persistent objects are actually reachable from global
      // variables up to the end of the process. However, this is *not*
      // true for closures inside of persistent thunks, which are
      // "orphaned" after being evaluated.
      __lsan_ignore_object(o);
#endif
#endif
      uint8_t tag = lean_ptr_tag(o);
      if (tag <= LeanMaxCtorTag) {
        object **it = lean_ctor_obj_cptr(o);
        object **end = it + lean_ctor_num_objs(o);
        for (; it != end; ++it)
          todo.push_back(*it);
      } else {
        switch (tag) {
        case LeanScalarArray:
        case LeanString:
        case LeanMPZ:
          break;
        case LeanExternal: {
          object *fn = lean_alloc_closure((void *)mark_persistent_fn, 1, 0);
          lean_to_external(o)->m_class->m_foreach(lean_to_external(o)->m_data,
                                                  fn);
          lean_dec(fn);
          break;
        }
        case LeanClosure: {
          object **it = lean_closure_arg_cptr(o);
          object **end = it + lean_closure_num_fixed(o);
          for (; it != end; ++it)
            todo.push_back(*it);
          break;
        }
        case LeanArray: {
          object **it = lean_array_cptr(o);
          object **end = it + lean_array_size(o);
          for (; it != end; ++it)
            todo.push_back(*it);
          break;
        }
        case LeanThunk:
          if (object *c = lean_to_thunk(o)->m_closure)
            todo.push_back(c);
          if (object *v = lean_to_thunk(o)->m_value)
            todo.push_back(v);
          break;
        case LeanRef:
          if (object *v = lean_to_ref(o)->m_value)
            todo.push_back(v);
          break;
        default:
          lean_unreachable();
          break;
        }
      }
    }
  }
}

// =======================================
// Natural numbers

object *alloc_mpz(mpz const &m) {
  void *mem = lean_alloc_small_object(sizeof(mpz_object));
  mpz_object *o = new (mem) mpz_object(m);
  lean_set_st_header((lean_object *)o, LeanMPZ, 0);
  return (lean_object *)o;
}

object *mpz_to_nat_core(mpz const &m) {
  lean_assert(!m.is_size_t() || m.get_size_t() > LEAN_MAX_SMALL_NAT);
  return alloc_mpz(m);
}

static inline obj_res mpz_to_nat(mpz const &m) {
  if (m.is_size_t() && m.get_size_t() <= LEAN_MAX_SMALL_NAT)
    return lean_box(m.get_size_t());
  else
    return mpz_to_nat_core(m);
}

extern "C" LEAN_EXPORT object *lean_cstr_to_nat(char const *n) {
  return mpz_to_nat(mpz(n));
}

extern "C" LEAN_EXPORT object *lean_big_usize_to_nat(size_t n) {
  if (n <= LEAN_MAX_SMALL_NAT) {
    return lean_box(n);
  } else {
    return mpz_to_nat_core(mpz::of_size_t(n));
  }
}

extern "C" LEAN_EXPORT object *lean_big_uint64_to_nat(uint64_t n) {
  if (LEAN_LIKELY(n <= LEAN_MAX_SMALL_NAT)) {
    return lean_box(n);
  } else {
    return mpz_to_nat_core(mpz(n));
  }
}

extern "C" LEAN_EXPORT object *lean_nat_big_succ(object *a) {
  return mpz_to_nat_core(mpz_value(a) + 1);
}

extern "C" LEAN_EXPORT object *lean_nat_big_add(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1))
    return mpz_to_nat_core(mpz::of_size_t(lean_unbox(a1)) + mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_nat_core(mpz_value(a1) + mpz::of_size_t(lean_unbox(a2)));
  else
    return mpz_to_nat_core(mpz_value(a1) + mpz_value(a2));
}

extern "C" LEAN_EXPORT object *lean_nat_big_sub(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1)) {
    lean_assert(mpz::of_size_t(lean_unbox(a1)) < mpz_value(a2));
    return lean_box(0);
  } else if (lean_is_scalar(a2)) {
    lean_assert(mpz_value(a1) > mpz::of_size_t(lean_unbox(a2)));
    return mpz_to_nat(mpz_value(a1) - mpz::of_size_t(lean_unbox(a2)));
  } else {
    if (mpz_value(a1) < mpz_value(a2))
      return lean_box(0);
    else
      return mpz_to_nat(mpz_value(a1) - mpz_value(a2));
  }
}

extern "C" LEAN_EXPORT object *lean_nat_big_mul(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1))
    return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) * mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_nat(mpz_value(a1) * mpz::of_size_t(lean_unbox(a2)));
  else
    return mpz_to_nat_core(mpz_value(a1) * mpz_value(a2));
}

extern "C" LEAN_EXPORT object *lean_nat_overflow_mul(size_t a1, size_t a2) {
  return mpz_to_nat(mpz::of_size_t(a1) * mpz::of_size_t(a2));
}

extern "C" LEAN_EXPORT object *lean_nat_big_div(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1)) {
    lean_assert(mpz_value(a2) != 0);
    lean_assert(mpz::of_size_t(lean_unbox(a1)) / mpz_value(a2) == 0);
    return lean_box(0);
  } else if (lean_is_scalar(a2)) {
    usize n2 = lean_unbox(a2);
    return n2 == 0 ? a2 : mpz_to_nat(mpz_value(a1) / mpz::of_size_t(n2));
  } else {
    lean_assert(mpz_value(a2) != 0);
    return mpz_to_nat(mpz_value(a1) / mpz_value(a2));
  }
}

extern "C" LEAN_EXPORT object *lean_nat_big_mod(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1)) {
    lean_assert(mpz_value(a2) != 0);
    return a1;
  } else if (lean_is_scalar(a2)) {
    usize n2 = lean_unbox(a2);
    if (n2 == 0) {
      lean_inc(a1);
      return a1;
    } else {
      return mpz_to_nat(mpz_value(a1) % mpz::of_size_t(n2));
    }
  } else {
    lean_assert(mpz_value(a2) != 0);
    return mpz_to_nat(mpz_value(a1) % mpz_value(a2));
  }
}

extern "C" LEAN_EXPORT bool lean_nat_big_eq(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    lean_assert(mpz::of_size_t(lean_unbox(a1)) != mpz_value(a2));
    return false;
  } else if (lean_is_scalar(a2)) {
    lean_assert(mpz_value(a1) != mpz::of_size_t(lean_unbox(a2)));
    return false;
  } else {
    return mpz_value(a1) == mpz_value(a2);
  }
}

extern "C" LEAN_EXPORT bool lean_nat_big_le(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    lean_assert(mpz::of_size_t(lean_unbox(a1)) < mpz_value(a2)) return true;
  } else if (lean_is_scalar(a2)) {
    lean_assert(mpz_value(a1) > mpz::of_size_t(lean_unbox(a2)));
    return false;
  } else {
    return mpz_value(a1) <= mpz_value(a2);
  }
}

extern "C" LEAN_EXPORT bool lean_nat_big_lt(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    lean_assert(mpz::of_size_t(lean_unbox(a1)) < mpz_value(a2));
    return true;
  } else if (lean_is_scalar(a2)) {
    lean_assert(mpz_value(a1) > mpz::of_size_t(lean_unbox(a2)));
    return false;
  } else {
    return mpz_value(a1) < mpz_value(a2);
  }
}

extern "C" LEAN_EXPORT object *lean_nat_big_land(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1))
    return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) & mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_nat(mpz_value(a1) & mpz::of_size_t(lean_unbox(a2)));
  else
    return mpz_to_nat(mpz_value(a1) & mpz_value(a2));
}

extern "C" LEAN_EXPORT object *lean_nat_big_lor(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1))
    return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) | mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_nat(mpz_value(a1) | mpz::of_size_t(lean_unbox(a2)));
  else
    return mpz_to_nat(mpz_value(a1) | mpz_value(a2));
}

extern "C" LEAN_EXPORT object *lean_nat_big_xor(object *a1, object *a2) {
  lean_assert(!lean_is_scalar(a1) || !lean_is_scalar(a2));
  if (lean_is_scalar(a1))
    return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)) ^ mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_nat(mpz_value(a1) ^ mpz::of_size_t(lean_unbox(a2)));
  else
    return mpz_to_nat(mpz_value(a1) ^ mpz_value(a2));
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_shiftl(b_lean_obj_arg a1,
                                                    b_lean_obj_arg a2) {
  // Special case for shifted value is 0.
  if (lean_is_scalar(a1) && lean_unbox(a1) == 0) {
    return lean_box(0);
  }
  auto a = lean_is_scalar(a1) ? mpz::of_size_t(lean_unbox(a1)) : mpz_value(a1);
  if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
    lean_internal_panic("Nat.shiftl exponent is too big");
  }
  mpz r;
  mul2k(r, a, lean_unbox(a2));
  return mpz_to_nat(r);
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_shiftr(b_lean_obj_arg a1,
                                                    b_lean_obj_arg a2) {
  if (!lean_is_scalar(a2)) {
    return lean_box(0); // This large of an exponent must be 0.
  }
  auto a = lean_is_scalar(a1) ? mpz::of_size_t(lean_unbox(a1)) : mpz_value(a1);
  size_t s = lean_unbox(a2);
  // If the shift amount is large, then we fail if it is not large
  // enough to zero out all the bits.
  if (s > UINT_MAX) {
    if (a.log2() >= s) {
      lean_internal_panic("Nat.shiftr exponent is too big");
    } else {
      return lean_box(0);
    }
  }
  mpz r;
  div2k(r, a, s);
  return mpz_to_nat(r);
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_pow(b_lean_obj_arg a1,
                                                 b_lean_obj_arg a2) {
  if (!lean_is_scalar(a2) || lean_unbox(a2) > UINT_MAX) {
    lean_internal_panic("Nat.pow exponent is too big");
  }
  if (lean_is_scalar(a1))
    return mpz_to_nat(mpz::of_size_t(lean_unbox(a1)).pow(lean_unbox(a2)));
  else
    return mpz_to_nat(mpz_value(a1).pow(lean_unbox(a2)));
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_gcd(b_lean_obj_arg a1,
                                                 b_lean_obj_arg a2) {
  if (lean_is_scalar(a1)) {
    if (lean_is_scalar(a2))
      return mpz_to_nat(
          gcd(mpz::of_size_t(lean_unbox(a1)), mpz::of_size_t(lean_unbox(a2))));
    else
      return mpz_to_nat(gcd(mpz::of_size_t(lean_unbox(a1)), mpz_value(a2)));
  } else {
    if (lean_is_scalar(a2))
      return mpz_to_nat(gcd(mpz_value(a1), mpz::of_size_t(lean_unbox(a2))));
    else
      return mpz_to_nat(gcd(mpz_value(a1), mpz_value(a2)));
  }
}

extern "C" LEAN_EXPORT lean_obj_res lean_nat_log2(b_lean_obj_arg a) {
  if (lean_is_scalar(a)) {
    unsigned res = 0;
    size_t n = lean_unbox(a);
    while (n >= 2) {
      res++;
      n /= 2;
    }
    return lean_box(res);
  } else {
    return lean_box(mpz_value(a).log2());
  }
}

// =======================================
// Integers

inline object *mpz_to_int_core(mpz const &m) {
  lean_assert(m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT);
  return alloc_mpz(m);
}

static object *mpz_to_int(mpz const &m) {
  if (m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT)
    return mpz_to_int_core(m);
  else
    return lean_box(static_cast<unsigned>(m.get_int()));
}

extern "C" LEAN_EXPORT lean_obj_res lean_big_int_to_nat(lean_obj_arg a) {
  lean_assert(!lean_is_scalar(a));
  mpz m = mpz_value(a);
  lean_dec(a);
  return mpz_to_nat(m);
}

extern "C" LEAN_EXPORT object *lean_cstr_to_int(char const *n) {
  return mpz_to_int(mpz(n));
}

extern "C" LEAN_EXPORT object *lean_big_int_to_int(int n) {
  return alloc_mpz(mpz(n));
}

extern "C" LEAN_EXPORT object *lean_big_size_t_to_int(size_t n) {
  return alloc_mpz(mpz::of_size_t(n));
}

extern "C" LEAN_EXPORT object *lean_big_int64_to_int(int64_t n) {
  if (LEAN_LIKELY(LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT)) {
    return lean_box(static_cast<unsigned>(static_cast<int>(n)));
  } else {
    return mpz_to_int_core(mpz(n));
  }
}

extern "C" LEAN_EXPORT object *lean_int_big_neg(object *a) {
  return mpz_to_int(neg(mpz_value(a)));
}

extern "C" LEAN_EXPORT object *lean_int_big_add(object *a1, object *a2) {
  if (lean_is_scalar(a1))
    return mpz_to_int(lean_scalar_to_int(a1) + mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_int(mpz_value(a1) + lean_scalar_to_int(a2));
  else
    return mpz_to_int(mpz_value(a1) + mpz_value(a2));
}

extern "C" LEAN_EXPORT object *lean_int_big_sub(object *a1, object *a2) {
  if (lean_is_scalar(a1))
    return mpz_to_int(lean_scalar_to_int(a1) - mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_int(mpz_value(a1) - lean_scalar_to_int(a2));
  else
    return mpz_to_int(mpz_value(a1) - mpz_value(a2));
}

extern "C" LEAN_EXPORT object *lean_int_big_mul(object *a1, object *a2) {
  if (lean_is_scalar(a1))
    return mpz_to_int(lean_scalar_to_int(a1) * mpz_value(a2));
  else if (lean_is_scalar(a2))
    return mpz_to_int(mpz_value(a1) * lean_scalar_to_int(a2));
  else
    return mpz_to_int(mpz_value(a1) * mpz_value(a2));
}

extern "C" LEAN_EXPORT object *lean_int_big_div(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    return mpz_to_int(lean_scalar_to_int(a1) / mpz_value(a2));
  } else if (lean_is_scalar(a2)) {
    int d = lean_scalar_to_int(a2);
    if (d == 0)
      return a2;
    else
      return mpz_to_int(mpz_value(a1) / d);
  } else {
    return mpz_to_int(mpz_value(a1) / mpz_value(a2));
  }
}

extern "C" LEAN_EXPORT object *lean_int_big_mod(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    return mpz_to_int(mpz(lean_scalar_to_int(a1)) % mpz_value(a2));
  } else if (lean_is_scalar(a2)) {
    int i2 = lean_scalar_to_int(a2);
    if (i2 == 0) {
      lean_inc(a1);
      return a1;
    } else {
      return mpz_to_int(mpz_value(a1) % mpz(i2));
    }
  } else {
    return mpz_to_int(mpz_value(a1) % mpz_value(a2));
  }
}

extern "C" LEAN_EXPORT object *lean_int_big_ediv(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    return mpz_to_int(mpz::ediv(lean_scalar_to_int(a1), mpz_value(a2)));
  } else if (lean_is_scalar(a2)) {
    int d = lean_scalar_to_int(a2);
    if (d == 0)
      return a2;
    else
      return mpz_to_int(mpz::ediv(mpz_value(a1), d));
  } else {
    return mpz_to_int(mpz::ediv(mpz_value(a1), mpz_value(a2)));
  }
}

extern "C" LEAN_EXPORT object *lean_int_big_emod(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    return mpz_to_int(mpz::emod(lean_scalar_to_int(a1), mpz_value(a2)));
  } else if (lean_is_scalar(a2)) {
    int i2 = lean_scalar_to_int(a2);
    if (i2 == 0) {
      lean_inc(a1);
      return a1;
    } else {
      return mpz_to_int(mpz::emod(mpz_value(a1), i2));
    }
  } else {
    return mpz_to_int(mpz::emod(mpz_value(a1), mpz_value(a2)));
  }
}

extern "C" LEAN_EXPORT bool lean_int_big_eq(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    lean_assert(lean_scalar_to_int(a1) != mpz_value(a2)) return false;
  } else if (lean_is_scalar(a2)) {
    lean_assert(mpz_value(a1) != lean_scalar_to_int(a2)) return false;
  } else {
    return mpz_value(a1) == mpz_value(a2);
  }
}

extern "C" LEAN_EXPORT bool lean_int_big_le(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    return lean_scalar_to_int(a1) <= mpz_value(a2);
  } else if (lean_is_scalar(a2)) {
    return mpz_value(a1) <= lean_scalar_to_int(a2);
  } else {
    return mpz_value(a1) <= mpz_value(a2);
  }
}

extern "C" LEAN_EXPORT bool lean_int_big_lt(object *a1, object *a2) {
  if (lean_is_scalar(a1)) {
    return lean_scalar_to_int(a1) < mpz_value(a2);
  } else if (lean_is_scalar(a2)) {
    return mpz_value(a1) < lean_scalar_to_int(a2);
  } else {
    return mpz_value(a1) < mpz_value(a2);
  }
}

extern "C" LEAN_EXPORT bool lean_int_big_nonneg(object *a) {
  return mpz_value(a) >= 0;
}

// =======================================
// UInt

extern "C" LEAN_EXPORT uint8 lean_uint8_of_big_nat(b_obj_arg a) {
  return static_cast<uint8>(mpz_value(a).mod8());
}

extern "C" LEAN_EXPORT uint16 lean_uint16_of_big_nat(b_obj_arg a) {
  return static_cast<uint16>(mpz_value(a).mod16());
}

extern "C" LEAN_EXPORT uint32 lean_uint32_of_big_nat(b_obj_arg a) {
  return mpz_value(a).mod32();
}

extern "C" LEAN_EXPORT uint32 lean_uint32_big_modn(uint32 a1,
                                                   b_lean_obj_arg a2) {
  mpz const &m = mpz_value(a2);
  return m.is_unsigned_int() ? a1 % m.get_unsigned_int() : a1;
}

extern "C" LEAN_EXPORT uint64 lean_uint64_of_big_nat(b_obj_arg a) {
  return mpz_value(a).mod64();
}

extern "C" LEAN_EXPORT uint64 lean_uint64_big_modn(uint64 a1, b_lean_obj_arg) {
  // TODO(Leo)
  return a1;
}

extern "C" LEAN_EXPORT uint64 lean_uint64_mix_hash(uint64 a1, uint64 a2) {
  return hash(a1, a2);
}

extern "C" LEAN_EXPORT usize lean_usize_of_big_nat(b_obj_arg a) {
  return mpz_value(a).get_size_t();
}

extern "C" LEAN_EXPORT usize lean_usize_big_modn(usize a1, b_lean_obj_arg) {
  // TODO(Leo)
  return a1;
}

// =======================================
// Float

extern "C" LEAN_EXPORT lean_obj_res lean_float_to_string(double a) {
  if (isnan(a))
    // override NaN because we don't want NaNs to be distinguishable
    // because the sign bit / payload bits can be architecture-dependent
    return mk_string("NaN");
  else
    return mk_string(std::to_string(a));
}

extern "C" LEAN_EXPORT double lean_float_scaleb(double a, b_lean_obj_arg b) {
  if (lean_is_scalar(b)) {
    return scalbn(a, lean_scalar_to_int(b));
  } else if (a == 0 || mpz_value(b).is_neg()) {
    return 0;
  } else {
    return a * (1.0 / 0.0);
  }
}

extern "C" LEAN_EXPORT uint8_t lean_float_isnan(double a) {
  return (bool)isnan(a);
}
extern "C" LEAN_EXPORT uint8_t lean_float_isfinite(double a) {
  return (bool)isfinite(a);
}
extern "C" LEAN_EXPORT uint8_t lean_float_isinf(double a) {
  return (bool)isinf(a);
}
extern "C" LEAN_EXPORT obj_res lean_float_frexp(double a) {
  object *r = lean_alloc_ctor(0, 2, 0);
  int exp;
  lean_ctor_set(r, 0, lean_box_float(frexp(a, &exp)));
  lean_ctor_set(r, 1, isfinite(a) ? lean_int_to_int(exp) : lean_box(0));
  return r;
}

// =======================================
// Strings

static inline char *w_string_cstr(object *o) {
  lean_assert(lean_is_string(o));
  return lean_to_string(o)->m_data;
}

static object *string_ensure_capacity(object *o, size_t extra) {
  lean_assert(is_exclusive(o));
  size_t sz = string_size(o);
  size_t cap = string_capacity(o);
  if (sz + extra > cap) {
    object *new_o = alloc_string(sz, cap + sz + extra, string_len(o));
    lean_assert(string_capacity(new_o) >= sz + extra);
    memcpy(w_string_cstr(new_o), string_cstr(o), sz);
    lean_dealloc(o, lean_string_byte_size(o));
    return new_o;
  } else {
    return o;
  }
}

extern "C" LEAN_EXPORT object *lean_mk_string_core(char const *s, size_t sz,
                                                   size_t len) {
  size_t rsz = sz + 1;
  object *r = lean_alloc_string(rsz, rsz, len);
  memcpy(w_string_cstr(r), s, sz);
  w_string_cstr(r)[sz] = 0;
  return r;
}

extern "C" LEAN_EXPORT object *lean_mk_string_from_bytes(char const *s,
                                                         size_t sz) {
  return lean_mk_string_core(s, sz, utf8_strlen(s, sz));
}

extern "C" LEAN_EXPORT object *lean_mk_string(char const *s) {
  return lean_mk_string_from_bytes(s, strlen(s));
}

extern "C" LEAN_EXPORT obj_res lean_string_from_utf8(b_obj_arg a) {
  return lean_mk_string_from_bytes(
      reinterpret_cast<char *>(lean_sarray_cptr(a)), lean_sarray_size(a));
}

extern "C" LEAN_EXPORT uint8 lean_string_validate_utf8(b_obj_arg a) {
  return validate_utf8(lean_sarray_cptr(a), lean_sarray_size(a));
}

extern "C" LEAN_EXPORT obj_res lean_string_to_utf8(b_obj_arg s) {
  size_t sz = lean_string_size(s) - 1;
  obj_res r = lean_alloc_sarray(1, sz, sz);
  memcpy(lean_sarray_cptr(r), lean_string_cstr(s), sz);
  return r;
}

object *mk_string(std::string const &s) {
  return lean_mk_string_from_bytes(s.data(), s.size());
}

object *mk_ascii_string(std::string const &s) {
  return lean_mk_string_core(s.data(), s.size(), s.size());
}

std::string string_to_std(b_obj_arg o) {
  lean_assert(string_size(o) > 0);
  return std::string(w_string_cstr(o), lean_string_size(o) - 1);
}

static size_t mk_capacity(size_t sz) { return sz * 2; }

extern "C" LEAN_EXPORT object *lean_string_push(object *s, unsigned c) {
  size_t sz = lean_string_size(s);
  size_t len = lean_string_len(s);
  object *r;
  if (!lean_is_exclusive(s)) {
    r = lean_alloc_string(sz, mk_capacity(sz + 5), len);
    memcpy(w_string_cstr(r), lean_string_cstr(s), sz - 1);
    lean_dec_ref(s);
  } else {
    r = string_ensure_capacity(s, 5);
  }
  unsigned consumed = push_unicode_scalar(w_string_cstr(r) + sz - 1, c);
  lean_to_string(r)->m_size = sz + consumed;
  lean_to_string(r)->m_length++;
  w_string_cstr(r)[sz + consumed - 1] = 0;
  return r;
}

extern "C" LEAN_EXPORT object *lean_string_append(object *s1, object *s2) {
  size_t sz1 = lean_string_size(s1);
  size_t sz2 = lean_string_size(s2);
  size_t len1 = lean_string_len(s1);
  size_t len2 = lean_string_len(s2);
  size_t new_len = len1 + len2;
  size_t new_sz = sz1 + sz2 - 1;
  object *r;
  if (!lean_is_exclusive(s1)) {
    r = lean_alloc_string(new_sz, mk_capacity(new_sz), new_len);
    memcpy(w_string_cstr(r), lean_string_cstr(s1), sz1 - 1);
    dec_ref(s1);
  } else {
    lean_assert(s1 != s2);
    r = string_ensure_capacity(s1, sz2 - 1);
  }
  memcpy(w_string_cstr(r) + sz1 - 1, lean_string_cstr(s2), sz2 - 1);
  lean_to_string(r)->m_size = new_sz;
  lean_to_string(r)->m_length = new_len;
  w_string_cstr(r)[new_sz - 1] = 0;
  return r;
}

extern "C" LEAN_EXPORT bool lean_string_eq_cold(b_lean_obj_arg s1,
                                                b_lean_obj_arg s2) {
  return std::memcmp(lean_string_cstr(s1), lean_string_cstr(s2),
                     lean_string_size(s1)) == 0;
}

bool string_eq(object *s1, char const *s2) {
  if (lean_string_size(s1) != strlen(s2) + 1)
    return false;
  return std::memcmp(lean_string_cstr(s1), s2, lean_string_size(s1)) == 0;
}

extern "C" LEAN_EXPORT bool lean_string_lt(object *s1, object *s2) {
  size_t sz1 = lean_string_size(s1) - 1; // ignore null char in the end
  size_t sz2 = lean_string_size(s2) - 1; // ignore null char in the end
  int r = std::memcmp(lean_string_cstr(s1), lean_string_cstr(s2),
                      std::min(sz1, sz2));
  return r < 0 || (r == 0 && sz1 < sz2);
}

static std::string list_as_string(b_obj_arg lst) {
  std::string s;
  b_obj_arg o = lst;
  while (!lean_is_scalar(o)) {
    push_unicode_scalar(s, lean_unbox_uint32(lean_ctor_get(o, 0)));
    o = lean_ctor_get(o, 1);
  }
  return s;
}

static obj_res string_to_list_core(std::string const &s, bool reverse = false) {
  std::vector<unsigned> tmp;
  utf8_decode(s, tmp);
  if (reverse)
    std::reverse(tmp.begin(), tmp.end());
  obj_res r = lean_box_uint32(0);
  unsigned i = tmp.size();
  while (i > 0) {
    --i;
    obj_res new_r = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(new_r, 0, lean_box_uint32(tmp[i]));
    lean_ctor_set(new_r, 1, r);
    r = new_r;
  }
  return r;
}

extern "C" LEAN_EXPORT obj_res lean_string_mk(obj_arg cs) {
  std::string s = list_as_string(cs);
  lean_dec(cs);
  return mk_string(s);
}

extern "C" LEAN_EXPORT obj_res lean_string_data(obj_arg s) {
  std::string tmp = string_to_std(s);
  lean_dec_ref(s);
  return string_to_list_core(tmp);
}

static bool lean_string_utf8_get_core(char const *str, usize size, usize i,
                                      uint32 &result) {
  unsigned c = static_cast<unsigned char>(str[i]);
  /* zero continuation (0 to 0x7F) */
  if ((c & 0x80) == 0) {
    result = c;
    return true;
  }

  /* one continuation (0x80 to 0x7FF) */
  if ((c & 0xe0) == 0xc0 && i + 1 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    result = ((c & 0x1f) << 6) | (c1 & 0x3f);
    if (result >= 0x80) {
      return true;
    }
  }

  /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
  if ((c & 0xf0) == 0xe0 && i + 2 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    result = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
    if (result >= 0x800 && (result < 0xD800 || result > 0xDFFF)) {
      return true;
    }
  }

  /* three continuations (0x10000 to 0x10FFFF) */
  if ((c & 0xf8) == 0xf0 && i + 3 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    unsigned c3 = static_cast<unsigned char>(str[i + 3]);
    result = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) |
             (c3 & 0x3f);
    if (result >= 0x10000 && result <= 0x10FFFF) {
      return true;
    }
  }

  /* invalid UTF-8 encoded string */
  return false;
}

extern "C" LEAN_EXPORT uint32 lean_string_utf8_get(b_obj_arg s, b_obj_arg i0) {
  if (!lean_is_scalar(i0)) {
    /* If `i0` is not a scalar, then it must be > LEAN_MAX_SMALL_NAT,
       and should not be a valid index.

       Recall that LEAN_MAX_SMALL_NAT is 2^31-1 in 32-bit machines and
       2^63 - 1 in 64-bit ones.

       `i0` would only be a valid index if `s` had more than
       `LEAN_MAX_SMALL_NAT` bytes which is unlikely.

       For example, Linux for 64-bit machines can address at most 256 Tb which
       is less than 2^63 - 1.
    */
    return lean_char_default_value();
  }
  usize i = lean_unbox(i0);
  char const *str = lean_string_cstr(s);
  usize size = lean_string_size(s) - 1;
  if (i >= lean_string_size(s) - 1)
    return lean_char_default_value();
  uint32 result;
  if (lean_string_utf8_get_core(str, size, i, result))
    return result;
  else
    return lean_char_default_value();
}

extern "C" LEAN_EXPORT uint32_t lean_string_utf8_get_fast_cold(
    char const *str, size_t i, size_t size, unsigned char c) {
  /* one continuation (0x80 to 0x7FF) */
  if ((c & 0xe0) == 0xc0 && i + 1 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    uint32_t result = ((c & 0x1f) << 6) | (c1 & 0x3f);
    if (result >= 0x80) {
      return result;
    }
  }

  /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
  if ((c & 0xf0) == 0xe0 && i + 2 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    uint32_t result = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
    if (result >= 0x800 && (result < 0xD800 || result > 0xDFFF)) {
      return result;
    }
  }

  /* three continuations (0x10000 to 0x10FFFF) */
  if ((c & 0xf8) == 0xf0 && i + 3 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    unsigned c3 = static_cast<unsigned char>(str[i + 3]);
    uint32_t result = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) |
                      ((c2 & 0x3f) << 6) | (c3 & 0x3f);
    if (result >= 0x10000 && result <= 0x10FFFF) {
      return result;
    }
  }
  /* invalid UTF-8 encoded string */
  return lean_char_default_value();
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_get_opt(b_obj_arg s,
                                                        b_obj_arg i0) {
  if (!lean_is_scalar(i0)) {
    return lean_box(0);
  }
  usize i = lean_unbox(i0);
  char const *str = lean_string_cstr(s);
  usize size = lean_string_size(s) - 1;
  if (i >= lean_string_size(s) - 1)
    return lean_box(0);
  uint32 result;
  if (lean_string_utf8_get_core(str, size, i, result)) {
    obj_res new_r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(new_r, 0, lean_box_uint32(result));
    return new_r;
  } else {
    return lean_box(0);
  }
}

static uint32 lean_string_utf8_get_panic() {
  lean_panic_fn(lean_box(0),
                lean_mk_string("Error: invalid `String.Pos` at `String.get!`"));
  return lean_char_default_value();
}

extern "C" LEAN_EXPORT uint32 lean_string_utf8_get_bang(b_obj_arg s,
                                                        b_obj_arg i0) {
  if (!lean_is_scalar(i0)) {
    return lean_string_utf8_get_panic();
  }
  usize i = lean_unbox(i0);
  char const *str = lean_string_cstr(s);
  usize size = lean_string_size(s) - 1;
  if (i >= lean_string_size(s) - 1)
    return lean_string_utf8_get_panic();
  uint32 result;
  if (lean_string_utf8_get_core(str, size, i, result))
    return result;
  else
    return lean_string_utf8_get_panic();
}

/* The reference implementation is:
   ```
   def next (s : @& String) (p : @& Pos) : Ppos :=
   let c := get s p in
   p + csize c
   ```
*/
extern "C" LEAN_EXPORT obj_res lean_string_utf8_next(b_obj_arg s,
                                                     b_obj_arg i0) {
  if (!lean_is_scalar(i0)) {
    /* See comment at string_utf8_get */
    return lean_nat_add(i0, lean_box(1));
  }
  usize i = lean_unbox(i0);
  char const *str = lean_string_cstr(s);
  usize size = lean_string_size(s) - 1;
  /* `csize c` is 1 when `i` is not a valid position in the reference
   * implementation. */
  if (i >= size)
    return lean_box(i + 1);
  unsigned c = static_cast<unsigned char>(str[i]);
  if ((c & 0x80) == 0)
    return lean_box(i + 1);
  if ((c & 0xe0) == 0xc0)
    return lean_box(i + 2);
  if ((c & 0xf0) == 0xe0)
    return lean_box(i + 3);
  if ((c & 0xf8) == 0xf0)
    return lean_box(i + 4);
  /* invalid UTF-8 encoded string */
  return lean_box(i + 1);
}

extern "C" LEAN_EXPORT obj_res
lean_string_utf8_next_fast_cold(size_t i, unsigned char c) {
  if ((c & 0xe0) == 0xc0)
    return lean_box(i + 2);
  if ((c & 0xf0) == 0xe0)
    return lean_box(i + 3);
  if ((c & 0xf8) == 0xf0)
    return lean_box(i + 4);
  /* invalid UTF-8 encoded string */
  return lean_box(i + 1);
}

static inline bool is_utf8_first_byte(unsigned char c) {
  return (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 ||
         (c & 0xf8) == 0xf0;
}

extern "C" LEAN_EXPORT uint8 lean_string_is_valid_pos(b_obj_arg s,
                                                      b_obj_arg i0) {
  if (!lean_is_scalar(i0)) {
    /* See comment at string_utf8_get */
    return false;
  }
  usize i = lean_unbox(i0);
  usize sz = lean_string_size(s) - 1;
  if (i > sz)
    return false;
  if (i == sz)
    return true;
  char const *str = lean_string_cstr(s);
  return is_utf8_first_byte(str[i]);
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_extract(b_obj_arg s,
                                                        b_obj_arg b0,
                                                        b_obj_arg e0) {
  if (!lean_is_scalar(b0) || !lean_is_scalar(e0)) {
    /* See comment at string_utf8_get */
    return s;
  }
  usize b = lean_unbox(b0);
  usize e = lean_unbox(e0);
  char const *str = lean_string_cstr(s);
  usize sz = lean_string_size(s) - 1;
  if (b >= e || b >= sz)
    return lean_mk_string("");
  /* In the reference implementation if `b` is not pointing to a valid UTF8
     character start position, the result is the empty string. */
  if (!is_utf8_first_byte(str[b]))
    return lean_mk_string("");
  if (e > sz)
    e = sz;
  lean_assert(b < e);
  lean_assert(e > 0);
  /* In the reference implementation if `e` is not pointing to a valid UTF8
     character start position, it is assumed to be at the end. */
  if (e < sz && !is_utf8_first_byte(str[e]))
    e = sz;
  usize new_sz = e - b;
  lean_assert(new_sz > 0);
  return lean_mk_string_from_bytes(lean_string_cstr(s) + b, new_sz);
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_prev(b_obj_arg s,
                                                     b_obj_arg i0) {
  if (!lean_is_scalar(i0)) {
    /* See comment at string_utf8_get */
    return lean_nat_sub(i0, lean_box(1));
  }
  usize i = lean_unbox(i0);
  usize sz = lean_string_size(s) - 1;
  if (i == 0 || i > sz)
    return lean_box(0);
  i--;
  char const *str = lean_string_cstr(s);
  while (!is_utf8_first_byte(str[i])) {
    lean_assert(i > 0);
    i--;
  }
  return lean_box(i);
}

/*
Table 3-6. UTF-8 Bit Distribution
Scalar Value               | First Byte | Second Byte | Third Byte | Fourth Byte
00000000 0xxxxxxx          | 0xxxxxxx   |             |            |
00000yyy yyxxxxxx          | 110yyyyy   | 10xxxxxx    |            |
zzzzyyyy yyxxxxxx          | 1110zzzz   | 10yyyyyy    | 10xxxxxx   |
000uuuuu zzzzyyyy yyxxxxxx | 11110uuu   | 10uuzzzz    | 10yyyyyy   | 10xxxxxx
*/
static unsigned get_utf8_char_size_at(std::string const &s, usize i) {
  unsigned char c = s[i];
  if ((c & 0x80) == 0) {
    /* 0xxxxxxx */
    return 1;
  } else if ((c & 0xe0) == 0xc0) {
    /* 110yyyyy */
    return 2;
  } else if ((c & 0xf0) == 0xe0) {
    /* 1110zzzz */
    return 3;
  } else if ((c & 0xf8) == 0xf0) {
    /* 11110uuu */
    return 4;
  } else {
    return 1;
  }
}

extern "C" LEAN_EXPORT obj_res lean_string_utf8_set(obj_arg s, b_obj_arg i0,
                                                    uint32 c) {
  if (!lean_is_scalar(i0)) {
    /* See comment at string_utf8_get */
    return s;
  }
  usize i = lean_unbox(i0);
  usize sz = lean_string_size(s) - 1;
  if (i >= sz)
    return s;
  char *str = w_string_cstr(s);
  if (lean_is_exclusive(s)) {
    if (static_cast<unsigned char>(str[i]) < 128 && c < 128) {
      str[i] = c;
      return s;
    }
  }
  if (!is_utf8_first_byte(str[i]))
    return s;
  /* TODO(Leo): improve performance of other special cases.
     Example: is_exclusive(s) and new and old characters have the same size;
     etc. */
  std::string tmp;
  push_unicode_scalar(tmp, c);
  std::string new_s = string_to_std(s);
  dec(s);
  new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp);
  return mk_string(new_s);
}

extern "C" LEAN_EXPORT uint64 lean_string_hash(b_obj_arg s) {
  usize sz = lean_string_size(s) - 1;
  char const *str = lean_string_cstr(s);
  return hash_str(sz, (unsigned char const *)str, 11);
}

extern "C" LEAN_EXPORT obj_res lean_string_of_usize(size_t n) {
  return mk_ascii_string(std::to_string(n));
}

// =======================================
// ByteArray & FloatArray

size_t lean_nat_to_size_t(obj_arg n) {
  if (lean_is_scalar(n)) {
    return lean_unbox(n);
  } else {
    mpz const &v = mpz_value(n);
    if (!v.is_size_t())
      lean_internal_panic_out_of_memory();
    size_t sz = v.get_size_t();
    lean_dec(n);
    return sz;
  }
}

extern "C" LEAN_EXPORT obj_res lean_copy_sarray(obj_arg a, size_t cap) {
  unsigned esz = lean_sarray_elem_size(a);
  size_t sz = lean_sarray_size(a);
  lean_assert(cap >= sz);
  object *r = lean_alloc_sarray(esz, sz, cap);
  uint8 *it = lean_sarray_cptr(a);
  uint8 *dest = lean_sarray_cptr(r);
  memcpy(dest, it, esz * sz);
  lean_dec(a);
  return r;
}

obj_res lean_sarray_ensure_exclusive(obj_arg a) {
  if (lean_is_exclusive(a)) {
    return a;
  } else {
    return lean_copy_sarray(a, lean_sarray_capacity(a));
  }
}

/* Ensure that `a` has capacity at least `min_cap`, copying `a` otherwise.
   If `exact` is false, double the capacity on copying. */
extern "C" LEAN_EXPORT obj_res lean_sarray_ensure_capacity(obj_arg a,
                                                           size_t min_cap,
                                                           bool exact) {
  size_t cap = lean_sarray_capacity(a);
  if (min_cap <= cap) {
    return a;
  } else {
    return lean_copy_sarray(a, exact ? min_cap : min_cap * 2);
  }
}

extern "C" LEAN_EXPORT obj_res lean_copy_byte_array(obj_arg a) {
  return lean_copy_sarray(a, lean_sarray_capacity(a));
}

extern "C" LEAN_EXPORT obj_res lean_byte_array_mk(obj_arg a) {
  usize sz = lean_array_size(a);
  obj_res r = lean_alloc_sarray(1, sz, sz);
  object **it = lean_array_cptr(a);
  object **end = it + sz;
  uint8 *dest = lean_sarray_cptr(r);
  for (; it != end; ++it, ++dest) {
    *dest = lean_unbox(*it);
  }
  lean_dec(a);
  return r;
}

extern "C" LEAN_EXPORT obj_res lean_byte_array_data(obj_arg a) {
  usize sz = lean_sarray_size(a);
  obj_res r = lean_alloc_array(sz, sz);
  uint8 *it = lean_sarray_cptr(a);
  uint8 *end = it + sz;
  object **dest = lean_array_cptr(r);
  for (; it != end; ++it, ++dest) {
    *dest = lean_box(*it);
  }
  lean_dec(a);
  return r;
}

extern "C" LEAN_EXPORT obj_res lean_byte_array_push(obj_arg a, uint8 b) {
  object *r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(
      a, lean_sarray_size(a) + 1, /* exact */ false));
  size_t &sz = lean_to_sarray(r)->m_size;
  uint8 *it = lean_sarray_cptr(r) + sz;
  *it = b;
  sz++;
  return r;
}

extern "C" LEAN_EXPORT obj_res
lean_byte_array_copy_slice(b_obj_arg src, obj_arg o_src_off, obj_arg dest,
                           obj_arg o_dest_off, obj_arg o_len, bool exact) {
  size_t ssz = lean_sarray_size(src);
  size_t dsz = lean_sarray_size(dest);
  size_t src_off = lean_nat_to_size_t(o_src_off);
  if (src_off > ssz) {
    return dest;
  }
  size_t len = std::min(lean_nat_to_size_t(o_len), ssz - src_off);
  size_t dest_off = lean_nat_to_size_t(o_dest_off);
  if (dest_off > dsz) {
    dest_off = dsz;
  }
  size_t new_dsz = std::max(dsz, dest_off + len);
  object *r = lean_sarray_ensure_exclusive(
      lean_sarray_ensure_capacity(dest, new_dsz, exact));
  lean_to_sarray(r)->m_size = new_dsz;
  // `r` is exclusive, so the ranges definitely cannot overlap
  memcpy(lean_sarray_cptr(r) + dest_off, lean_sarray_cptr(src) + src_off, len);
  return r;
}

extern "C" LEAN_EXPORT uint64_t lean_byte_array_hash(b_obj_arg a) {
  return hash_str(lean_sarray_size(a), lean_sarray_cptr(a), 11);
}

extern "C" LEAN_EXPORT obj_res lean_copy_float_array(obj_arg a) {
  return lean_copy_sarray(a, lean_sarray_capacity(a));
}

extern "C" LEAN_EXPORT obj_res lean_float_array_mk(obj_arg a) {
  usize sz = lean_array_size(a);
  obj_res r = lean_alloc_sarray(sizeof(double), sz, sz); // NOLINT
  object **it = lean_array_cptr(a);
  object **end = it + sz;
  double *dest = reinterpret_cast<double *>(lean_sarray_cptr(r));
  for (; it != end; ++it, ++dest) {
    *dest = lean_unbox_float(*it);
  }
  lean_dec(a);
  return r;
}

extern "C" LEAN_EXPORT obj_res lean_float_array_data(obj_arg a) {
  usize sz = lean_sarray_size(a);
  obj_res r = lean_alloc_array(sz, sz);
  double *it = reinterpret_cast<double *>(lean_sarray_cptr(a));
  double *end = it + sz;
  object **dest = lean_array_cptr(r);
  for (; it != end; ++it, ++dest) {
    *dest = lean_box_float(*it);
  }
  lean_dec(a);
  return r;
}

extern "C" LEAN_EXPORT obj_res lean_float_array_push(obj_arg a, double d) {
  object *r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(
      a, lean_sarray_size(a) + 1, /* exact */ false));
  size_t &sz = lean_to_sarray(r)->m_size;
  double *it = reinterpret_cast<double *>(lean_sarray_cptr(r)) + sz;
  *it = d;
  sz++;
  return r;
}

// =======================================
// Array functions for generated code

extern "C" LEAN_EXPORT object *lean_mk_array(obj_arg n, obj_arg v) {
  size_t sz;
  if (lean_is_scalar(n)) {
    sz = lean_unbox(n);
  } else {
    mpz const &v = mpz_value(n);
    if (!v.is_size_t())
      lean_internal_panic_out_of_memory();
    sz = v.get_size_t();
    lean_dec(n);
  }
  object *r = lean_alloc_array(sz, sz);
  object **it = lean_array_cptr(r);
  object **end = it + sz;
  for (; it != end; ++it) {
    *it = v;
  }
  if (sz == 0) {
    lean_dec(v);
  } else if (sz > 1) {
    lean_inc_n(v, sz - 1);
  }
  return r;
}

extern "C" LEAN_EXPORT obj_res lean_copy_expand_array(obj_arg a, bool expand) {
  size_t sz = lean_array_size(a);
  size_t cap = lean_array_capacity(a);
  lean_assert(cap >= sz);
  if (expand)
    cap = (cap + 1) * 2;
  lean_assert(!expand || cap > sz);
  object *r = lean_alloc_array(sz, cap);
  object **it = lean_array_cptr(a);
  object **end = it + sz;
  object **dest = lean_array_cptr(r);
  if (lean_is_exclusive(a)) {
    // transfer ownership of elements directly instead of inc+dec
    memcpy(dest, it, sz * sizeof(object *));
    lean_dealloc(a, lean_array_byte_size(a));
  } else {
    for (; it != end; ++it, ++dest) {
      *dest = *it;
      lean_inc(*it);
    }
    lean_dec(a);
  }
  return r;
}

extern "C" LEAN_EXPORT object *lean_array_push(obj_arg a, obj_arg v) {
  object *r;
  if (lean_is_exclusive(a)) {
    if (lean_array_capacity(a) > lean_array_size(a))
      r = a;
    else
      r = lean_copy_expand_array(a, true);
  } else {
    r = lean_copy_expand_array(a, lean_array_capacity(a) <
                                      2 * lean_array_size(a) + 1);
  }
  lean_assert(lean_array_capacity(r) > lean_array_size(r));
  size_t &sz = lean_to_array(r)->m_size;
  object **it = lean_array_cptr(r) + sz;
  *it = v;
  sz++;
  return r;
}

// =======================================
// Name primitives

extern "C" LEAN_EXPORT uint8 lean_name_eq(b_lean_obj_arg n1,
                                          b_lean_obj_arg n2) {
  if (n1 == n2)
    return true;
  if (lean_is_scalar(n1) != lean_is_scalar(n2) ||
      lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2))
    return false;
  while (true) {
    lean_assert(!lean_is_scalar(n1));
    lean_assert(!lean_is_scalar(n2));
    lean_assert(n1 && n2);
    if (lean_ptr_tag(n1) != lean_ptr_tag(n2))
      return false;
    if (lean_ptr_tag(n1) == 1) {
      if (!lean_string_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)))
        return false;
    } else {
      if (!lean_nat_eq(lean_ctor_get(n1, 1), lean_ctor_get(n1, 1)))
        return false;
    }
    n1 = lean_ctor_get(n1, 0);
    n2 = lean_ctor_get(n2, 0);
    if (n1 == n2)
      return true;
    if (lean_is_scalar(n1) != lean_is_scalar(n2))
      return false;
    /*
    // The `return false` in the following `if` is seldom reached.
    if (lean_name_hash_ptr(n1) != lean_name_hash_ptr(n2))
        return false;
    */
  }
}

// =======================================
// Runtime info

extern "C" LEAN_EXPORT object *lean_closure_max_args(object *) {
  return lean_unsigned_to_nat((unsigned)LEAN_CLOSURE_MAX_ARGS);
}

extern "C" LEAN_EXPORT object *lean_max_small_nat(object *) {
  return lean_usize_to_nat(LEAN_MAX_SMALL_NAT);
}

// =======================================
// Debugging helper functions

extern "C" obj_res lean_io_eprintln(obj_arg s, obj_arg w);
void io_eprintln(obj_arg s) {
  object *r = lean_io_eprintln(s, lean_io_mk_world());
  lean_assert(lean_io_result_is_ok(r));
  lean_dec(r);
}

extern "C" LEAN_EXPORT object *lean_dbg_trace(obj_arg s, obj_arg fn) {
  io_eprintln(s);
  return lean_apply_1(fn, lean_box(0));
}

extern "C" LEAN_EXPORT object *lean_dbg_trace_if_shared(obj_arg s, obj_arg a) {
  if (!lean_is_scalar(a) && lean_is_shared(a)) {
    io_eprintln(mk_string(std::string("shared RC ") + lean_string_cstr(s)));
  }
  return a;
}
} // namespace lean
