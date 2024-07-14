/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
// Linux include files
#include "runtime/io.h"
#include "runtime/object.h"
#include <cctype>
#include <csignal>
#include <cstdlib>
#include <fcntl.h>
#include <string>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

namespace lean {

extern "C" object *lean_io_error_to_string(object *err);

extern "C" LEAN_EXPORT void lean_io_result_show_error(b_obj_arg r) {
  fprintf(stderr, "uncaught exception: (omitted)\n");
}

obj_res io_result_mk_error(char const *msg) {
  return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

obj_res io_result_mk_error(std::string const &msg) {
  return io_result_mk_error(lean_mk_io_user_error(mk_string(msg)));
}

static bool g_initializing = true;
extern "C" LEAN_EXPORT void lean_io_mark_end_initialization() {
  g_initializing = false;
}
extern "C" LEAN_EXPORT obj_res lean_io_initializing(obj_arg) {
  return io_result_mk_ok(box(g_initializing));
}

extern "C" obj_res lean_stream_of_handle(obj_arg h);

static object *g_stream_stdin = nullptr;
static object *g_stream_stdout = nullptr;
static object *g_stream_stderr = nullptr;

/* getStdin : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stdin(obj_arg /* w */) {
  return io_result_mk_ok(g_stream_stdin);
}

/* getStdout : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stdout(obj_arg /* w */) {
  return io_result_mk_ok(g_stream_stdout);
}

/* getStderr : BaseIO FS.Stream */
extern "C" LEAN_EXPORT obj_res lean_get_stderr(obj_arg /* w */) {
  return io_result_mk_ok(g_stream_stderr);
}

static FILE *io_get_handle(lean_object *hfile) { return (FILE *)hfile; }

extern "C" LEAN_EXPORT obj_res lean_decode_io_error(int errnum,
                                                    b_obj_arg fname) {
  abort();
}

/* Handle.isTty : (@& Handle) → BaseIO Bool */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_is_tty(b_obj_arg h,
                                                          obj_arg /* w */) {
  return io_result_mk_ok(box(false));
}

/* Handle.isEof : (@& Handle) → BaseIO Bool */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_is_eof(b_obj_arg h,
                                                          obj_arg /* w */) {
  FILE *fp = io_get_handle(h);
  return io_result_mk_ok(box(std::feof(fp) != 0));
}

/* Handle.flush : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_flush(b_obj_arg h,
                                                         obj_arg /* w */) {
  FILE *fp = io_get_handle(h);
  if (!std::fflush(fp)) {
    return io_result_mk_ok(box(0));
  } else {
    return io_result_mk_error(decode_io_error(errno, nullptr));
  }
}

/* Handle.rewind : (@& Handle) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_rewind(b_obj_arg h,
                                                          obj_arg /* w */) {
  FILE *fp = io_get_handle(h);
  if (!std::fseek(fp, 0, SEEK_SET)) {
    return io_result_mk_ok(box(0));
  } else {
    return io_result_mk_error(decode_io_error(errno, nullptr));
  }
}

/* Handle.read : (@& Handle) → USize → IO ByteArray */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_read(b_obj_arg h,
                                                        usize nbytes,
                                                        obj_arg /* w */) {
  FILE *fp = io_get_handle(h);
  obj_res res = lean_alloc_sarray(1, 0, nbytes);
  usize n = std::fread(lean_sarray_cptr(res), 1, nbytes, fp);
  if (n > 0) {
    lean_sarray_set_size(res, n);
    return io_result_mk_ok(res);
  } else if (feof(fp)) {
    clearerr(fp);
    lean_sarray_set_size(res, n);
    return io_result_mk_ok(res);
  } else {
    dec_ref(res);
    return io_result_mk_error(decode_io_error(errno, nullptr));
  }
}

/* Handle.write : (@& Handle) → (@& ByteArray) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_write(b_obj_arg h,
                                                         b_obj_arg buf,
                                                         obj_arg /* w */) {
  FILE *fp = io_get_handle(h);
  usize n = lean_sarray_size(buf);
  usize m = std::fwrite(lean_sarray_cptr(buf), 1, n, fp);
  if (m == n) {
    return io_result_mk_ok(box(0));
  } else {
    return io_result_mk_error(decode_io_error(errno, nullptr));
  }
}

/*
  Handle.getLine : (@& Handle) → IO Unit
  The line returned by `lean_io_prim_handle_get_line`
  is truncated at the first '\0' character and the
  rest of the line is discarded. */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_get_line(b_obj_arg h,
                                                            obj_arg /* w */) {
  FILE *fp = io_get_handle(h);
  const int buf_sz = 64;
  char buf_str[buf_sz]; // NOLINT
  std::string result;
  bool first = true;
  while (true) {
    char *out = std::fgets(buf_str, buf_sz, fp);
    if (out != nullptr) {
      if (strlen(buf_str) < buf_sz - 1 || buf_str[buf_sz - 2] == '\n') {
        if (first) {
          return io_result_mk_ok(mk_string(out));
        } else {
          result.append(out);
          return io_result_mk_ok(mk_string(result));
        }
      }
      result.append(out);
    } else if (std::feof(fp)) {
      clearerr(fp);
      return io_result_mk_ok(mk_string(result));
    } else {
      return io_result_mk_error(decode_io_error(errno, nullptr));
    }
    first = false;
  }
}

/* Handle.putStr : (@& Handle) → (@& String) → IO Unit */
extern "C" LEAN_EXPORT obj_res lean_io_prim_handle_put_str(b_obj_arg h,
                                                           b_obj_arg s,
                                                           obj_arg /* w */) {
  FILE *fp = io_get_handle(h);
  if (std::fputs(lean_string_cstr(s), fp) != EOF) {
    return io_result_mk_ok(box(0));
  } else {
    return io_result_mk_error(decode_io_error(errno, nullptr));
  }
}

/* monoMsNow : BaseIO Nat */
extern "C" LEAN_EXPORT obj_res lean_io_mono_ms_now(obj_arg /* w */) {
  // TODO
  abort();
}

/* monoNanosNow : BaseIO Nat */
extern "C" LEAN_EXPORT obj_res lean_io_mono_nanos_now(obj_arg /* w */) {
  // TODO
  abort();
}

/* getRandomBytes (nBytes : USize) : IO ByteArray */
extern "C" LEAN_EXPORT obj_res lean_io_get_random_bytes(size_t nbytes,
                                                        obj_arg /* w */) {
  // TODO
  abort();
}

// =======================================
// ST ref primitives
extern "C" LEAN_EXPORT obj_res lean_st_mk_ref(obj_arg a, obj_arg) {
  lean_ref_object *o =
      (lean_ref_object *)lean_alloc_small_object(sizeof(lean_ref_object));
  lean_set_st_header((lean_object *)o, LeanRef, 0);
  o->m_value = a;
  return io_result_mk_ok((lean_object *)o);
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_get(b_obj_arg ref, obj_arg) {
  object *val = lean_to_ref(ref)->m_value;
  lean_assert(val != nullptr);
  inc(val);
  return io_result_mk_ok(val);
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_take(b_obj_arg ref, obj_arg) {
  object *val = lean_to_ref(ref)->m_value;
  lean_assert(val != nullptr);
  lean_to_ref(ref)->m_value = nullptr;
  return io_result_mk_ok(val);
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_set(b_obj_arg ref, obj_arg a,
                                               obj_arg) {
  if (lean_to_ref(ref)->m_value != nullptr)
    dec(lean_to_ref(ref)->m_value);
  lean_to_ref(ref)->m_value = a;
  return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_swap(b_obj_arg ref, obj_arg a,
                                                obj_arg) {
  object *old_a = lean_to_ref(ref)->m_value;
  if (old_a == nullptr)
    return io_result_mk_error(
        lean_mk_io_user_error(mk_string("null reference read")));
  lean_to_ref(ref)->m_value = a;
  return io_result_mk_ok(old_a);
}

extern "C" LEAN_EXPORT obj_res lean_st_ref_ptr_eq(b_obj_arg ref1,
                                                  b_obj_arg ref2, obj_arg) {
  bool r = lean_to_ref(ref1)->m_value == lean_to_ref(ref2)->m_value;
  return io_result_mk_ok(box(r));
}

extern "C" LEAN_EXPORT obj_res lean_io_exit(uint8_t code, obj_arg /* w */) {
  exit(code);
}

void initialize_io() {
  g_stream_stdout = lean_stream_of_handle((obj_arg)stdout);
  mark_persistent(g_stream_stdout);
  g_stream_stderr = lean_stream_of_handle((obj_arg)stderr);
  mark_persistent(g_stream_stderr);
  g_stream_stdin = lean_stream_of_handle((obj_arg)stdin);
  mark_persistent(g_stream_stdin);
}
} // namespace lean
