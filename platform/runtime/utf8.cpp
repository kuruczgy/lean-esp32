/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/utf8.h"
#include <cstdlib>
#include <string>

namespace lean {

static unsigned get_utf8_size(unsigned char c) {
  if ((c & 0x80) == 0)
    return 1;
  else if ((c & 0xE0) == 0xC0)
    return 2;
  else if ((c & 0xF0) == 0xE0)
    return 3;
  else if ((c & 0xF8) == 0xF0)
    return 4;
  else if ((c & 0xFC) == 0xF8)
    return 5;
  else if ((c & 0xFE) == 0xFC)
    return 6;
  else if (c == 0xFF)
    return 1;
  else
    return 1; /* invalid */
}

extern "C" LEAN_EXPORT size_t lean_utf8_strlen(char const *str) {
  size_t r = 0;
  while (*str != 0) {
    unsigned sz = get_utf8_size(*str);
    r++;
    str += sz;
  }
  return r;
}

size_t utf8_strlen(char const *str) { return lean_utf8_strlen(str); }

extern "C" LEAN_EXPORT size_t lean_utf8_n_strlen(char const *str, size_t sz) {
  size_t r = 0;
  size_t i = 0;
  while (i < sz) {
    unsigned d = get_utf8_size(str[i]);
    r++;
    i += d;
  }
  return r;
}

size_t utf8_strlen(char const *str, size_t sz) {
  return lean_utf8_n_strlen(str, sz);
}

size_t utf8_strlen(std::string const &str) {
  return utf8_strlen(str.data(), str.size());
}

static unsigned next_utf8(char const *str, size_t size, size_t &i) {
  unsigned c = static_cast<unsigned char>(str[i]);
  /* zero continuation (0 to 0x7F) */
  if ((c & 0x80) == 0) {
    i++;
    return c;
  }

  /* one continuation (0x80 to 0x7FF) */
  if ((c & 0xe0) == 0xc0 && i + 1 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned r = ((c & 0x1f) << 6) | (c1 & 0x3f);
    if (r >= 0x80) {
      i += 2;
      return r;
    }
  }

  /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
  if ((c & 0xf0) == 0xe0 && i + 2 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    unsigned r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
    if (r >= 0x800 && (r < 0xD800 || r > 0xDFFF)) {
      i += 3;
      return r;
    }
  }

  /* three continuations (0x10000 to 0x10FFFF) */
  if ((c & 0xf8) == 0xf0 && i + 3 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    unsigned c3 = static_cast<unsigned char>(str[i + 3]);
    unsigned r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) |
                 (c3 & 0x3f);
    if (r >= 0x10000 && r <= 0x10FFFF) {
      i += 4;
      return r;
    }
  }

  /* invalid UTF-8 encoded string */
  i++;
  return c;
}

static unsigned next_utf8(std::string const &str, size_t &i) {
  return next_utf8(str.data(), str.size(), i);
}

void utf8_decode(std::string const &str, std::vector<unsigned> &out) {
  size_t i = 0;
  while (i < str.size()) {
    out.push_back(next_utf8(str, i));
  }
}

bool validate_utf8(uint8_t const *str, size_t size) {
  size_t i = 0;
  while (i < size) {
    unsigned c = str[i];
    if ((c & 0x80) == 0) {
      /* zero continuation (0 to 0x7F) */
      i++;
    } else if ((c & 0xe0) == 0xc0) {
      /* one continuation (0x80 to 0x7FF) */
      if (i + 1 >= size)
        return false;

      unsigned c1 = str[i + 1];
      if ((c1 & 0xc0) != 0x80)
        return false;

      unsigned r = ((c & 0x1f) << 6) | (c1 & 0x3f);
      if (r < 0x80)
        return false;

      i += 2;
    } else if ((c & 0xf0) == 0xe0) {
      /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
      if (i + 2 >= size)
        return false;

      unsigned c1 = str[i + 1];
      unsigned c2 = str[i + 2];
      if ((c1 & 0xc0) != 0x80 || (c2 & 0xc0) != 0x80)
        return false;

      unsigned r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
      if (r < 0x800 || (r >= 0xD800 && r <= 0xDFFF))
        return false;

      i += 3;
    } else if ((c & 0xf8) == 0xf0) {
      /* three continuations (0x10000 to 0x10FFFF) */
      if (i + 3 >= size)
        return false;

      unsigned c1 = str[i + 1];
      unsigned c2 = str[i + 2];
      unsigned c3 = str[i + 3];
      if ((c1 & 0xc0) != 0x80 || (c2 & 0xc0) != 0x80 || (c3 & 0xc0) != 0x80)
        return false;

      unsigned r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) |
                   ((c2 & 0x3f) << 6) | (c3 & 0x3f);
      if (r < 0x10000 || r > 0x10FFFF)
        return false;

      i += 4;
    } else {
      return false;
    }
  }
  return true;
}

#define TAG_CONT static_cast<unsigned char>(0b10000000)
#define TAG_TWO_B static_cast<unsigned char>(0b11000000)
#define TAG_THREE_B static_cast<unsigned char>(0b11100000)
#define TAG_FOUR_B static_cast<unsigned char>(0b11110000)
#define MAX_ONE_B 0x80
#define MAX_TWO_B 0x800
#define MAX_THREE_B 0x10000

template <typename T> class push_back_trait {};

template <> class push_back_trait<char *> {
public:
  static void push(char *&s, unsigned char c) {
    *s = c;
    ++s;
  }
};

template <> class push_back_trait<std::string> {
public:
  static void push(std::string &s, unsigned char c) { s.push_back(c); }
};

template <typename T> unsigned push_unicode_scalar_core(T &d, unsigned code) {
  if (code < MAX_ONE_B) {
    push_back_trait<T>::push(d, static_cast<unsigned char>(code));
    return 1;
  } else if (code < MAX_TWO_B) {
    push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 6 & 0x1F) |
                                    TAG_TWO_B);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) |
                                    TAG_CONT);
    return 2;
  } else if (code < MAX_THREE_B) {
    push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 12 & 0x0F) |
                                    TAG_THREE_B);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 6 & 0x3F) |
                                    TAG_CONT);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) |
                                    TAG_CONT);
    return 3;
  } else {
    push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 18 & 0x07) |
                                    TAG_FOUR_B);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 12 & 0x3F) |
                                    TAG_CONT);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 6 & 0x3F) |
                                    TAG_CONT);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) |
                                    TAG_CONT);
    return 4;
  }
}

unsigned push_unicode_scalar(char *d, unsigned code) {
  return push_unicode_scalar_core<char *>(d, code);
}

void push_unicode_scalar(std::string &s, unsigned code) {
  push_unicode_scalar_core(s, code);
}
} // namespace lean
