/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "lean/lean.h"
#include <string>
#include <vector>

namespace lean {
using uchar = unsigned char;

/* Return the length of the null terminated string encoded using UTF8 */
LEAN_EXPORT size_t utf8_strlen(char const *str);
/* Return the length of the string `str` encoded using UTF8.
   `str` may contain null characters. */
LEAN_EXPORT size_t utf8_strlen(std::string const &str);
/* Return the length of the string `str` encoded using UTF8.
   `str` may contain null characters. */
LEAN_EXPORT size_t utf8_strlen(char const *str, size_t sz);

/* Decode a UTF-8 encoded string `str` into unicode scalar values */
LEAN_EXPORT void utf8_decode(std::string const &str,
                             std::vector<unsigned> &out);

/* Returns true if the given character is valid UTF-8 */
LEAN_EXPORT bool validate_utf8_one(uint8_t const *str, size_t size,
                                   size_t &pos);

/* Returns true if the provided string is valid UTF-8 */
LEAN_EXPORT bool validate_utf8(uint8_t const *str, size_t size, size_t &pos,
                               size_t &i);

/* Push a unicode scalar value into a utf-8 encoded string */
LEAN_EXPORT void push_unicode_scalar(std::string &s, unsigned code);

/* Store unicode scalar value at `d`, `d` must point to memory with enough space
   to store `c`. Return the number of bytes consumed. */
LEAN_EXPORT unsigned push_unicode_scalar(char *d, unsigned code);
} // namespace lean
