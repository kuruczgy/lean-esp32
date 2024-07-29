/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lean/lean.h>

#define lean_unreachable()                                                     \
  { abort(); }

#define lean_assert(COND)                                                      \
  {                                                                            \
    if (LEAN_UNLIKELY(!(COND)))                                                \
      abort();                                                                 \
  }