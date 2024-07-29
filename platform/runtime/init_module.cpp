/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/io.h"

namespace lean {
extern "C" LEAN_EXPORT void lean_initialize_runtime_module() {
  initialize_io();
}
} // namespace lean
