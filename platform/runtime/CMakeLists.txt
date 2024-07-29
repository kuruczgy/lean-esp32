set(RUNTIME_OBJS mpz.cpp utf8.cpp object.cpp apply.cpp init_module.cpp io.cpp hash.cpp mpn.cpp)

# The above library, like all other C++ code, is built using `-ftls-model=initial-exec`, which is necessary for linking it into `leanshared`,
# but introduces a measurable overhead while accessing the thread-local variable `g_heap` when allocating and deallocating. Therefore we compile
# the runtime again with the more restrictive `local-exec` and use it when linking Lean code statically, i.e. not against `leanshared`.
add_library(leanrt STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY})
target_compile_options(leanrt PRIVATE -ftls-model=local-exec)