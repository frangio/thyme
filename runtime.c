#include <lean/lean.h>

LEAN_EXPORT LEAN_NORETURN lean_object *
tmeta_panic_thunk(lean_object *message, lean_object *unit) {
    (void)unit;
    lean_internal_panic(lean_string_cstr(message));
}
