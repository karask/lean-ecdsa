/*
 * Valgrind client requests for the constant-time check.
 *
 * Marking secret bytes as "undefined" makes memcheck report every conditional
 * branch and every memory address that depends on them ("Conditional jump or
 * move depends on uninitialised value(s)" / "Use of uninitialised value").
 * Outputs that are public by design are marked "defined" again before they
 * are inspected. This is the technique of libsecp256k1's ctime_tests.
 *
 * Outside valgrind these requests are no-ops.
 */
#include <lean/lean.h>
#include <valgrind/memcheck.h>

LEAN_EXPORT lean_obj_res ctgrind_classify(b_lean_obj_arg bytes) {
    VALGRIND_MAKE_MEM_UNDEFINED(lean_sarray_cptr(bytes), lean_sarray_size(bytes));
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res ctgrind_declassify(b_lean_obj_arg bytes) {
    VALGRIND_MAKE_MEM_DEFINED(lean_sarray_cptr(bytes), lean_sarray_size(bytes));
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT uint8_t ctgrind_running_on_valgrind(lean_obj_arg unit) {
    return RUNNING_ON_VALGRIND ? 1 : 0;
}
