#include <lean/lean.h>

extern "C" int mymain();

extern "C" lean_obj_res run_mceliece(int32_t a, int32_t b) {
    int r = mymain();
    return lean_io_result_mk_ok(lean_box(0));
}