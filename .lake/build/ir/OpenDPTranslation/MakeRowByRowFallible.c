// Lean compiler output
// Module: OpenDPTranslation.MakeRowByRowFallible
// Imports: public import Init public import OpenDPTranslation.OpenDPCore
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_OpenDPTranslation_new__stability__map__from__constant___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_new__stability__map__from__constant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_new__stability__map__from__constant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_new__stability__map__from__constant___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_2, x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_new__stability__map__from__constant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_OpenDPTranslation_new__stability__map__from__constant___redArg(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_new__stability__map__from__constant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_OpenDPTranslation_new__stability__map__from__constant(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_alloc_closure((void*)(lp_OpenDPTranslation_make__row__by__row__fallible___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
lean_inc(x_6);
x_13 = lean_apply_2(x_10, x_6, x_8);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(lp_OpenDPTranslation_new__stability__map__from__constant___boxed), 8, 7);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_3);
lean_closure_set(x_14, 5, x_4);
lean_closure_set(x_14, 6, x_5);
lean_inc(x_7);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_7);
lean_ctor_set(x_15, 4, x_7);
lean_ctor_set(x_15, 5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = lp_OpenDPTranslation_make__row__by__row__fallible___redArg(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row__fallible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = lp_OpenDPTranslation_make__row__by__row__fallible(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_17;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_OpenDPCore(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OpenDPTranslation_OpenDPTranslation_MakeRowByRowFallible(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_OpenDPCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
