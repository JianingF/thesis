// Lean compiler output
// Module: OpenDPTranslation.RowByRow
// Imports: public import Init public import OpenDPTranslation.TypeClasses public import OpenDPTranslation.Domains public import OpenDPTranslation.Transformations public import OpenDPTranslation.Axioms public import OpenDPTranslation.RowByRowFallible
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
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_OpenDPTranslation_make__row__by__row__fallible___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(lp_OpenDPTranslation_make__row__by__row___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lp_OpenDPTranslation_make__row__by__row__fallible___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lp_OpenDPTranslation_make__row__by__row___redArg(x_6, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__row__by__row___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lp_OpenDPTranslation_make__row__by__row(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_TypeClasses(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_Domains(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_Transformations(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_Axioms(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_RowByRowFallible(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OpenDPTranslation_OpenDPTranslation_RowByRow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_TypeClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_Domains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_Transformations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_Axioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_RowByRowFallible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
