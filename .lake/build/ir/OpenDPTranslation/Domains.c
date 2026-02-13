// Lean compiler output
// Module: OpenDPTranslation.Domains
// Imports: public import Init
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
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Bounds_new__closed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1;
static lean_object* lp_OpenDPTranslation_AtomDomain_default___closed__0;
LEAN_EXPORT lean_object* lp_OpenDPTranslation_AtomDomain_default(lean_object*, lean_object*);
static lean_object* lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0;
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Bounds_new__closed___redArg(lean_object*, lean_object*);
static lean_object* _init_lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid bounds: lower must be ≤ upper", 39, 37);
return x_1;
}
}
static lean_object* _init_lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Bounds_new__closed___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_apply_2(x_1, x_4, x_5);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_free_object(x_2);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_apply_2(x_1, x_10, x_11);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Bounds_new__closed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_OpenDPTranslation_Bounds_new__closed___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_lp_OpenDPTranslation_AtomDomain_default___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_AtomDomain_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_OpenDPTranslation_AtomDomain_default___closed__0;
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OpenDPTranslation_OpenDPTranslation_Domains(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0 = _init_lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0();
lean_mark_persistent(lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0);
lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1 = _init_lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1();
lean_mark_persistent(lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1);
lp_OpenDPTranslation_AtomDomain_default___closed__0 = _init_lp_OpenDPTranslation_AtomDomain_default___closed__0();
lean_mark_persistent(lp_OpenDPTranslation_AtomDomain_default___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
