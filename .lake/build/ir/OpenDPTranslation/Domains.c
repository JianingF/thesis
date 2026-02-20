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
static const lean_string_object lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Invalid bounds: lower must be ≤ upper"};
static const lean_object* lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0 = (const lean_object*)&lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0_value;
static const lean_ctor_object lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__0_value)}};
static const lean_object* lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1 = (const lean_object*)&lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Bounds_new__closed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Bounds_new__closed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_OpenDPTranslation_AtomDomain_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_OpenDPTranslation_AtomDomain_default___closed__0 = (const lean_object*)&lp_OpenDPTranslation_AtomDomain_default___closed__0_value;
LEAN_EXPORT lean_object* lp_OpenDPTranslation_AtomDomain_default(lean_object*, lean_object*);
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
x_8 = ((lean_object*)(lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1));
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
x_14 = ((lean_object*)(lp_OpenDPTranslation_Bounds_new__closed___redArg___closed__1));
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
LEAN_EXPORT lean_object* lp_OpenDPTranslation_AtomDomain_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(lp_OpenDPTranslation_AtomDomain_default___closed__0));
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
