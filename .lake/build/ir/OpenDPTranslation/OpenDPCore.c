// Lean compiler output
// Module: OpenDPTranslation.OpenDPCore
// Imports: public import Init public import Mathlib.Order.Basic public import Mathlib.Tactic
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
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_Metric_instPreorderDistance___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instPreorderDistance___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_OpenDPTranslation_Metric_instPreorderDistance(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_Metric_instLEDistance___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_Metric_instLEDistance___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_OpenDPTranslation_Metric_instLEDistance(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_DatasetDomain_instElementDomain___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_DatasetDomain_instElementDomain___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_OpenDPTranslation_DatasetDomain_instElementDomain(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OpenDPTranslation_OpenDPTranslation_OpenDPCore(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
