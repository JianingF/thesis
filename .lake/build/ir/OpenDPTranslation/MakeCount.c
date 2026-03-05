// Lean compiler output
// Module: OpenDPTranslation.MakeCount
// Imports: public import Init public import OpenDPTranslation.OpenDPCore public import OpenDPTranslation.MakeRowByRowFallible
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
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDomainAtomDomain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDomainVectorDomain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_SymmetricDistance_toCtorIdx(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_OpenDPTranslation_instDecidableEqIntDistance_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDecidableEqIntDistance_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_OpenDPTranslation_instDecidableEqIntDistance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDecidableEqIntDistance___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instLEIntDistance;
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instLTIntDistance;
static const lean_ctor_object lp_OpenDPTranslation_instPreorderIntDistance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_OpenDPTranslation_instPreorderIntDistance___closed__0 = (const lean_object*)&lp_OpenDPTranslation_instPreorderIntDistance___closed__0_value;
LEAN_EXPORT const lean_object* lp_OpenDPTranslation_instPreorderIntDistance = (const lean_object*)&lp_OpenDPTranslation_instPreorderIntDistance___closed__0_value;
LEAN_EXPORT const lean_object* lp_OpenDPTranslation_instMetricSymmetricDistance = (const lean_object*)&lp_OpenDPTranslation_instPreorderIntDistance___closed__0_value;
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_batteries_List_diff___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_symmetric__distance__list___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_symmetric__distance__list(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instSymmetricDistanceOnListDecEq___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instSymmetricDistanceOnListDecEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_saturating__count___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_saturating__count(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_OpenDPTranslation_make__count___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* lp_OpenDPTranslation_make__count___redArg___closed__0 = (const lean_object*)&lp_OpenDPTranslation_make__count___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation___private_OpenDPTranslation_MakeCount_0__make__count_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation___private_OpenDPTranslation_MakeCount_0__make__count_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDomainAtomDomain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDomainVectorDomain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_SymmetricDistance_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_OpenDPTranslation_instDecidableEqIntDistance_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDecidableEqIntDistance_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_OpenDPTranslation_instDecidableEqIntDistance_decEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_OpenDPTranslation_instDecidableEqIntDistance(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instDecidableEqIntDistance___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_OpenDPTranslation_instDecidableEqIntDistance(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_lp_OpenDPTranslation_instLEIntDistance() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_lp_OpenDPTranslation_instLTIntDistance() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_symmetric__distance__list___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_4);
x_5 = lp_batteries_List_diff___redArg(x_4, x_2, x_3);
x_6 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
x_7 = lp_batteries_List_diff___redArg(x_4, x_3, x_2);
x_8 = l_List_lengthTR___redArg(x_7);
lean_dec(x_7);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
x_10 = lean_nat_to_int(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_symmetric__distance__list(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_OpenDPTranslation_symmetric__distance__list___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instSymmetricDistanceOnListDecEq___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_OpenDPTranslation_symmetric__distance__list), 5, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instSymmetricDistanceOnListDecEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_OpenDPTranslation_symmetric__distance__list), 5, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_OpenDPTranslation_instMetricOnSymmetricDistanceListOfSymmetricDistanceOnList(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_instMetricOnSymDistVecAtom___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnSymDistVecAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_OpenDPTranslation_instMetricOnSymDistVecAtom(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_OpenDPTranslation_instMetricAbsoluteDistanceOfPreorder(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_OpenDPTranslation_instMetricOnAbsoluteDistanceOfAbsoluteDistanceOn(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_OpenDPTranslation_instMetricOnAbsDistAtom___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_instMetricOnAbsDistAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_OpenDPTranslation_instMetricOnAbsDistAtom(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_saturating__count___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
return x_3;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_saturating__count(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_OpenDPTranslation_saturating__count___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_List_lengthTR___redArg(x_2);
x_4 = lp_OpenDPTranslation_saturating__count___redArg(x_1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_OpenDPTranslation_make__count___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_closure((void*)(lp_OpenDPTranslation_make__count___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(lp_OpenDPTranslation_make__count___redArg___lam__1), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_4);
x_9 = ((lean_object*)(lp_OpenDPTranslation_make__count___redArg___closed__0));
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lp_OpenDPTranslation_make__count___redArg(x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation_make__count___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lp_OpenDPTranslation_make__count(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation___private_OpenDPTranslation_MakeCount_0__make__count_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_OpenDPTranslation___private_OpenDPTranslation_MakeCount_0__make__count_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_OpenDPTranslation___private_OpenDPTranslation_MakeCount_0__make__count_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_OpenDPCore(uint8_t builtin);
lean_object* initialize_OpenDPTranslation_OpenDPTranslation_MakeRowByRowFallible(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_OpenDPTranslation_OpenDPTranslation_MakeCount(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_OpenDPCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_OpenDPTranslation_OpenDPTranslation_MakeRowByRowFallible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_OpenDPTranslation_instLEIntDistance = _init_lp_OpenDPTranslation_instLEIntDistance();
lean_mark_persistent(lp_OpenDPTranslation_instLEIntDistance);
lp_OpenDPTranslation_instLTIntDistance = _init_lp_OpenDPTranslation_instLTIntDistance();
lean_mark_persistent(lp_OpenDPTranslation_instLTIntDistance);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
