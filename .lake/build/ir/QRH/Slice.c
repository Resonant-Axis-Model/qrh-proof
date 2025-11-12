// Lean compiler output
// Module: QRH.Slice
// Imports: Init Mathlib QRH.Prelude
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
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_chart(lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_toQuat(lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_reflect(lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_toQuat___boxed(lean_object*);
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_instCoeQuaternionReal;
static lean_object* l_QRH_SlicePoint_instCoeQuaternionReal___closed__0;
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ctorIdx(lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofComplex(lean_object*);
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_QRH_SlicePoint_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_toQuat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_toQuat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_QRH_SlicePoint_toQuat(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_QRH_SlicePoint_instCoeQuaternionReal___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_QRH_SlicePoint_toQuat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_QRH_SlicePoint_instCoeQuaternionReal() {
_start:
{
lean_object* x_1; 
x_1 = l_QRH_SlicePoint_instCoeQuaternionReal___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_chart(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofComplex(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_QRH_SlicePoint_ofQuat___redArg(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_QRH_SlicePoint_ofQuat___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_ofQuat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_QRH_SlicePoint_ofQuat(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_QRH_SlicePoint_reflect(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
x_5 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
x_10 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
lean_object* initialize_QRH_Prelude(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_QRH_Slice(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_QRH_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_QRH_SlicePoint_instCoeQuaternionReal___closed__0 = _init_l_QRH_SlicePoint_instCoeQuaternionReal___closed__0();
lean_mark_persistent(l_QRH_SlicePoint_instCoeQuaternionReal___closed__0);
l_QRH_SlicePoint_instCoeQuaternionReal = _init_l_QRH_SlicePoint_instCoeQuaternionReal();
lean_mark_persistent(l_QRH_SlicePoint_instCoeQuaternionReal);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
