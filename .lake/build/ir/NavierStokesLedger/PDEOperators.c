// Lean compiler output
// Module: NavierStokesLedger.PDEOperators
// Imports: Init Mathlib.Analysis.Calculus.Gradient.Basic Mathlib.Analysis.Calculus.FDeriv.Basic Mathlib.Analysis.Calculus.ContDiff.Basic NavierStokesLedger.BasicDefinitions
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
LEAN_EXPORT lean_object* l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_nat_dec_eq(x_8, x_5);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_1(x_4, lean_box(0));
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, lean_box(0));
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_apply_1(x_2, lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_NavierStokesLedger_PDEOperators_0__NavierStokes_curl_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_Gradient_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_FDeriv_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Calculus_ContDiff_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_NavierStokesLedger_BasicDefinitions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NavierStokesLedger_PDEOperators(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Gradient_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_FDeriv_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_ContDiff_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NavierStokesLedger_BasicDefinitions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
