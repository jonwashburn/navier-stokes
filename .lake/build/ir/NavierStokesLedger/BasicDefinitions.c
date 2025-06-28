// Lean compiler output
// Module: NavierStokesLedger.BasicDefinitions
// Imports: Init Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
LEAN_EXPORT lean_object* l_NavierStokes_C__star;
LEAN_EXPORT lean_object* l_NavierStokes_C__stretch;
LEAN_EXPORT lean_object* l_NavierStokes_C__CZ;
lean_object* l_Rat_ofScientific(lean_object*, uint8_t, lean_object*);
lean_object* l_Nat_cast___at_Real_instNatCast___spec__2(lean_object*);
static lean_object* l_NavierStokes_C__stretch___closed__1;
static lean_object* l_NavierStokes_recognition__tick___closed__1;
static lean_object* l_NavierStokes_recognition__tick___closed__2;
lean_object* l_NNRat_cast___at_Real_instNNRatCast___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes__u03c4__recog;
LEAN_EXPORT lean_object* l_NavierStokes_C__BS;
static lean_object* l_NavierStokes_C__CZ___closed__1;
static lean_object* l_NavierStokes_C__star___closed__1;
LEAN_EXPORT lean_object* l_NavierStokes_recognition__tick;
static lean_object* l_NavierStokes_C__star___closed__2;
static lean_object* _init_l_NavierStokes_C__star___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_NavierStokes_C__star___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_NavierStokes_C__star___closed__1;
x_2 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_NavierStokes_C__star() {
_start:
{
lean_object* x_1; 
x_1 = l_NavierStokes_C__star___closed__2;
return x_1;
}
}
static lean_object* _init_l_NavierStokes_C__BS() {
_start:
{
lean_object* x_1; 
x_1 = l_NavierStokes_C__star___closed__2;
return x_1;
}
}
static lean_object* _init_l_NavierStokes_recognition__tick___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(733u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(17u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_NavierStokes_recognition__tick___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_NavierStokes_recognition__tick___closed__1;
x_2 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_NavierStokes_recognition__tick() {
_start:
{
lean_object* x_1; 
x_1 = l_NavierStokes_recognition__tick___closed__2;
return x_1;
}
}
static lean_object* _init_l_NavierStokes_C__CZ___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_NavierStokes_C__CZ() {
_start:
{
lean_object* x_1; 
x_1 = l_NavierStokes_C__CZ___closed__1;
return x_1;
}
}
static lean_object* _init_l_NavierStokes_C__stretch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at_Real_instNatCast___spec__2(x_1);
return x_2;
}
}
static lean_object* _init_l_NavierStokes_C__stretch() {
_start:
{
lean_object* x_1; 
x_1 = l_NavierStokes_C__stretch___closed__1;
return x_1;
}
}
static lean_object* _init_l_NavierStokes__u03c4__recog() {
_start:
{
lean_object* x_1; 
x_1 = l_NavierStokes_recognition__tick___closed__2;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NavierStokesLedger_BasicDefinitions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_NavierStokes_C__star___closed__1 = _init_l_NavierStokes_C__star___closed__1();
lean_mark_persistent(l_NavierStokes_C__star___closed__1);
l_NavierStokes_C__star___closed__2 = _init_l_NavierStokes_C__star___closed__2();
lean_mark_persistent(l_NavierStokes_C__star___closed__2);
l_NavierStokes_C__star = _init_l_NavierStokes_C__star();
lean_mark_persistent(l_NavierStokes_C__star);
l_NavierStokes_C__BS = _init_l_NavierStokes_C__BS();
lean_mark_persistent(l_NavierStokes_C__BS);
l_NavierStokes_recognition__tick___closed__1 = _init_l_NavierStokes_recognition__tick___closed__1();
lean_mark_persistent(l_NavierStokes_recognition__tick___closed__1);
l_NavierStokes_recognition__tick___closed__2 = _init_l_NavierStokes_recognition__tick___closed__2();
lean_mark_persistent(l_NavierStokes_recognition__tick___closed__2);
l_NavierStokes_recognition__tick = _init_l_NavierStokes_recognition__tick();
lean_mark_persistent(l_NavierStokes_recognition__tick);
l_NavierStokes_C__CZ___closed__1 = _init_l_NavierStokes_C__CZ___closed__1();
lean_mark_persistent(l_NavierStokes_C__CZ___closed__1);
l_NavierStokes_C__CZ = _init_l_NavierStokes_C__CZ();
lean_mark_persistent(l_NavierStokes_C__CZ);
l_NavierStokes_C__stretch___closed__1 = _init_l_NavierStokes_C__stretch___closed__1();
lean_mark_persistent(l_NavierStokes_C__stretch___closed__1);
l_NavierStokes_C__stretch = _init_l_NavierStokes_C__stretch();
lean_mark_persistent(l_NavierStokes_C__stretch);
l_NavierStokes__u03c4__recog = _init_l_NavierStokes__u03c4__recog();
lean_mark_persistent(l_NavierStokes__u03c4__recog);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
