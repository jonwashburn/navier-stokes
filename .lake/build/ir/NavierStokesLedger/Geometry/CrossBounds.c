// Lean compiler output
// Module: NavierStokesLedger.Geometry.CrossBounds
// Imports: Init Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic Mathlib.Data.Real.Basic Mathlib.Analysis.InnerProductSpace.Basic NavierStokesLedger.BasicDefinitions
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
LEAN_EXPORT lean_object* l_NavierStokes_Geometry_crossProduct(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_Geometry_crossProduct___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_669_(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_476_(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_584_(lean_object*);
LEAN_EXPORT lean_object* l_NavierStokes_Geometry_crossProduct(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_6);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_669_(x_9, x_10);
x_12 = lean_apply_1(x_1, x_6);
x_13 = lean_apply_1(x_2, x_4);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_669_(x_12, x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_584_(x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_476_(x_11, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_18 = lean_apply_1(x_1, x_17);
lean_inc(x_2);
x_19 = lean_apply_1(x_2, x_4);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_669_(x_18, x_19);
x_21 = lean_apply_1(x_1, x_4);
x_22 = lean_apply_1(x_2, x_17);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_669_(x_21, x_22);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_584_(x_23);
x_25 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_476_(x_20, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_27 = lean_apply_1(x_1, x_26);
x_28 = lean_unsigned_to_nat(2u);
lean_inc(x_2);
x_29 = lean_apply_1(x_2, x_28);
x_30 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_669_(x_27, x_29);
x_31 = lean_apply_1(x_1, x_28);
x_32 = lean_apply_1(x_2, x_26);
x_33 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_669_(x_31, x_32);
x_34 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_584_(x_33);
x_35 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_476_(x_30, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_NavierStokes_Geometry_crossProduct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_NavierStokes_Geometry_crossProduct(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_NavierStokesLedger_BasicDefinitions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NavierStokesLedger_Geometry_CrossBounds(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_Basic(builtin, lean_io_mk_world());
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
