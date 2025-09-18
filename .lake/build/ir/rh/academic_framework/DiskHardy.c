// Lean compiler output
// Module: rh.academic_framework.DiskHardy
// Imports: Init Mathlib.Data.Complex.Basic Mathlib.Analysis.Analytic.Basic Mathlib.MeasureTheory.Integral.Bochner Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
LEAN_EXPORT lean_object* l_RH_AcademicFramework_DiskHardy_unitDisk;
static lean_object* _init_l_RH_AcademicFramework_DiskHardy_unitDisk() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Complex_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Analytic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Integral_Bochner(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_rh_academic__framework_DiskHardy(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Complex_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Analytic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Integral_Bochner(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_MeasureTheory_Measure_Lebesgue_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RH_AcademicFramework_DiskHardy_unitDisk = _init_l_RH_AcademicFramework_DiskHardy_unitDisk();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
