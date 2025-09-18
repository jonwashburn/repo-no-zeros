import rh.academic_framework.DiskHardy
import rh.academic_framework.HalfPlaneOuter

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework

/-- Cayley map from the right half-plane Ω = {Re s > 1/2} to the unit disk. -/
@[simp] def toDisk (s : ℂ) : ℂ := (s - (1 : ℂ)) / s

/-- Inverse Cayley map from the unit disk to the right half-plane Ω. -/
@[simp] def toHalf (w : ℂ) : ℂ := 1 / (1 - w)

/-- Boundary parametrization transport under Cayley: on Re s=1/2, the image lies on ∂𝔻. -/
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (HalfPlaneOuter.boundary t)

/-- On the right half–plane (in particular for any `s ≠ 0`), `toHalf` inverts `toDisk`. -/
lemma toHalf_comp_toDisk {s : ℂ} (hs : s ≠ 0) : toHalf (toDisk s) = s := by
  -- toHalf ((s - 1) / s) = 1 / (1 - (s - 1)/s) = 1 / ((s - (s - 1))/s) = 1 / (1/s) = s
  have hden : (1 - (s - 1) / s) = (1 : ℂ) / s := by
    field_simp [toDisk, sub_eq_add_neg, hs]
  have : toHalf (toDisk s) = (1 : ℂ) / ((1 : ℂ) / s) := by
    simp [toHalf, toDisk, hden]
  simpa [one_div, inv_inv] using this

/-- Algebraic identity: difference of Cayley images collapses to a single fraction. -/
lemma toDisk_sub_toDisk (s₁ s₂ : ℂ) (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0) :
    toDisk s₁ - toDisk s₂ = (s₁ - s₂) / (s₁ * s₂) := by
  -- (s₁-1)/s₁ - (s₂-1)/s₂ = (s₂(s₁-1) - s₁(s₂-1)) / (s₁ s₂) = (s₁ - s₂) / (s₁ s₂)
  have h : toDisk s₁ - toDisk s₂ = (s₂ * (s₁ - 1) - s₁ * (s₂ - 1)) / (s₁ * s₂) := by
    field_simp [toDisk, hs₁, hs₂]
  have hnum : s₂ * (s₁ - 1) - s₁ * (s₂ - 1) = s₁ - s₂ := by ring
  simpa [hnum]

/-- Norm identity used in Poisson kernel CoV: `1 - ‖(s-1)/s‖^2 = (2·Re s - 1)/‖s‖^2`. -/
lemma one_sub_norm_toDisk_sq (s : ℂ) (hs : s ≠ 0) :
    1 - ‖toDisk s‖^2 = (2 * s.re - 1) / ‖s‖^2 := by
  -- ‖(s-1)/s‖^2 = ‖s-1‖^2 / ‖s‖^2 ⇒
  -- 1 - that = (‖s‖^2 - ‖s-1‖^2) / ‖s‖^2 = (2 Re s - 1)/‖s‖^2
  have hpos : ‖s‖^2 ≠ 0 := by
    have : ‖s‖ ≠ 0 := by
      simpa [Complex.norm_eq_zero] using hs
    exact by
      have : (‖s‖^2 : ℝ) ≠ 0 := mul_ne_zero (by exact_mod_cast this) (by exact_mod_cast this) |> ?_;
      -- simplify: since ‖s‖ ≥ 0, use pow_two_ne_zero
      simpa [pow_two] using (pow_ne_zero 2 (by exact_mod_cast this))
  have hnorm : ‖toDisk s‖^2 = ‖s - 1‖^2 / ‖s‖^2 := by
    have : ‖toDisk s‖ = ‖s - 1‖ / ‖s‖ := by
      simp [toDisk, Complex.norm_div, Complex.abs.cast]
    simpa [this, sq_div]
  have : 1 - (‖s - 1‖^2 / ‖s‖^2) = (‖s‖^2 - ‖s - 1‖^2) / ‖s‖^2 := by
    field_simp [hpos]
  have hdiff : (‖s‖^2 - ‖s - 1‖^2) = (2 * s.re - 1) := by
    -- Expand using ‖z‖^2 = z.re^2 + z.im^2
    have : ‖s‖^2 = s.re^2 + s.im^2 := by simpa [Complex.norm_sq] using Complex.norm_sq_eq_real_inner (z := s)
    have : ‖s - 1‖^2 = (s.re - 1)^2 + s.im^2 := by
      have : (s - 1).re = s.re - 1 := by simp
      have : (s - 1).im = s.im := by simp
      simpa [Complex.norm_sq, this, *]
    ring_nf at *
    -- Using real ring arithmetic: (sr^2+si^2) - ((sr-1)^2+si^2) = 2sr - 1
    have sr : ℝ := s.re; have si : ℝ := s.im
    have : (sr^2 + si^2) - ((sr - 1)^2 + si^2) = 2 * sr - 1 := by ring
    simpa using this
  simpa [hnorm, this, hdiff]

/-- Distance identity along the boundary map: denominator transforms with a simple factor. -/
lemma norm_sub_toDisk_boundary_sq (z : ℂ) (t : ℝ) (hz : z ≠ 0) :
    ‖boundaryToDisk t - toDisk z‖^2
      = ‖(HalfPlaneOuter.boundary t) - z‖^2 / (‖HalfPlaneOuter.boundary t‖^2 * ‖z‖^2) := by
  -- From `toDisk_sub_toDisk`, take norms and square
  have hb : HalfPlaneOuter.boundary t ≠ 0 := by
    -- 1/2 + i t ≠ 0
    intro h0
    have hre : (HalfPlaneOuter.boundary t).re = 1/2 := by simp [HalfPlaneOuter.boundary]
    have him : (HalfPlaneOuter.boundary t).im = t := by simp [HalfPlaneOuter.boundary]
    have : (HalfPlaneOuter.boundary t) ≠ 0 := by
      intro h; have : (1/2 : ℝ) = 0 := by simpa [h, Complex.zero_re] using hre; norm_num at this
    exact this h0
  have hdiff : boundaryToDisk t - toDisk z = ((HalfPlaneOuter.boundary t) - z) / ((HalfPlaneOuter.boundary t) * z) := by
    simpa [boundaryToDisk] using toDisk_sub_toDisk (s₁ := HalfPlaneOuter.boundary t) (s₂ := z) hb hz
  have : ‖boundaryToDisk t - toDisk z‖ = ‖(HalfPlaneOuter.boundary t) - z‖ / ‖(HalfPlaneOuter.boundary t) * z‖ := by
    simpa [hdiff, Complex.norm_div]
  have hmul : ‖(HalfPlaneOuter.boundary t) * z‖ = ‖HalfPlaneOuter.boundary t‖ * ‖z‖ := by
    simpa [Complex.norm_mul]
  have : ‖boundaryToDisk t - toDisk z‖^2 = (‖(HalfPlaneOuter.boundary t) - z‖^2) / (‖HalfPlaneOuter.boundary t‖^2 * ‖z‖^2) := by
    simpa [this, hmul, sq_div, sq_mul]
  simpa using this

/-- Bridge (packaging form): Given the Cayley relation between `F` and a disk-side
transform `Hdisk`, together with half-plane analyticity, boundary integrability,
and the Poisson identity on Ω, produce the half-plane Poisson representation
record. This removes internal admits; callers supply the analytic facts. -/
def HalfPlanePoisson_from_Disk
  (F : ℂ → ℂ)
  (Hdisk : ℂ → ℂ)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuter.Ω)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuter.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuter.Ω,
    Integrable (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re * HalfPlaneOuter.poissonKernel z t))
  (hReEq : ∀ z ∈ HalfPlaneOuter.Ω,
    (F z).re = HalfPlaneOuter.P (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re) z)
  : HalfPlaneOuter.HasHalfPlanePoissonRepresentation F := by
  -- Package the provided half-plane facts directly; no internal admits.
  exact {
    analytic := hAnalytic
  , integrable := hIntegrable
  , re_eq := hReEq }

end CayleyAdapters
end AcademicFramework
end RH
