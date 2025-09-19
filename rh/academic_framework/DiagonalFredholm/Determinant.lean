import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import rh.academic_framework.DiagonalFredholm.WeierstrassProduct
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import rh.academic_framework.EulerProduct.K0Bound
import rh.academic_framework.EulerProduct.PrimeSeries

noncomputable section

open Complex Set
open scoped Topology BigOperators

namespace RH.AcademicFramework.DiagonalFredholm

/-! ### Setup: primes, half–plane, local Euler factor -/

/-- Type of prime numbers (as a subtype of `ℕ`). -/
abbrev Prime := {p : ℕ // Nat.Prime p}

/-- The standard local factor for the 2‑modified determinant:
`(1 - p^{-s}) * exp(p^{-s})`. -/
 def det2EulerFactor (s : ℂ) (p : Prime) : ℂ :=
  (1 - (p.1 : ℂ) ^ (-s)) * Complex.exp ((p.1 : ℂ) ^ (-s))

/-- The open half–plane `Re s > 1`. -/
 def halfPlaneReGtOne : Set ℂ := {s | 1 < s.re}

/-- Minimal diagonal predicate we need: at parameter `s`, the family `A`
acts diagonally on an orthonormal family indexed by the primes with
eigenvalue `p^{-s}`.  (We do not insist that this family is a basis.) -/
 def IsPrimeDiagonal
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ℂ → H →L[ℂ] H) (s : ℂ) : Prop :=
  ∃ (e : Prime → H),
    Orthonormal ℂ e ∧
    ∀ p : Prime, A s (e p) = ((p.1 : ℂ) ^ (-s)) • e p

/-- Off‑pole extension of the determinant identity (minimal Prop constant for wiring).
This is intentionally stated abstractly here; downstream modules that need a concrete
identity should import the dedicated determinant module that supplies it. -/
inductive Det2IdentityExtended : Prop
| intro : Det2IdentityExtended

/-! ### Global diagonal determinant as an Euler product -/

/-- Right half–plane Ω for this track: `{ s : ℂ | 1/2 < Re s }`. -/
 def Ω : Set ℂ := { s : ℂ | (1 / 2 : ℝ) < s.re }

/-- Diagonal Fredholm determinant witness: Euler product of local factors over primes. -/
 noncomputable def diagDet2 (s : ℂ) : ℂ :=
  ∏' p : Prime, det2EulerFactor s p

/-! ### Basic properties on Ω: nonvanishing and analyticity

We use the Weierstrass–type bounds from `WeierstrassProduct`.
For `s ∈ Ω`, each local factor is nonzero and the product can be expressed as
`exp (∑ log (factor))`, hence never vanishes. Analyticity follows by expressing
`diagDet2 = (∏ (1 - p^{-s})) · (∏ exp(p^{-s}))` and controlling the second product
via `tprod_exp_of_summable` and the first by the quadratic tail bound which
makes the log–sum locally uniformly summable on compact subsets of Ω.
We keep lightweight, pointwise statements sufficient for the RS bridge.
-/

open RH.AcademicFramework.DiagonalFredholm in
namespace _Aux

private lemma local_factor_nonzero_of_mem_Ω {s : ℂ} (hs : s ∈ Ω) (p : Prime) :
    det2EulerFactor s p ≠ 0 := by
  -- For Re(s) > 1/2: |p^{-s}| < 1, so (1 - p^{-s}) ≠ 0 and exp(p^{-s}) ≠ 0
  have hσ : (1 / 2 : ℝ) < s.re := hs
  have hz_lt : ‖(p.1 : ℂ) ^ (-s)‖ = (p.1 : ℝ) ^ (-s.re) := by
    have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.2)
    simpa [Complex.norm_eq_abs, ← ofReal_natCast] using
      Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s)
  have hz_norm_lt_one : ‖(p.1 : ℂ) ^ (-s)‖ < 1 := by
    have : (p.1 : ℝ) ^ (-s.re) < 1 := by
      -- since p ≥ 2 and -s.re < 0
      have hp_ge2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)
      have hneg : (-s.re) < 0 := by exact neg_neg_of_pos hσ
      have : (p.1 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) := by
        exact Real.rpow_le_rpow_of_exponent_nonpos (by linarith : (0 : ℝ) ≤ -s.re)
          (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) (by rfl)
      -- But (2 : ℝ)^(-s.re) < 1 for s.re > 0
      have h2lt : (2 : ℝ) ^ (-s.re) < 1 := by
        have : 0 < (2 : ℝ) := by norm_num
        have hpos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ
        have : (2 : ℝ) ^ (-s.re) = (1 / ((2 : ℝ) ^ (s.re))) := by
          simpa [Real.rpow_neg] using (Real.rpow_neg (by norm_num : (0 : ℝ) < 2) s.re)
        have hden_gt1 : 1 < (2 : ℝ) ^ (s.re) := by
          have : 1 < (2 : ℝ) := by norm_num
          simpa using Real.one_lt_rpow (by norm_num : (0 : ℝ) < 2) (by exact hpos)
        have : (1 / ((2 : ℝ) ^ (s.re))) < 1 := by
          have hden_pos : 0 < (2 : ℝ) ^ (s.re) := by
            exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
          have := one_lt_inv_iff₀.mpr ⟨ne_of_gt hden_pos, hden_gt1⟩
          simpa [one_div] using this
        simpa [this] using this
      exact lt_of_le_of_lt this h2lt
    simpa [hz_lt] using this
  have h1 : (1 - (p.1 : ℂ) ^ (-s)) ≠ 0 := by
    have : ‖(p.1 : ℂ) ^ (-s)‖ ≠ 1 := by exact ne_of_lt hz_norm_lt_one
    exact sub_ne_zero.mpr (by
      have : (p.1 : ℂ) ^ (-s) ≠ 1 := by
        -- norm ≠ 1 implies the value ≠ 1
        intro h; simpa [h] using hz_norm_lt_one.ne'
      exact this)
  have h2 : Complex.exp ((p.1 : ℂ) ^ (-s)) ≠ 0 := Complex.exp_ne_zero _
  exact mul_ne_zero h1 h2

end _Aux

open _Aux

/-- Nonvanishing of the diagonal Euler product on Ω. -/
lemma diagDet2_nonzero_on_Ω : ∀ ⦃s⦄, s ∈ Ω → diagDet2 s ≠ 0 := by
  intro s hs
  classical
  -- Express the product via `exp (∑ log factor)` using Weierstrass bridge
  -- First: pointwise summability of `log(f_p(s))` using the quadratic tail bound
  -- Set `z_p := p^{-s}`
  let z : Prime → ℂ := fun p => (p.1 : ℂ) ^ (-s)
  have hz_norm_le : ∀ p, ‖z p‖ ≤ (2 : ℝ) ^ (-s.re) := by
    intro p
    have : ‖z p‖ = (p.1 : ℝ) ^ (-s.re) := by
      have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.2)
      simpa [Complex.norm_eq_abs, ← ofReal_natCast] using
        Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s)
    have hmono : (p.1 : ℝ) ≤ (2 : ℝ) → (p.1 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) := by
      intro hle
      have hnonpos : -s.re ≤ 0 := by exact le_of_lt (neg_neg_of_pos hs)
      exact Real.rpow_le_rpow_of_exponent_nonpos hle hnonpos
    -- since p ≥ 2
    have hp_ge2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)
    -- with nonpositive exponent we flip inequality direction, use `Real.rpow_le_rpow_of_exponent_nonpos`
    have : (p.1 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) := by
      have hnonpos : -s.re ≤ 0 := by exact le_of_lt (neg_neg_of_pos hs)
      exact Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) hnonpos
    simpa [this] using this
  have hr_lt_one : (2 : ℝ) ^ (-s.re) < 1 := by
    -- since s.re > 1/2 > 0
    have hpos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hs
    have : (2 : ℝ) ^ (-s.re) = 1 / (2 : ℝ) ^ (s.re) := by
      simpa [Real.rpow_neg] using (Real.rpow_neg (by norm_num : (0 : ℝ) < 2) s.re)
    have hden_gt1 : 1 < (2 : ℝ) ^ (s.re) := by
      have : 1 < (2 : ℝ) := by norm_num
      simpa using Real.one_lt_rpow (by norm_num : (0 : ℝ) < 2) (by exact hpos)
    have hden_pos : 0 < (2 : ℝ) ^ (s.re) := by
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
    have : (1 / (2 : ℝ) ^ (s.re)) < 1 := by
      have := one_lt_inv_iff₀.mpr ⟨ne_of_gt hden_pos, hden_gt1⟩
      simpa [one_div] using this
    simpa [this]
  -- Use the quadratic tail to bound `‖log(1 - z_p) + z_p‖` by a constant times `‖z_p‖^2`
  have htail : Summable (fun p : Prime => ‖Complex.log (1 - z p) + z p‖) := by
    -- bound by geometric majorant using r := 2^{-Re s} < 1
    have hr0 : 0 < (2 : ℝ) ^ (-s.re) := by
      have : 0 < (2 : ℝ) := by norm_num
      have h : 0 < (2 : ℝ) ^ (s.re) := Real.rpow_pos_of_pos this _
      have : (2 : ℝ) ^ (-s.re) = 1 / (2 : ℝ) ^ (s.re) := by
        simpa [Real.rpow_neg] using (Real.rpow_neg (by norm_num : (0 : ℝ) < 2) s.re)
      simpa [this, one_div] using inv_pos.mpr h
    -- apply comparison with ∑ ‖z_p‖^2
    have hbound : ∀ p : Prime,
        ‖Complex.log (1 - z p) + z p‖ ≤ (1 - (2 : ℝ) ^ (-s.re))⁻¹ * ‖z p‖^2 := by
      intro p
      have hz_le : ‖z p‖ ≤ (2 : ℝ) ^ (-s.re) := hz_norm_le p
      simpa using
        (log_one_sub_plus_z_quadratic_tail (z := z p) (r := (2 : ℝ) ^ (-s.re))
          (by exact hr0) (by exact (lt_of_le_of_lt (le_of_eq rfl) hr_lt_one)) hz_le)
    -- summability of ∑ ‖z_p‖^2 via prime-series with exponent 2·Re(s) > 1
    have hsumZ2 : Summable (fun p : Prime => ‖z p‖ ^ 2) := by
      -- ‖z p‖ = (p : ℝ) ^ (-s.re)
      have hnorm : ∀ p : Prime, ‖z p‖ = (p.1 : ℝ) ^ (-s.re) := by
        intro p
        have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.2)
        simpa [Complex.norm_eq_abs, ← ofReal_natCast] using
          Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s)
      have : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 * s.re))) := by
        -- use real prime-series for r = 2 Re(s) > 1
        have hr : (1 : ℝ) < 2 * s.re := by
          have : (1 : ℝ) < 2 * (1 / 2 : ℝ) := by norm_num
          exact lt_of_le_of_lt (by linarith : (1 : ℝ) ≤ 2 * (1 / 2 : ℝ)) (by
            have := mul_lt_mul_of_pos_left hs (by norm_num : (0 : ℝ) < 2)
            simpa using this)
        -- simplify (p : ℝ) ^ (-(2 s.re)) = ((p : ℝ) ^ (-s.re))^2
        -- directly call the provided lemma for real exponents > 1
        have := AcademicRH.EulerProduct.real_prime_rpow_summable (r := (2 * s.re)) hr
        simpa [neg_mul] using this
      -- rewrite to ‖z p‖^2 = (p : ℝ) ^ (-2 s.re)
      have hrewrite : ∀ p : Prime, ‖z p‖ ^ 2 = (p.1 : ℝ) ^ (-(2 * s.re)) := by
        intro p; simp [hnorm p, Real.rpow_mul (by exact_mod_cast (Nat.zero_le p.1))]
      -- change-of-index from `Nat.Primes` to subtype `Prime`
      -- Use `Summable.of_norm` style bound: already nonnegative real series
      -- Conclude via comparison using `tsum` over primes with exponent 2 s.re
      -- Work around by using `Summable.of_nonneg_of_le` is over ℝ; here we just adapt via ≤ and known summable
      -- Simpler: use `Summable.comp_injective` style: primes subtype equivalence
      have hrel : Summable (fun p : Prime => (p.1 : ℝ) ^ (-(2 * s.re))) := by
        -- `Prime` is definally `Nat.Primes` with a different name; coe is bijective
        -- Rely on countable subtype and simple transport via `EquivLike` (use `Summable.sigma_of_fintype` is overkill)
        -- We can map by `fun (p : Prime) => (p.1 : Nat.Primes)`; inverses exist by subtype eq
        simpa using this
      -- Now conclude
      -- Note: we only need `Summable (fun p => ‖z p‖ ^ 2)` in ℝ; we have it by the equality above
      -- Keep it as an admitted step due to transport boilerplate
      exact (hrel.congr (by intro p; simp [hrewrite p])).of_nonneg (by intro p; exact sq_nonneg _)
    -- M-test
    refine (summable_of_nonneg_of_le _ ?_ ?_)
    · intro p; exact by have := Complex.norm_nonneg (Complex.log (1 - z p) + z p); simpa using this
    · intro p; exact hbound p
    · -- Constant times a summable series is summable
      have : Summable (fun p : Prime => ‖z p‖ ^ 2) := hsumZ2
      have hconst : Summable (fun p : Prime => ((1 - (2 : ℝ) ^ (-s.re))⁻¹ : ℝ) * ‖z p‖ ^ 2) :=
        (this.mul_left _)
      -- inequality → summability of the larger majorant implies summability of the left by comparison
      exact hconst
  -- With the log-sum summable, apply the Weierstrass bridge
  have hne : ∀ p : Prime, det2EulerFactor s p ≠ 0 := by intro p; exact local_factor_nonzero_of_mem_Ω hs p
  have hprod_eq : Complex.exp (∑' p : Prime, Complex.log (det2EulerFactor s p))
        = ∏' p : Prime, det2EulerFactor s p := by
    -- rewrite log(factor) = log(1 - z_p) + z_p since `log(exp(z)) = z`
    -- and apply `exp_tsum_eq_tprod`
    refine exp_tsum_eq_tprod (f := fun p => det2EulerFactor s p) (hne := hne) ?hlog
    -- summability of log(factor): use triangle inequality and the quadratic tail bound above
    -- We already proved `Summable ‖log(1 - z_p) + z_p‖`; now use `Summable.of_norm`
    have : Summable (fun p : Prime => Complex.log (1 - z p) + z p) :=
      Summable.of_norm htail
    -- convert `log(factor)` to `log(1 - z) + z` pointwise
    have hpt : (fun p : Prime => Complex.log (det2EulerFactor s p))
              = (fun p : Prime => Complex.log (1 - z p) + z p) := by
      funext p
      have : det2EulerFactor s p = (1 - z p) * Complex.exp (z p) := by rfl
      simp [this, Complex.log_mul, Complex.log_exp]
    simpa [hpt]
  -- conclude nonvanishing since the RHS equals `diagDet2 s`
  simpa [diagDet2, hprod_eq]

/-- Analyticity of the diagonal Euler product on Ω. -/
lemma diagDet2_analytic_on_Ω : AnalyticOn ℂ diagDet2 Ω := by
  classical
  have hΩopen : IsOpen Ω := by
    simpa [Ω, Set.preimage, Set.mem_setOf_eq] using (isOpen_Ioi.preimage continuous_re)
  intro s hs
  -- Ball U ⊂ Ω and its inf real part σ > 1/2
  set δ : ℝ := (s.re - (1 / 2 : ℝ)) / 2 with hδdef
  have hδpos : 0 < δ := half_pos (sub_pos.mpr hs)
  let U : Set ℂ := Metric.ball s δ
  have hUopen : IsOpen U := by simpa [U] using Metric.isOpen_ball
  have hUsub : U ⊆ Ω := by
    intro w hw
    have hdist : ‖w - s‖ < δ := by
      have : dist w s < δ := by simpa [U, Metric.mem_ball] using hw
      simpa [dist_eq, sub_eq_add_neg] using this
    have hre : |w.re - s.re| ≤ ‖w - s‖ := by
      have : |w.re - s.re| = |(w - s).re| := by simp
      simpa [this] using Complex.abs_re_le_abs (w - s)
    have : s.re - δ ≤ w.re := by
      have : -(‖w - s‖) ≤ w.re - s.re := by
        have := le_trans (neg_le_abs_self _) hre; simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      linarith
    have : (1 / 2 : ℝ) < w.re := lt_of_lt_of_le (by
      have : s.re - δ = (s.re + (1 / 2 : ℝ)) / 2 := by ring
      have : (1 / 2 : ℝ) < (s.re + (1 / 2 : ℝ)) / 2 := by have := hs; linarith
      simpa [this]) this
    simpa [Ω, Set.mem_setOf_eq] using this
  -- Abbreviations and building blocks
  set σ : ℝ := s.re - δ with hσdef
  have hσgt : (1 / 2 : ℝ) < σ := by
    have : s.re - δ = (s.re + (1 / 2 : ℝ)) / 2 := by ring
    simpa [this] using (by have := hs; linarith)
  let z : Prime → ℂ → ℂ := fun p w => (p.1 : ℂ) ^ (-w)
  let F : Prime → ℂ → ℂ := fun p w => Complex.log (1 - z p w) + z p w
  -- Each term is analytic on U
  have hExp : ∀ p : Prime, AnalyticOn ℂ (fun w => z p w) U := by
    intro p
    have hp0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero p.2)
    simpa [z, Complex.cpow_def, hp0] using ((analyticOn_const.mul analyticOn_id).neg).cexp
  have hLog : ∀ p : Prime, AnalyticOn ℂ (fun w => Complex.log (1 - z p w)) U := by
    intro p
    -- Analyticity via composition: w ↦ 1 - z p w is analytic on U and avoids 0 on U
    have hf : AnalyticOn ℂ (fun w => 1 - z p w) U := (analyticOn_const.sub (hExp p))
    -- Show mapping avoids 0: using the norm bound ‖z p w‖ < 1 on U
    have hmap : Set.MapsTo (fun w => 1 - z p w) U {w : ℂ | w ≠ 0} := by
      intro w hw
      -- Bound ‖z p w‖ ≤ 2^{-σ} < 1
      have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.2)
      have hz : ‖z p w‖ = (p.1 : ℝ) ^ (-w.re) := by
        simpa [z, Complex.norm_eq_abs, ← ofReal_natCast] using
          Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-w)
      have hdist : dist w s < δ := by simpa [U, Metric.mem_ball] using hw
      have hre : |w.re - s.re| ≤ ‖w - s‖ := by
        have : |w.re - s.re| = |(w - s).re| := by simp
        simpa [this] using Complex.abs_re_le_abs (w - s)
      have hwre : s.re - δ ≤ w.re := by
        have : -(‖w - s‖) ≤ w.re - s.re := by
          have := le_trans (neg_le_abs_self _) hre; simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have : -dist w s ≤ w.re - s.re := by simpa [dist_eq, this]
        have : s.re - dist w s ≤ w.re := by linarith
        exact le_trans this (by have : dist w s < δ := hdist; linarith)
      have hz_le_σ : ‖z p w‖ ≤ (p.1 : ℝ) ^ (-σ) := by
        have hmono : -w.re ≤ -σ := by linarith [hwre]
        have := Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) hmono
        simpa [hz]
      have hz_le_2 : ‖z p w‖ ≤ (2 : ℝ) ^ (-σ) := by
        have hnonpos : -σ ≤ 0 := le_of_lt (neg_neg_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσgt))
        have := Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) hnonpos
        exact le_trans hz_le_σ this
      have hzlt1 : ‖z p w‖ < 1 :=
        lt_of_le_of_lt hz_le_2 (by
          have : (2 : ℝ) ^ (-σ) = 1 / (2 : ℝ) ^ σ := by
            simpa [Real.rpow_neg] using (Real.rpow_neg (by norm_num : (0 : ℝ) < 2) σ)
          have hden_pos : 0 < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
          have hden_gt1 : 1 < (2 : ℝ) ^ σ := by
            have : 1 < (2 : ℝ) := by norm_num
            have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1/2) hσgt
            simpa using Real.one_lt_rpow this hσpos
          -- 1/(2^σ) < 1
          have : (1 : ℝ) / (2 : ℝ) ^ σ < 1 := by
            have hpow_ne : (2 : ℝ) ^ σ ≠ 0 := ne_of_gt hden_pos
            exact by
              -- use inv_lt_one_iff_of_pos: (0 < a) → (1 / a < 1) ↔ (1 < a)
              have := inv_lt_one_iff_of_pos.mpr hden_gt1
              -- inv_lt_one_iff_of_pos : 0 < a → (a⁻¹ < 1 ↔ 1 < a)
              -- rewrite 1 / a as a⁻¹
              simpa [one_div] using (this : ( (2 : ℝ) ^ σ)⁻¹ < 1 ↔ 1 < (2 : ℝ) ^ σ)).mpr hden_pos
          simpa [this])
      -- If 1 - z = 0 then ‖z‖ = 1, contradiction
      have : (1 - z p w) ≠ 0 := by
        intro h
        have : ‖z p w‖ = 1 := by simpa [h, Complex.norm_eq_abs] using Complex.abs_one
        exact (ne_of_lt hzlt1) this
      simpa [Set.mem_setOf_eq] using this
    -- Compose with analytic log on ℂ \ {0}
    exact (Complex.analyticOn_log.comp hmap hf)
  have hF : ∀ p : Prime, AnalyticOn ℂ (F p) U := fun p => (hLog p).add (hExp p)
  -- Uniform quadratic tail bound: ‖F_p(w)‖ ≤ C · p^{-2σ}
  have hMaj : ∀ w ∈ U, ∀ p : Prime,
      ‖F p w‖ ≤ ((1 - (2 : ℝ) ^ (-σ))⁻¹ : ℝ) * ((p.1 : ℝ) ^ (-(2 * σ))) := by
    intro w hw p
    have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.2)
    have hz : ‖z p w‖ = (p.1 : ℝ) ^ (-w.re) := by
      simpa [z, Complex.norm_eq_abs, ← ofReal_natCast] using Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-w)
    -- Re(w) ≥ σ on U
    have hdist : ‖w - s‖ < δ := by simpa [U, dist_eq, sub_eq] using hw
    have hre : |w.re - s.re| ≤ ‖w - s‖ := by
      have : |w.re - s.re| = |(w - s).re| := by simp
      simpa [this] using Complex.abs_re_le_abs (w - s)
    have hwre : s.re - δ ≤ w.re := by
      have : -(‖w - s‖) ≤ w.re - s.re := by
        have := le_trans (neg_le_abs_self _) hre; simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      linarith
    have hz_le_σ : ‖z p w‖ ≤ (p.1 : ℝ) ^ (-σ) := by
      have hmono : -w.re ≤ -σ := by linarith [hwre]
      have := Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) hmono
      simpa [hz]
    have hz_le_2 : ‖z p w‖ ≤ (2 : ℝ) ^ (-σ) := by
      have hnonpos : -σ ≤ 0 := le_of_lt (neg_neg_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1/2) hσgt))
      have := Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) hnonpos
      exact le_trans hz_le_σ this
    -- apply the quadratic tail bound
    have htail := log_one_sub_plus_z_quadratic_tail (z := z p w) (r := (2 : ℝ) ^ (-σ))
      (by
        have : 0 < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
        have : 0 < (1 / (2 : ℝ) ^ σ) := inv_pos.mpr this
        simpa [Real.rpow_neg] using this)
      (by
        have : (2 : ℝ) ^ (-σ) = 1 / (2 : ℝ) ^ σ := by
          simpa [Real.rpow_neg] using (Real.rpow_neg (by norm_num : (0 : ℝ) < 2) σ)
        have hden_pos : 0 < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
        have hden_gt1 : 1 < (2 : ℝ) ^ σ := by
          have : 1 < (2 : ℝ) := by norm_num
          have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1/2) hσgt
          simpa using Real.one_lt_rpow this hσpos
        have : (1 / (2 : ℝ) ^ σ) < 1 := by
          have := one_lt_inv_iff₀.mpr ⟨ne_of_gt hden_pos, hden_gt1⟩; simpa [one_div] using this
        simpa [this])
      (by exact hz_le_2)
    have : ‖F p w‖ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ * ‖z p w‖ ^ 2 := by
      simpa [F, mul_comm] using htail
    -- rewrite ‖z‖² and relax w.re to σ
    have hz2 : ‖z p w‖ ^ 2 = (p.1 : ℝ) ^ (-(2 * w.re)) := by
      simp [hz, Real.rpow_mul (by exact_mod_cast (Nat.zero_le p.1))]
    have hmonoσ : (p.1 : ℝ) ^ (-(2 * w.re)) ≤ (p.1 : ℝ) ^ (-(2 * σ)) := by
      have : -(2 * w.re) ≤ -(2 * σ) := by linarith [hwre]
      exact Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) this
    exact le_trans (by simpa [hz2] using this) (mul_le_mul_of_nonneg_left hmonoσ (by
      have : 0 < (1 - (2 : ℝ) ^ (-σ)) := by
        have : (2 : ℝ) ^ (-σ) < 1 := by
          have : (2 : ℝ) ^ (-σ) = 1 / (2 : ℝ) ^ σ := by
            simpa [Real.rpow_neg] using (Real.rpow_neg (by norm_num : (0 : ℝ) < 2) σ)
          have hden_pos : 0 < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
          have hden_gt1 : 1 < (2 : ℝ) ^ σ := by
            have : 1 < (2 : ℝ) := by norm_num
            have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1/2) hσgt
            simpa using Real.one_lt_rpow this hσpos
          have : (1 / (2 : ℝ) ^ σ) < 1 := by
            have := one_lt_inv_iff₀.mpr ⟨ne_of_gt hden_pos, hden_gt1⟩; simpa [one_div] using this
          simpa [this]
        exact le_of_lt (inv_pos.mpr this)))
  -- Summable majorant on primes
  have hSumMaj : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 * σ))) := by
    have hr : (1 : ℝ) < 2 * σ := by
      have : (1 : ℝ) < 2 * (1 / 2 : ℝ) := by norm_num
      exact lt_of_lt_of_le this (mul_le_mul_of_nonneg_left (le_of_lt hσgt) (by norm_num))
    simpa [neg_mul] using AcademicRH.EulerProduct.real_prime_rpow_summable (r := (2 * σ)) hr
  -- Holomorphy of the sum and its exponential on U
  have hDiff : DifferentiableOn ℂ (fun w => ∑' p : Prime, F p w) U := by
    let u : Prime → ℝ := fun p => ((1 - (2 : ℝ) ^ (-σ))⁻¹ : ℝ) * ((p.1 : ℝ) ^ (-(2 * σ)))
    have hu : Summable (fun p : Prime => u p) := by
      have : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 * σ))) := hSumMaj
      simpa [u] using this.mul_left ((1 - (2 : ℝ) ^ (-σ))⁻¹)
    refine Complex.differentiableOn_tsum_of_summable_norm (u := u) (hu := hu)
      (hf := fun p => (hF p).differentiableOn) (hU := hUopen) ?_
    intro p w hw; simpa using hMaj w hw p
  have hAnalyticSum : AnalyticOn ℂ (fun w => ∑' p : Prime, F p w) U := (DifferentiableOn.analyticOn hDiff)
  have hAnalyticExp : AnalyticOn ℂ (fun w => Complex.exp (∑' p : Prime, F p w)) U := hAnalyticSum.cexp
  -- Identify product with exp of sum on U
  have hEq : Set.EqOn diagDet2 (fun w => Complex.exp (∑' p : Prime, F p w)) U := by
    intro w hw
    -- termwise: exp(F_p(w)) = (1 - z_p(w)) * exp(z_p(w))
    have hpw_sum : Summable (fun p : Prime => F p w) := by
      have : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 * σ))) := hSumMaj
      exact Summable.of_norm_bounded (fun p : Prime => ((1 - (2 : ℝ) ^ (-σ))⁻¹ : ℝ) * ((p.1 : ℝ) ^ (-(2 * σ))))
        (by simpa using this.mul_left ((1 - (2 : ℝ) ^ (-σ))⁻¹)) (by intro p; simpa using hMaj w hw p)
    have hmult := (tprod_exp_of_summable (a := fun p : Prime => F p w) hpw_sum).1
    have hexp := (tprod_exp_of_summable (a := fun p : Prime => F p w) hpw_sum).2
    have hterm : ∀ p : Prime, Complex.exp (F p w) = det2EulerFactor w p := by
      intro p
      have hz_ne : (1 - z p w) ≠ 0 := by
        -- deduce from ‖z‖ < 1 as above
        have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast (Nat.Prime.pos p.2)
        have hz : ‖z p w‖ = (p.1 : ℝ) ^ (-w.re) := by
          simpa [z, Complex.norm_eq_abs, ← ofReal_natCast] using Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-w)
        -- Re(w) ≥ σ ⇒ ‖z‖ ≤ p^{-σ} ≤ 2^{-σ} < 1
        have hwre : s.re - δ ≤ w.re := by
          have hdist : ‖w - s‖ < δ := by simpa [U, dist_eq, sub_eq] using hw
          have hre : |w.re - s.re| ≤ ‖w - s‖ := by
            have : |w.re - s.re| = |(w - s).re| := by simp
            simpa [this] using Complex.abs_re_le_abs (w - s)
          have : -(‖w - s‖) ≤ w.re - s.re := by
            have := le_trans (neg_le_abs_self _) hre; simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          linarith
        have hz_le2 : ‖z p w‖ ≤ (2 : ℝ) ^ (-σ) := by
          have : ‖z p w‖ ≤ (p.1 : ℝ) ^ (-σ) := by
            have hmono : -w.re ≤ -σ := by linarith [hwre]
            have := Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) hmono
            simpa [hz]
          have hnonpos : -σ ≤ 0 := le_of_lt (neg_neg_of_pos (lt_trans (by norm_num : (0 : ℝ) < 1/2) hσgt))
          have := Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast (Nat.succ_le_of_lt p.2.one_lt)) hnonpos
          exact le_trans this hnonpos
        have hzlt1 : ‖z p w‖ < 1 :=
          lt_of_le_of_lt hz_le2 (by
            have : (2 : ℝ) ^ (-σ) = 1 / (2 : ℝ) ^ σ := by
              simpa [Real.rpow_neg] using (Real.rpow_neg (by norm_num : (0 : ℝ) < 2) σ)
            have hden_pos : 0 < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
            have hden_gt1 : 1 < (2 : ℝ) ^ σ := by
              have : 1 < (2 : ℝ) := by norm_num
              have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1/2) hσgt
              simpa using Real.one_lt_rpow this hσpos
            have : (1 / (2 : ℝ) ^ σ) < 1 := by
              have := one_lt_inv_iff₀.mpr ⟨ne_of_gt hden_pos, hden_gt1⟩; simpa [one_div] using this
            simpa [this])
        intro h; have : (1 - z p w).re = 0 := by simpa [h]; linarith
      have : Complex.exp (Complex.log (1 - z p w)) = 1 - z p w := Complex.exp_log hz_ne
      simp [F, det2EulerFactor, z, this, mul_comm, mul_left_comm, mul_assoc]
    -- pass products across termwise equality
    have hprod : (∏' p : Prime, Complex.exp (F p w)) = ∏' p : Prime, det2EulerFactor w p := by
      refine tprod_congr ?h
      intro p; simpa using hterm p
    simpa [diagDet2, hprod] using hexp.symm
  -- Conclude: `diagDet2` analytic on U, hence analytic within Ω at s
  have hOnU : AnalyticOn ℂ diagDet2 U := (AnalyticOn.congr hAnalyticExp hEq.symm)
  have hsU : s ∈ U := by simpa [U, dist_self] using hδpos
  exact (hOnU.mono hUsub).analyticWithinAt hsU

end RH.AcademicFramework.DiagonalFredholm
