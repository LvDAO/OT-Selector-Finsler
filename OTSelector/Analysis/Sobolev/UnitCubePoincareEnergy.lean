import OTSelector.Analysis.Normed.CoordinateCovectorBound
import OTSelector.Analysis.Sobolev.SmoothBoxPoincare
import OTSelector.Analysis.Sobolev.UnitCubeCriticalBootstrap
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeSobolevPoincareEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeSobolevPoincareEnergy`; the selected original proof blocks follow. -/
section

/-!
Conditions: Dimension greater than two and a mean-zero C1 function on the unit cube.

Objects: Critical Sobolev–Poincaré bound by the square root of actual coordinate L2 energy.

Proof detail: Combine the critical bootstrap with the cube Poincaré estimate, control the derivative norm by its coordinate square sum and collect the explicit constant.

Sources: Terence Tao, Section 1.14, Exercise 1.14.21, pp. 248–249, and Lemma 1.14.9 (Endpoint Sobolev inequality), p. 249 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=257); D. H. Fremlin, Sections 473F–473H, pp. 32–34, especially 473G (iterated Hölder) and 473H (Gagliardo–Nirenberg–Sobolev) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=32); Rick Durrett, Section 1.6.3, variance identities (1.6.2)–(1.6.4), p. 33; Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=41).
Relation: Derived explicit bounded-cube inequality; it does not assert an optimal embedding constant.
-/

/-! Actual critical cube Sobolev-Poincare from original coordinate derivative L2 energy. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction

/-- A fixed dimension-dependent constant for the genuine unit-cube critical Sobolev bound. -/
def cubeSobolevPoincareConstant (q : ℕ) : ℝ :=
  Real.sqrt ((q : ℝ) + 2 * (2 * ((q : ℝ) - 1) / ((q : ℝ) - 2))^2 *
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖^2)

/-- The actual constant is nonnegative. -/
theorem cubeSobolevPoincareConstant_nonneg (q : ℕ) : 0 ≤ cubeSobolevPoincareConstant q :=
  Real.sqrt_nonneg _

/-- The actual critical Sobolev-Poincare inequality on the unit cube. Only genuine C1
regularity and zero cube mean are inputs; every derivative energy is in an original coordinate. -/
theorem smooth_unit_cube_eLpNorm_critical_le_sqrt_coordinate_energy
    {q : ℕ} (hq : 2 < q) {p : ℝ≥0}
    (hp : (p : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (q : ℝ)⁻¹)
    {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hmean : (∫ x in Icc (0 : Fin q → ℝ) 1, u x) = 0) :
    eLpNorm u p (volume.restrict (Icc (0 : Fin q → ℝ) 1)) ≤
      ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt
        (∑ k : Fin q, ∫ x in Icc (0 : Fin q → ℝ) 1,
          (fderiv ℝ u x (Pi.single k 1))^2)) := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (Icc 0 1)
  let γ : ℝ := 2 * ((q : ℝ) - 1) / ((q : ℝ) - 2)
  let α : ℝ := ‖(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap‖
  let E : ℝ := ∑ k : Fin q, ∫ x, (fderiv ℝ u x (Pi.single k 1))^2 ∂μ
  have hqR : (2 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < (q : ℝ) - 2 := by linarith
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hα : 0 ≤ α := norm_nonneg _
  have hE : 0 ≤ E := Finset.sum_nonneg (fun k _ ↦ integral_nonneg (fun x ↦ sq_nonneg _))
  have hD : Continuous (fun x ↦ ‖fderiv ℝ u x‖) := (hu.continuous_fderiv (by norm_num)).norm
  have hDi : Integrable (fun x ↦ ‖fderiv ℝ u x‖^2) μ := (hD.pow 2).continuousOn.integrableOn_Icc
  have hi (k : Fin q) : Integrable (fun x ↦ (fderiv ℝ u x (Pi.single k 1))^2) μ :=
    (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).continuousOn.integrableOn_Icc
  have hsum : Integrable (fun x ↦ α^2 * ∑ k : Fin q, (fderiv ℝ u x (Pi.single k 1))^2) μ :=
    (integrable_finsetSum Finset.univ (fun k _ ↦ hi k)).const_mul _
  have hDe : (∫ x, ‖fderiv ℝ u x‖^2 ∂μ) ≤ α^2 * E := by
    have hh := integral_mono hDi hsum (fun x ↦ raw_covector_norm_sq_le_coord_sum (fderiv ℝ u x))
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ ↦ hi k)] at hh
    exact hh
  have hP := smooth_box_poincare_sq_of_mean_zero (a := (0 : Fin q → ℝ)) (b := 1)
    (fun _ ↦ zero_lt_one) hu hmean
  simp only [Pi.zero_apply, Pi.one_apply, sub_zero, one_pow, one_mul] at hP
  have hHi : Integrable (fun x ↦ (‖u x‖ + γ * ‖fderiv ℝ u x‖)^2) μ :=
    ((hu.continuous.norm.add (hD.const_mul γ)).pow 2).continuousOn.integrableOn_Icc
  have hUi : Integrable (fun x ↦ (u x)^2) μ := (hu.continuous.pow 2).continuousOn.integrableOn_Icc
  have hupper : (∫ x, (‖u x‖ + γ * ‖fderiv ℝ u x‖)^2 ∂μ) ≤
      ((q : ℝ) + 2 * γ^2 * α^2) * E := by
    have hh := integral_mono hHi
      ((hUi.const_mul 2).add (hDi.const_mul (2 * γ^2))) (fun x ↦ by
        change (‖u x‖ + γ * ‖fderiv ℝ u x‖)^2 ≤
          2 * (u x)^2 + (2 * γ^2) * ‖fderiv ℝ u x‖^2
        have hn := sq_nonneg (‖u x‖ - γ * ‖fderiv ℝ u x‖)
        simp only [Real.norm_eq_abs] at hn ⊢
        nlinarith [sq_abs (u x)])
    simp only [Pi.add_apply] at hh
    rw [integral_add (hUi.const_mul 2) (hDi.const_mul (2 * γ^2)),
      integral_const_mul, integral_const_mul] at hh
    calc
      _ ≤ 2 * (∫ x, (u x)^2 ∂μ) + (2 * γ^2) * ∫ x, ‖fderiv ℝ u x‖^2 ∂μ := hh
      _ ≤ (q : ℝ) * E + (2 * γ^2) * (α^2 * E) :=
        add_le_add hP (mul_le_mul_of_nonneg_left hDe (by positivity))
      _ = _ := by ring
  have hC : 0 ≤ (q : ℝ) + 2 * γ^2 * α^2 := by positivity
  have hident : (∫⁻ x, (‖u x‖ₑ + ENNReal.ofReal γ * ‖fderiv ℝ u x‖ₑ)^2 ∂μ) =
      ENNReal.ofReal (∫ x, (‖u x‖ + γ * ‖fderiv ℝ u x‖)^2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hHi (ae_of_all _ (fun _ ↦ sq_nonneg _))]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (by positivity) 2, ENNReal.ofReal_add (norm_nonneg _) (by positivity),
      ENNReal.ofReal_mul hγ, ofReal_norm, ofReal_norm]
  calc
    _ ≤ (∫⁻ x, (‖u x‖ₑ + ENNReal.ofReal γ * ‖fderiv ℝ u x‖ₑ)^2 ∂μ) ^ (1 / (2 : ℝ)) :=
      smooth_unit_cube_eLpNorm_critical_le_lintegral_square hq hp hu
    _ = ENNReal.ofReal (∫ x, (‖u x‖ + γ * ‖fderiv ℝ u x‖)^2 ∂μ) ^ (1 / (2 : ℝ)) := by rw [hident]
    _ ≤ ENNReal.ofReal (((q : ℝ) + 2 * γ^2 * α^2) * E) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hupper) (by norm_num)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC hE) (by norm_num),
        ← Real.sqrt_eq_rpow, Real.sqrt_mul hC]
      rfl

/-- The genuine unit-cube Sobolev-Poincare estimate with the literal critical exponent
2q/(q-2), an actual dimension-only constant and the original coordinate derivative energy. -/
theorem smooth_unit_cube_sobolev_poincare
    {q : ℕ} (hq : 2 < q) {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hmean : (∫ x in Icc (0 : Fin q → ℝ) 1, u x) = 0) :
    eLpNorm u (ENNReal.ofReal (2 * (q : ℝ) / ((q : ℝ) - 2)))
      (volume.restrict (Icc (0 : Fin q → ℝ) 1)) ≤
      ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt
        (∑ k : Fin q, ∫ x in Icc (0 : Fin q → ℝ) 1,
          (fderiv ℝ u x (Pi.single k 1))^2)) := by
  apply smooth_unit_cube_eLpNorm_critical_le_sqrt_coordinate_energy hq (p :=
    Real.toNNReal (2 * (q : ℝ) / ((q : ℝ) - 2))) ?_ hu hmean
  have hqr : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_trans (by norm_num) hqr
  have hden : (0 : ℝ) < (q : ℝ) - 2 := sub_pos.mpr hqr
  rw [Real.coe_toNNReal _ (le_of_lt (div_pos (mul_pos (by norm_num) hqpos) hden))]
  field_simp [ne_of_gt hqpos, ne_of_gt hden]

end OTSelector.Reconstruction

end
end
