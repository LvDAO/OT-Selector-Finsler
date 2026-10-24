import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic
import OTSelector.Analysis.Sobolev.UnitCubeW11
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeSobolevPoincareBootstrap.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeSobolevPoincareBootstrap`; the selected original proof blocks follow. -/
section

/-!
Conditions: Dimension greater than two, the critical reciprocal-exponent identity and a C1 function on the bounded unit cube.

Objects: The critical p=2 Sobolev bootstrap including its lower-order value term and explicit power constant.

Proof detail: Apply the FTC/Loomis–Whitney endpoint estimate to a power of the function, use Hölder to separate the critical factor and cancel its finite norm.

Sources: Terence Tao, Section 1.14, Exercise 1.14.21, pp. 248–249, and Lemma 1.14.9 (Endpoint Sobolev inequality), p. 249 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=257); D. H. Fremlin, Sections 473F–473H, pp. 32–34, especially 473G (iterated Hölder) and 473H (Gagliardo–Nirenberg–Sobolev) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=32); Sheldon Axler, Section 7A, Theorems 7.9–7.10, pp. 196–197; Theorem 7.14, p. 199 (https://measure.axler.net/MIRA.pdf#page=211).
Relation: Bounded-cube bootstrap derived from the endpoint Sobolev method; it is not an identification of arbitrary weak Sobolev representatives.
-/

/-! Genuine critical p=2 bounded-cube Sobolev bootstrap. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction

private instance cubeSobolevVolumeFinite {q : ℕ} :
    IsFiniteMeasure (volume.restrict (Icc (0 : Fin q → ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

private theorem continuous_memLp_unitCube {q : ℕ} {u : (Fin q → ℝ) → ℝ}
    (hu : Continuous u) (p : ℝ≥0∞) : MemLp u p (volume.restrict (Icc (0 : Fin q → ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.continuousOn
  apply MemLp.of_bound hu.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- Actual C1 cube tests satisfy the critical p=2 Sobolev estimate with a lower-order term,
proved by the power bootstrap of the genuine bounded-cube W1,1 inequality. -/
theorem smooth_unit_cube_eLpNorm_critical_le_lintegral_square
    {q : ℕ} (hq : 2 < q) {p : ℝ≥0}
    (hp : (p : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (q : ℝ)⁻¹)
    {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) :
    eLpNorm u p (volume.restrict (Icc (0 : Fin q → ℝ) 1)) ≤
      (∫⁻ x in Icc (0 : Fin q → ℝ) 1,
        (‖u x‖ₑ + ENNReal.ofReal (2 * ((q : ℝ) - 1) / ((q : ℝ) - 2)) *
          ‖fderiv ℝ u x‖ₑ)^2) ^ (1 / (2 : ℝ)) := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (Icc 0 1)
  have hqR : (2 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < (q : ℝ) - 2 := by linarith
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz] at hp
    have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num) hqR
    norm_num only [NNReal.coe_zero, inv_zero, one_div] at hp h
    linarith
  let n' := NNReal.conjExponent q
  have hn : NNReal.HolderConjugate (q : ℝ≥0) n' := .conjExponent (by exact_mod_cast (show 1 < q by omega))
  let γ : ℝ≥0 := .mk (2 * ((q : ℝ) - 1) / ((q : ℝ) - 2)) (by positivity)
  have hγ : (γ : ℝ) = 2 * ((q : ℝ) - 1) / ((q : ℝ) - 2) := rfl
  have hγ1 : 1 < (γ : ℝ) := by rw [hγ]; apply (one_lt_div hq2).mpr; linarith
  have hγn : γ * n' = p := by
    rw [← NNReal.coe_inj, ← inv_inj, hp, NNReal.coe_mul, hγ, hn.coe.conjugate_eq]
    simp [field]
  have hγ2 : ((γ : ℝ) - 1) * 2 = p := by
    rw [← inv_inj, hp, hγ]
    field_simp [hq0.ne', hq2.ne']
    rw [show 2 * ((q : ℝ) - 1) - ((q : ℝ) - 2) = q by ring]
    exact div_self hq0.ne'
  have hexp : 1 / (n' : ℝ) - 1 / (2 : ℝ) = 1 / (p : ℝ) := by
    simp only [one_div]
    rw [← hn.coe.one_sub_inv, hp]
    push_cast
    ring
  by_cases hA0 : (∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂μ) = 0
  · rw [eLpNorm_nnreal_eq_lintegral hp0, hA0, ENNReal.zero_rpow_of_pos] <;> positivity
  have hAfin : (∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂μ) ≠ ∞ := by
    refine lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
      ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp0) ?_ |>.ne
    rw [← eLpNorm_nnreal_eq_eLpNorm' hp0]
    exact (continuous_memLp_unitCube hu.continuous p).eLpNorm_lt_top
  have hhalf0 : (∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hA0) hAfin).ne'
  have hhalffin : (∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≠ ∞ := by finiteness
  let v : (Fin q → ℝ) → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ)
  have hv : ContDiff ℝ 1 v := hu.norm_rpow hγ1
  have hboot :
      (∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (n' : ℝ)) ≤
        (∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫⁻ x, (‖u x‖ₑ + (γ : ℝ≥0∞) * ‖fderiv ℝ u x‖ₑ)^2 ∂μ) ^ (1 / (2 : ℝ)) := by
    calc
      _ = eLpNorm v n' μ := by
        rw [← hγn, eLpNorm_nnreal_eq_lintegral hn.symm.pos.ne']
        simp (discharger := positivity) [v, Real.enorm_rpow_of_nonneg, ENNReal.rpow_mul]
      _ ≤ ∫⁻ x, ‖v x‖ₑ + ‖fderiv ℝ v x‖ₑ ∂μ :=
        smooth_unit_cube_eLpNorm_le_lintegral_add_fderiv hn hv
      _ ≤ ∫⁻ x, ‖u x‖ₑ ^ ((γ : ℝ) - 1) *
          (‖u x‖ₑ + (γ : ℝ≥0∞) * ‖fderiv ℝ u x‖ₑ) ∂μ := by
        apply lintegral_mono
        intro x
        have hpow : ‖u x‖ₑ ^ (γ : ℝ) = ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖u x‖ₑ := by
          calc
            _ = ‖u x‖ₑ ^ (((γ : ℝ) - 1) + 1) := by congr 1; ring
            _ = ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖u x‖ₑ ^ (1 : ℝ) :=
              ENNReal.rpow_add_of_nonneg ((γ : ℝ) - 1) 1 (by linarith) (by norm_num)
            _ = _ := by rw [ENNReal.rpow_one]
        have hd := enorm_fderiv_norm_rpow_le (x := x) (hu.differentiable one_ne_zero)
          (show (1 : ℝ≥0) < γ by exact_mod_cast hγ1)
        calc
          _ ≤ ‖u x‖ₑ ^ (γ : ℝ) + (γ : ℝ≥0∞) * ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖ₑ := by
            apply add_le_add
            · simp [v, Real.enorm_rpow_of_nonneg]
            · exact hd
          _ = _ := by rw [hpow]; ring
      _ ≤ _ := by
        have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
          (f := fun x ↦ ‖u x‖ₑ ^ ((γ : ℝ) - 1))
          (g := fun x ↦ ‖u x‖ₑ + (γ : ℝ≥0∞) * ‖fderiv ℝ u x‖ₑ)
          (show Real.HolderConjugate 2 2 by rw [Real.holderConjugate_iff]; norm_num)
          ((hu.continuous.measurable.enorm.pow_const ((γ : ℝ) - 1)).aemeasurable (μ := μ))
          ((hu.continuous.measurable.enorm.add
              (measurable_const.mul (hu.continuous_fderiv (by norm_num)).measurable.enorm)).aemeasurable (μ := μ))
        have hpower (x : Fin q → ℝ) :
            (‖u x‖ₑ ^ ((γ : ℝ) - 1)) ^ (2 : ℝ) = ‖u x‖ₑ ^ (p : ℝ) := by
          rw [← ENNReal.rpow_mul, hγ2]
        simp only [Pi.mul_apply, hpower] at hh
        simpa only [ENNReal.rpow_two] using hh
  change eLpNorm u p μ ≤ _
  rw [eLpNorm_nnreal_eq_lintegral hp0]
  have hcancel : (∫⁻ x, ‖u x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) ≤
      (∫⁻ x, (‖u x‖ₑ + (γ : ℝ≥0∞) * ‖fderiv ℝ u x‖ₑ)^2 ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [← hexp, ENNReal.rpow_sub _ _ hA0 hAfin, ENNReal.div_le_iff hhalf0 hhalffin]
    simpa only [mul_comm] using hboot
  have hγcoe : (γ : ℝ≥0∞) = ENNReal.ofReal (2 * ((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
    rw [← hγ, ENNReal.ofReal_coe_nnreal]
  simpa only [hγcoe, μ] using hcancel

end OTSelector.Reconstruction

end
end
