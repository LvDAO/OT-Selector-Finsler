import OTSelector.Reconstruction.FinslerRelativeLawUniformPopulationEnergy

/-!
Actual deterministic original residual mass bounds feed the original iid full
competitor estimate. The repair cost depends on the original residual mass,
with the kinetic constants supplied uniformly by the whole-pair geometry.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- The rebuilt residual charges the literal original discarded label mass in
real units, without a sample-size-dependent kernel bound. -/
theorem original_residual_mass_le_ofReal_add_label_complement
    {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (r : Measure Z) [IsFiniteMeasure r] (G : Set Z) (ξ : Measure W)
    (B : ℝ) (hB : 0 ≤ B) (hmass : ξ univ ≤ ENNReal.ofReal B + r Gᶜ) :
    ξ univ ≤ ENNReal.ofReal (B + r.real Gᶜ) := by
  rw [ENNReal.ofReal_add hB measureReal_nonneg, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top r Gᶜ)]
  exact hmass

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)

/-- An actual deterministic original subplan with raw mass at most `β` has
quantitative original-iid repair energy in terms of `β`. The full tagged
assignment is constructed by the original population theorem. -/
theorem fixed_subplan_full_competitor_of_mass_bound
    {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π)
    (β : ℝ) (hβ : 0 ≤ β) (hmass : ξ univ ≤ ENNReal.ofReal β) :
    let R := D.refineSubplan ξ hξ
    ∃ K : ℕ,
      (∀ i : Fin n, Measurable (fun sample ↦
        taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) sample i)) ∧
      Integrable (D.subplanAttributedEnergy ξ hξ n K) (R.markedLaw n) ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ sample, D.subplanAttributedEnergy ξ hξ n K sample ∂R.markedLaw n) ≤
        D.quadraticConstant * dyadicMatchingConstant q *
          (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * β ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * Real.sqrt (2 * Fintype.card T) *
          (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt β := by
  let _instResidualFinite : IsFiniteMeasure ξ := isFiniteMeasure_of_le π hξ
  have hm : (ξ univ).toReal ≤ β := by
    have h := (ENNReal.toReal_le_toReal (measure_ne_top ξ univ) ENNReal.ofReal_ne_top).mpr hmass
    simpa only [ENNReal.toReal_ofReal hβ] using h
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hqpos : 0 < (q : ℝ) := by linarith
  have hp : 0 ≤ 1 - 2 / (q : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hqpos).mpr
    linarith
  obtain ⟨K, hmeas, _, hsmall⟩ := D.fixed_subplan_full_competitor hq hn hπ ξ hξ
  refine ⟨K, hmeas, hsmall.1, hsmall.2.trans ?_⟩
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ENNReal.toReal_nonneg hm hp)
    exact mul_nonneg (mul_nonneg D.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
      (Real.rpow_nonneg (by positivity) _)
  · apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm)
    exact mul_nonneg (mul_nonneg D.bound_nonneg (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (by positivity) _)

end OTSelector.Reconstruction.PopulationTypedCostData
