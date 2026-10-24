import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellwiseCutoff
import OTSelector.Reconstruction.FinslerRelativeLawResidualEnergyBound

/-! Original per-cell label losses feed one original typed residual energy. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false

/-- One prescribed union of original cell cutoffs supplies the actual
original-iid full residual competitor with the original atlas constant once.
Its mass parameter is the base residual plus the original removed label masses. -/
theorem original_cellwise_cutoff_full_competitor
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype C] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (hwhole : Vlasov.IsCoupling (χ + ξ) μ ν)
    (a : X → Z) (ha : Measurable a) (cell cutoff : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c)) (hcutoff : ∀ c, MeasurableSet (cutoff c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsupport : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c)
    {n : ℕ} (hq : 4 < q) (hn : 0 < n) :
    let G := ⋃ c, cell c ∩ cutoff c
    let hG := MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff c)
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let β := (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff c)
    let R := D.refineSubplan η hη
    ∃ K : ℕ,
      (∀ i : Fin n, Measurable (fun sample ↦
        taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) sample i)) ∧
      Integrable (D.subplanAttributedEnergy η hη n K) (R.markedLaw n) ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ sample, D.subplanAttributedEnergy η hη n K sample ∂R.markedLaw n) ≤
        D.quadraticConstant * dyadicMatchingConstant q *
          (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * β ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * Real.sqrt (2 * Fintype.card T) *
          (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt β := by
  let G := ⋃ c, cell c ∩ cutoff c
  have hG : MeasurableSet G := MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff c)
  let η := restrictOriginalRetainedResidual χ ξ a G
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
  let β := (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff c)
  have hβ : 0 ≤ β := add_nonneg ENNReal.toReal_nonneg
    (Finset.sum_nonneg fun c _ ↦ measureReal_nonneg)
  have hmassReal : (η univ).toReal ≤ β :=
    original_cellwise_cutoff_residual_real_mass_le χ ξ μ ν hwhole a ha
      cell cutoff hcell hcutoff hdisj hsupport
  have hmass : η univ ≤ ENNReal.ofReal β := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top η univ) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hβ] using hmassReal
  exact D.fixed_subplan_full_competitor_of_mass_bound hq hn hwhole η hη β hβ hmass

/-- The actual full residual cost, including the bounded original probe loss,
is controlled by the same once-counted original label-loss parameter. -/
theorem original_cellwise_cutoff_repair_budget_le
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (hwhole : Vlasov.IsCoupling (χ + ξ) μ ν)
    (a : X → Z) (ha : Measurable a) (cell cutoff : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c)) (hcutoff : ∀ c, MeasurableSet (cutoff c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsupport : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c)
    (hq : 4 < q) (n : ℕ) (tilt probeBound : ℝ) (hprobeBound : 0 ≤ probeBound) :
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ cutoff c)
    let β := (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff c)
    D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal +
      2 * |tilt| * probeBound * (η univ).toReal ≤
    D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * β ^ (1 - 2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt β +
      2 * |tilt| * probeBound * β := by
  have hm := original_cellwise_cutoff_residual_real_mass_le χ ξ μ ν hwhole a ha
    cell cutoff hcell hcutoff hdisj hsupport
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have htwo : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
  have hexp : 0 ≤ 1 - 2 / (q : ℝ) := sub_nonneg.mpr ((div_le_one hqpos).mpr htwo)
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ENNReal.toReal_nonneg hm hexp)
        (mul_nonneg (mul_nonneg D.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm)
        (mul_nonneg (mul_nonneg D.bound_nonneg (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · exact mul_le_mul_of_nonneg_left hm
      (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) hprobeBound)

end OTSelector.Reconstruction.PopulationTypedCostData
