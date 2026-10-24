import OTSelector.Reconstruction.FinslerRelativeLawGlobalResidualSplice
import OTSelector.Reconstruction.FinslerRelativeLawResidualEnergyBound

/-! The same original marked experiment has a full upper competitor after
splicing retained cell optima with its true-flag hierarchy. The residual energy
keeps its small original mass rate, while bounded completion pays only counts. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))]

/-- The residual pressure budget of the original hierarchy, including its
literal bounded probe. -/
def originalResidualPressureBudget (ξ : Measure (X × Y)) (hξ : ξ ≤ π)
    (n K : ℕ) (probe : X → Y → ℝ) (tilt : ℝ)
    (sample : (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T))) : ℝ :=
  let R := D.refineSubplan ξ hξ
  attributedTypesEnergy (selectedSubplanTags (T := T))
    (fun i ↦ R.sourceSample n i sample) (fun j ↦ R.targetSample n j sample)
    (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
      |tilt| * |probe (sample.1 i).1 (sample.2 j).1|)
    (taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) sample)

/-- The original full type discrepancy, before selecting any matched endpoints. -/
def originalResidualCountBudget (ξ : Measure (X × Y)) (hξ : ξ ≤ π) (n : ℕ)
    (sample : (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T))) : ℝ :=
  let R := D.refineSubplan ξ hξ
  ∑ t : Option (Bool × T),
    |partitionCount (fun i ↦ (R.sourceSample n i sample).1) t -
      partitionCount (fun j ↦ (R.targetSample n j sample).1) t|

/-- Actual original iid counts give the square-root completion budget in the
same residual refinement, independently of subsequent retained matchings. -/
theorem originalResidualCountBudget_expectation
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π) (n : ℕ) :
    let R := D.refineSubplan ξ hξ
    Integrable (D.originalResidualCountBudget ξ hξ n) (R.markedLaw n) ∧
    (∫ sample, D.originalResidualCountBudget ξ hξ n sample ∂R.markedLaw n) ≤
      Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) := by
  let R := D.refineSubplan ξ hξ
  obtain ⟨hP, hL, hx, hy, hxi, hyi, hxl, hyl, hxy⟩ := R.iid_facts hπ n
  let _instP : IsProbabilityMeasure (R.markedLaw n) := hP
  let _instL : IsProbabilityMeasure R.coordinateLaw := hL
  have hm (t : Option (Bool × T)) : MeasurableSet
      {x : Option (Bool × T) × DyadicUnitCube q | x.1 = t} :=
    measurable_fst (measurableSet_singleton t)
  have hmass : (∑ t : Option (Bool × T), R.coordinateLaw.real {x | x.1 = t}) = 1 := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      sum_measureReal_preimage_singleton (μ := R.coordinateLaw) Finset.univ (f := Prod.fst)
        (fun t _ ↦ hm t)
  have h := iidTypeCount_total_difference_bound (R.markedLaw n) R.coordinateLaw R.coordinateLaw
    (R.sourceSample n) (R.targetSample n) hx hy hxi hyi hxl hyl hxy
    (fun t : Option (Bool × T) ↦ {x | x.1 = t}) (fun t ↦ {x | x.1 = t}) hm hm
    (fun _ ↦ rfl) hmass
  have hfun : D.originalResidualCountBudget ξ hξ n = fun sample ↦
      ∑ t : Option (Bool × T), |iidTypeCount (R.sourceSample n) {x | x.1 = t} sample -
        iidTypeCount (R.targetSample n) {x | x.1 = t} sample| := by
    funext sample
    simp only [originalResidualCountBudget, partitionCount_tag_eq_iidTypeCount, R]
  dsimp only
  rw [hfun]
  simpa only [mul_one] using h

/-- One actual hierarchy depth simultaneously gives quantitative original
residual energy and a full original-sample upper competitor after arbitrary
retained CELL matchings are inserted. Only original count/Hall leftovers are
completed using the original physical edge bound. -/
theorem exists_original_global_full_assignment
    {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π)
    (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {G : ℝ} (hG : 0 ≤ G) (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G) :
    let R := D.refineSubplan ξ hξ
    ∃ K : ℕ,
      (∀ tilt : ℝ,
        Integrable (D.originalResidualPressureBudget ξ hξ n K probe tilt) (R.markedLaw n) ∧
        (1 / (n : ℝ)) *
          (∫ sample, D.originalResidualPressureBudget ξ hξ n K probe tilt sample ∂R.markedLaw n) ≤
          D.quadraticConstant * dyadicMatchingConstant q *
            (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (ξ univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * Real.sqrt (2 * Fintype.card T) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (ξ univ).toReal +
          2 * |tilt| * G * (ξ univ).toReal) ∧
      (Integrable (D.originalResidualCountBudget ξ hξ n) (R.markedLaw n) ∧
        (∫ sample, D.originalResidualCountBudget ξ hξ n sample ∂R.markedLaw n) ≤
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T)))) ∧
      ∀ᵐ sample ∂R.markedLaw n, ∀ tilt : ℝ,
      ∀ (sourceCell targetCell : Fin n → Option C),
      (∀ i, sourceCell i = none ↔ (R.sourceSample n i sample).1 ∈ selectedSubplanTags (T := T)) →
      (∀ j, targetCell j = none ↔ (R.targetSample n j sample).1 ∈ selectedSubplanTags (T := T)) →
      ∀ retained : C → OTSelector.PartialMatching n n,
      (∀ c e, e ∈ (retained c).edges → sourceCell e.1 = some c ∧ targetCell e.2 = some c) →
      ∃ full : Assignment n,
        assignmentCost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
          tilt * probe (sample.1 i).1 (sample.2 j).1) full ≤
        (∑ c, (retained c).cost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
          tilt * probe (sample.1 i).1 (sample.2 j).1)) +
        D.originalResidualPressureBudget ξ hξ n K probe tilt sample +
        ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * G) *
          ((Finset.univ.sum (fun c : C ↦ partitionCount sourceCell (some c) - ((retained c).card : ℝ))) +
            D.originalResidualCountBudget ξ hξ n sample) := by
  let R := D.refineSubplan ξ hξ
  obtain ⟨K, hK⟩ := D.fixed_subplan_pressure_recovery hq hn hπ ξ hξ probe hprobe hG hg
  refine ⟨K, hK, D.originalResidualCountBudget_expectation hπ ξ hξ n, ?_⟩
  have hkin := R.iid_cost_bounds hπ n
  have hgOriginal : ∀ᵐ sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)), ∀ i j, |probe (sample.1 i) (sample.2 j)| ≤ G := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) i)
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) j)).ae hg
  have hgMarked := R.types.iid_original_physical_property hπ _ hgOriginal
  filter_upwards [hkin.1, hkin.2, hgMarked] with sample hnonneg hbound hprobeBound
  intro tilt sourceCell targetCell hsourceCell htargetCell retained hretained
  let x := fun i ↦ R.sourceSample n i sample
  let y := fun j ↦ R.targetSample n j sample
  let hierarchy := taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) sample
  have hsat := taggedHierarchy_type_no_opposite x y
    (firstOptimalAssignment_isOptimal (taggedHierarchyCost K x y))
  apply exists_global_assignment_retained_and_selected (selectedSubplanTags (T := T)) x y hierarchy hsat
    sourceCell targetCell hsourceCell htargetCell retained hretained
    (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
      tilt * probe (sample.1 i).1 (sample.2 j).1)
    (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
      |tilt| * |probe (sample.1 i).1 (sample.2 j).1|)
  · intro i j
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hnonneg i j))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · intro i j
    apply add_le_add le_rfl
    calc tilt * probe (sample.1 i).1 (sample.2 j).1 ≤
        |tilt * probe (sample.1 i).1 (sample.2 j).1| := le_abs_self _
      _ = _ := abs_mul _ _
  · exact add_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) D.bound_nonneg)
      (mul_nonneg (abs_nonneg _) hG)
  · intro i j
    have hkinBound := mul_le_mul_of_nonneg_left (hbound i j)
      (Real.rpow_nonneg (Nat.cast_nonneg n) (2 / (q : ℝ)))
    have hprobeMajor : tilt * probe (sample.1 i).1 (sample.2 j).1 ≤ |tilt| * G := by
      calc _ ≤ |tilt * probe (sample.1 i).1 (sample.2 j).1| := le_abs_self _
        _ = |tilt| * |probe (sample.1 i).1 (sample.2 j).1| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hprobeBound i j) (abs_nonneg _)
    exact add_le_add hkinBound hprobeMajor

end OTSelector.Reconstruction.PopulationTypedCostData
