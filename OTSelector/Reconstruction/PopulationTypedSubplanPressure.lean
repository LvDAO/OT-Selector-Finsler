import OTSelector.Reconstruction.PopulationTypedSubplanEnergy

/-!
# Original subplan recovery including the bounded probe

The full marked competitor has the small-mass distance estimate and a probe
correction linear in the original prescribed mass. Both use the same assignment.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)

/-- A single full original-sample assignment supplies the paper's fixed-subplan
recovery estimate for every tilt, including all count-completion edges. -/
theorem fixed_subplan_pressure_recovery {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π)
    (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {G : ℝ} (hG : 0 ≤ G) (hg : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ G) :
    let R := D.refineSubplan η hη
    ∃ K : ℕ, ∀ τ : ℝ,
      Integrable (fun ω ↦ attributedTypesEnergy (selectedSubplanTags (T := T))
        (fun i ↦ R.sourceSample n i ω) (fun i ↦ R.targetSample n i ω)
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i).1 (ω.2 j).1 +
          |τ| * |probe (ω.1 i).1 (ω.2 j).1|)
        (taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) ω))
        (R.markedLaw n) ∧
      (1 / (n : ℝ)) * (∫ ω, attributedTypesEnergy (selectedSubplanTags (T := T))
        (fun i ↦ R.sourceSample n i ω) (fun i ↦ R.targetSample n i ω)
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (ω.1 i).1 (ω.2 j).1 +
          |τ| * |probe (ω.1 i).1 (ω.2 j).1|)
        (taggedHierarchyAssignment K (R.sourceSample n) (R.targetSample n) ω)
        ∂R.markedLaw n) ≤
        D.quadraticConstant * dyadicMatchingConstant q *
          (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
          (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * Real.sqrt (2 * Fintype.card T) *
          (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal +
        2 * |τ| * G * (η univ).toReal := by
  let R := D.refineSubplan η hη
  obtain ⟨hP, hL, hx, hy, hxi, hyi, hxl, hyl, hxy⟩ := R.iid_facts hπ n
  let : IsProbabilityMeasure (R.markedLaw n) := hP
  let : IsProbabilityMeasure R.coordinateLaw := hL
  have hcm (i j : Fin n) : Measurable
      (fun ω : (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        cost (ω.1 i).1 (ω.2 j).1) :=
    D.measurable_cost.comp (show Measurable (fun ω :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        ((ω.1 i).1, (ω.2 j).1)) from by fun_prop)
  have hgm (i j : Fin n) : Measurable
      (fun ω : (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        probe (ω.1 i).1 (ω.2 j).1) :=
    hprobe.comp (show Measurable (fun ω :
      (Fin n → X × Option (Bool × T)) × (Fin n → Y × Option (Bool × T)) ↦
        ((ω.1 i).1, (ω.2 j).1)) from by fun_prop)
  have hgOriginal : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)), ∀ i j, |probe (ω.1 i) (ω.2 j)| ≤ G := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ μ) i)
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) j)).ae hg
  have hgMarked := R.types.iid_original_physical_property hπ _ hgOriginal
  have hb := R.iid_cost_bounds hπ n
  obtain ⟨K, hK⟩ := exists_taggedHierarchy_smallMass_pressure_recovery hq hn
    (R.markedLaw n) R.coordinateLaw (R.sourceSample n) (R.targetSample n)
    hx hy hxi hyi hxl hyl hxy (fun ω i j ↦ cost (ω.1 i).1 (ω.2 j).1)
    (fun ω i j ↦ probe (ω.1 i).1 (ω.2 j).1) hcm hgm
    R.quadratic_nonneg R.bound_nonneg hG hb.1 hb.2 hgMarked (R.iid_quadratic hπ n)
  refine ⟨K, fun τ ↦ ?_⟩
  have h := hK (selectedSubplanTags (T := T)) τ
  rw [card_selectedSubplanTags, D.refineSubplan_selected_coordinate_mass η hη] at h
  exact h

end OTSelector.Reconstruction.PopulationTypedCostData
