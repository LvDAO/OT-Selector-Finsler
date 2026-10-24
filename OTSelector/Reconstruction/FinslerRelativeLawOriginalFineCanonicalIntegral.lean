import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCellDefect
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCanonicalObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineAssignmentIntegral
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineFullRetention

/-! Canonical retained costs have the exact original RN-flag expectation on the same fine experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false

/-- The original endpoint relation gives finite graph events on the coarse
original residual/retained experiment directly. -/
theorem measurableSet_originalSubplanPhysicalGraph_eq
    {X C T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] {n : ℕ}
    (legal : C → X → X → Prop)
    (hlegal : ∀ c, MeasurableSet {p : X × X | legal c p.1 p.2})
    (c : C) (S : Finset (Fin n × Fin n)) :
    MeasurableSet {sample | originalSubplanPhysicalGraph (T := T) legal c sample = S} := by
  have hm : Measurable (originalSubplanPhysicalGraph (T := T) (n := n) legal c) := by
    apply measurable_finset_iff.mpr
    intro e
    apply measurableSet_setOfPred.mp
    have heq : {sample | e ∈ originalSubplanPhysicalGraph (T := T) (n := n) legal c sample} =
        {sample | legal c (sample.1 e.1).1 (sample.2 e.2).1} := by
      ext sample
      simp only [originalSubplanPhysicalGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact (hlegal c).preimage (show Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
        ((sample.1 e.1).1, (sample.2 e.2).1)) by fun_prop)
  exact (measurableSet_singleton S).preimage hm

namespace PopulationTypedCostData
/-- The literal fine canonical retained cost and the old original RN-flag
canonical cost have exactly equal means. Both integrabilities, complete mark
coverage and the first-optimizer identity are derived from the actual data. -/
theorem rnCellRefinedTypes_canonical_integral_eq_original
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    {π : Measure (X × X)} [IsFiniteMeasure π]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × X)) (hη : η ≤ π)
    (good : T → Measure (X × X)) (bad : C → T → Measure (X × X))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ)
    (a : X → Z) (ha : Measurable a) (cell : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c)) (hdisj : Pairwise (Disjoint on cell))
    (legal : C → X → X → Prop)
    (hlegal : ∀ c, MeasurableSet {p : X × X | legal c p.1 p.2})
    (model : C → X → X → ℝ) (hmodel : ∀ c, Measurable (Function.uncurry (model c)))
    (probe : X → X → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) (tilt : ℝ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let A := D.refineSubplan η hη
    let oldCost := fun (sample : (Fin n → X × Option (Bool × T)) ×
      (Fin n → X × Option (Bool × T))) ↦ ∑ c, (originalRetainedCellOptimizer a cell
      (originalSubplanPhysicalGraph legal) (fun c sample i j ↦ model c (sample.1 i).1 (sample.2 j).1)
      c sample).cost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
        cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1)
    let fineCost := fun sample ↦ ∑ c, (PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
        (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
        (originalFinePhysicalGraph legal sample) c)
      (fun i j ↦ model c (sample.1 i).1 (sample.2 j).1)).cost
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
          tilt * probe (sample.1 i).1 (sample.2 j).1)
    Integrable oldCost (A.markedLaw n) ∧ Integrable fineCost P ∧
      (∫ sample, fineCost sample ∂P) = ∫ sample, oldCost sample ∂A.markedLaw n := by
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let A := D.refineSubplan η hη
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  let oldCost := fun (sample : (Fin n → X × Option (Bool × T)) ×
      (Fin n → X × Option (Bool × T))) ↦ ∑ c, (originalRetainedCellOptimizer a cell
    (originalSubplanPhysicalGraph legal) (fun c sample i j ↦ model c (sample.1 i).1 (sample.2 j).1)
    c sample).cost (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1)
  have hm := measurable_cellRefinedSubplanObservation (X := X) (Y := X) (C := C) (T := T)
    (I := Fin n) (J := Fin n)
  have hlaw : P.map cellRefinedSubplanObservation = A.markedLaw n :=
    D.types.rnCellRefinedTypes_iid_subplan_law η hη good bad hsplit μ ν
  have hedge := D.original_marked_tilted_edge_integrable hπ η hη n probe hprobe hb tilt
  have hi : Integrable oldCost (A.markedLaw n) := by
    apply integrable_finsetSum
    intro c _
    apply OTSelector.PartialMatching.integrable_sample_cost_of_edge_events _ _ _ _ hedge
    intro e
    apply measurableSet_mem_originalRetainedCellOptimizer a ha cell hcell
      (originalSubplanPhysicalGraph legal) (fun c S ↦ measurableSet_originalSubplanPhysicalGraph_eq legal hlegal c S)
      (fun c sample i j ↦ model c (sample.1 i).1 (sample.2 j).1) _ c e
    intro c i j
    exact (hmodel c).comp (show Measurable (fun sample :
      (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
        ((sample.1 i).1, (sample.2 j).1)) by fun_prop)
  have hmapI : Integrable oldCost (P.map cellRefinedSubplanObservation) := by rwa [hlaw]
  have hcompI := hmapI.comp_measurable hm
  have hproper := D.rnCellRefinedTypes_iid_some η hη good bad hsplit hπ (I := Fin n) (J := Fin n)
  dsimp only
  have heq : ∀ᵐ sample ∂P,
      (∑ c, (PartialMatching.firstLegalOptimalMatching
        (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
          (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
          (originalFinePhysicalGraph legal sample) c)
        (fun i j ↦ model c (sample.1 i).1 (sample.2 j).1)).cost
          (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
            tilt * probe (sample.1 i).1 (sample.2 j).1)) =
      oldCost (cellRefinedSubplanObservation sample) := by
    filter_upwards [hproper] with sample hp
    apply Finset.sum_congr rfl
    intro c _
    rw [original_fine_canonical_eq_subplan_optimizer a cell hdisj legal model sample c hp.1 hp.2]
    rfl
  refine ⟨hi, hcompI.congr (heq.mono fun _ h ↦ h.symm), ?_⟩
  rw [integral_congr_ae heq, ← integral_map hm.aemeasurable hmapI.aestronglyMeasurable, hlaw]

end PopulationTypedCostData
end OTSelector.Reconstruction
