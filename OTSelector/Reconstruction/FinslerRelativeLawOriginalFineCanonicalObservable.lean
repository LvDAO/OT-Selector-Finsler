import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCellDefect
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCanonicalIntegral
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyDyadicComplete
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

namespace PopulationTypedCostData
/-- Every measurable canonical observable, including the literal frozen model
score, has the same old-RN and fine mean. Integrability is equivalent, so the
identity remains independent of compact colors and of any particular budget. -/
theorem rnCellRefinedTypes_canonical_observable_integral
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
    (observable : C → X → X → ℝ)
    (hobservable : ∀ c, Measurable (Function.uncurry (observable c))) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let A := D.refineSubplan η hη
    let oldCost := fun (sample : (Fin n → X × Option (Bool × T)) ×
      (Fin n → X × Option (Bool × T))) ↦ ∑ c, (originalRetainedCellOptimizer a cell
      (originalSubplanPhysicalGraph legal) (fun c sample i j ↦ model c (sample.1 i).1 (sample.2 j).1)
      c sample).cost (fun i j ↦ observable c (sample.1 i).1 (sample.2 j).1)
    let fineCost := fun sample ↦ ∑ c, (PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
        (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
        (originalFinePhysicalGraph legal sample) c)
      (fun i j ↦ model c (sample.1 i).1 (sample.2 j).1)).cost
        (fun i j ↦ observable c (sample.1 i).1 (sample.2 j).1)
    (Integrable fineCost P ↔ Integrable oldCost (A.markedLaw n)) ∧
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
    c sample).cost (fun i j ↦ observable c (sample.1 i).1 (sample.2 j).1)
  have hm := measurable_cellRefinedSubplanObservation (X := X) (Y := X) (C := C) (T := T)
    (I := Fin n) (J := Fin n)
  have hlaw : P.map cellRefinedSubplanObservation = A.markedLaw n :=
    D.types.rnCellRefinedTypes_iid_subplan_law η hη good bad hsplit μ ν
  have hmeas : Measurable oldCost := by
    apply Finset.measurable_sum
    intro c _
    apply measurable_retained_edge_sum
    · intro e
      apply measurableSet_mem_originalRetainedCellOptimizer a ha cell hcell
        (originalSubplanPhysicalGraph legal)
        (fun c S ↦ measurableSet_originalSubplanPhysicalGraph_eq legal hlegal c S)
        (fun c sample i j ↦ model c (sample.1 i).1 (sample.2 j).1) _ c e
      intro c i j
      exact (hmodel c).comp (show Measurable (fun sample :
        (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
          ((sample.1 i).1, (sample.2 j).1)) by fun_prop)
    · intro e
      exact (hobservable c).comp (show Measurable (fun sample :
        (Fin n → X × Option (Bool × T)) × (Fin n → X × Option (Bool × T)) ↦
          ((sample.1 e.1).1, (sample.2 e.2).1)) by fun_prop)
  have hproper := D.rnCellRefinedTypes_iid_some η hη good bad hsplit hπ (I := Fin n) (J := Fin n)
  dsimp only
  have heq : ∀ᵐ sample ∂P,
      (∑ c, (PartialMatching.firstLegalOptimalMatching
        (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
          (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
          (originalFinePhysicalGraph legal sample) c)
        (fun i j ↦ model c (sample.1 i).1 (sample.2 j).1)).cost
          (fun i j ↦ observable c (sample.1 i).1 (sample.2 j).1)) =
      oldCost (cellRefinedSubplanObservation sample) := by
    filter_upwards [hproper] with sample hp
    apply Finset.sum_congr rfl
    intro c _
    rw [original_fine_canonical_eq_subplan_optimizer a cell hdisj legal model sample c hp.1 hp.2]
    rfl
  refine ⟨?_, ?_⟩
  · have hi := integrable_map_measure (μ := P) hmeas.aestronglyMeasurable hm.aemeasurable
    rw [hlaw] at hi
    exact (integrable_congr heq).trans hi.symm
  · rw [integral_congr_ae heq, ← integral_map hm.aemeasurable hmeas.aestronglyMeasurable, hlaw]

end PopulationTypedCostData
end OTSelector.Reconstruction
