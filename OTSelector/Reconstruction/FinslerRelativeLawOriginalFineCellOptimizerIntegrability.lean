import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalCellDefect
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineAssignmentIntegral
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags

/-! Actual fine canonical cell optimizers have measurable edges and integrable original costs. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- Fine physical cell events are measurable directly from the original label and mark. -/
theorem measurableSet_fineOriginalRetainedCellTag_eq_some
    {Ω X Z C T : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (a : X → Z) (ha : Measurable a) (cell : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c)) (hdisj : Pairwise (Disjoint on cell))
    (p : Ω → X × Option (CellRefinedType C T)) (hp : Measurable p) (c : C) :
    MeasurableSet {ω | fineOriginalRetainedCellTag a cell (p ω) = some c} := by
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  exact measurableSet_originalRetainedCellTag_eq_some a ha cell hcell hdisj
    (PopulationTypedCostData.selectedSubplanTags (T := T))
    (fun ω ↦ ((p ω).1, (p ω).2.map cellRefinedSubplanType))
    (hp.fst.prodMk ((measurable_of_countable (Option.map cellRefinedSubplanType)).comp hp.snd)) c

/-- Filtering to actual measurable physical cells preserves finite graph measurability. -/
theorem measurableSet_originalAmbientCellLegalGraph_eq
    {Ω C : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (sourceCell : Ω → Fin m → Option C) (targetCell : Ω → Fin n → Option C)
    (hs : ∀ i c, MeasurableSet {ω | sourceCell ω i = some c})
    (ht : ∀ j c, MeasurableSet {ω | targetCell ω j = some c})
    (allowed : Ω → C → Finset (Fin m × Fin n))
    (hallowed : ∀ c S, MeasurableSet {ω | allowed ω c = S})
    (c : C) (S : Finset (Fin m × Fin n)) :
    MeasurableSet {ω | originalAmbientCellLegalGraph
      (sourceCell ω) (targetCell ω) (allowed ω) c = S} := by
  classical
  have hallowed' : Measurable (fun ω ↦ allowed ω c) := by
    apply measurable_to_countable'
    exact hallowed c
  have hm : Measurable (fun ω ↦ originalAmbientCellLegalGraph
      (sourceCell ω) (targetCell ω) (allowed ω) c) := by
    apply measurable_finset_iff.mpr
    intro e
    apply measurableSet_setOfPred.mp
    have heq : {ω | e ∈ originalAmbientCellLegalGraph
        (sourceCell ω) (targetCell ω) (allowed ω) c} =
        {ω | e ∈ allowed ω c} ∩ ({ω | sourceCell ω e.1 = some c} ∩
          {ω | targetCell ω e.2 = some c}) := by
      ext ω
      simp only [originalAmbientCellLegalGraph, Finset.mem_filter, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
    rw [heq]
    exact ((measurableSet_mem_finset e).preimage hallowed').inter ((hs e.1 c).inter (ht e.2 c))
  exact (measurableSet_singleton S).preimage hm

namespace PopulationTypedCostData
variable {X Y Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- The literal canonical retained-cell physical cost sum is integrable on the
same fine experiment. The original finite edge law supplies every cost bound;
only the actual finite graph and model-score measurability metadata are used. -/
theorem rnCellRefinedTypes_canonical_cell_cost_integrable
    (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ)
    (left : X → Z) (right : Y → Z) (hleft : Measurable left) (hright : Measurable right)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (allowed : ((Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) → C → Finset (Fin n × Fin n))
    (hallowed : ∀ c S, MeasurableSet {sample | allowed sample c = S})
    (modelScore : ((Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) → C → Fin n → Fin n → ℝ)
    (hmodelScore : ∀ c i j, Measurable (fun sample ↦ modelScore sample c i j))
    (probe : X → Y → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) (tilt : ℝ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let canonical := fun sample c ↦ PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag left cell (sample.1 i))
        (fun j ↦ fineOriginalRetainedCellTag right cell (sample.2 j)) (allowed sample) c)
      (modelScore sample c)
    Integrable (fun sample ↦ ∑ c, (canonical sample c).cost (fun i j ↦
      (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i).1 (sample.2 j).1 +
        tilt * probe (sample.1 i).1 (sample.2 j).1)) P := by
  have hedge := D.rnCellRefinedTypes_original_tilted_edge_integrable η hη good bad hsplit
    hπ n probe hprobe hb tilt
  dsimp only
  apply integrable_finsetSum
  intro c _
  apply OTSelector.PartialMatching.integrable_sample_cost_of_edge_events _ _ _ _ hedge
  intro e
  apply PartialMatching.measurableSet_mem_firstLegalOptimalMatching _ _ _ (hmodelScore c) e
  intro S
  apply measurableSet_originalAmbientCellLegalGraph_eq _ _ _ _ allowed hallowed c S
  · intro i d
    exact measurableSet_fineOriginalRetainedCellTag_eq_some left hleft cell hcell hdisj
      (fun sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T)) ↦ sample.1 i) (by fun_prop) d
  · intro j d
    exact measurableSet_fineOriginalRetainedCellTag_eq_some right hright cell hcell hdisj
      (fun sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T)) ↦ sample.2 j) (by fun_prop) d

end PopulationTypedCostData
end OTSelector.Reconstruction
