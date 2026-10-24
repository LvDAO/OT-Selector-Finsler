import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedPrefix

/-! The same global original residual experiment supplies the exact finite
retained-cell block observations. Counts remain the original binomial counts,
with no change to other retained cells or to the prescribed global residual. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The literal original retained flag together with one physical cell event. -/
def retainedMarkedCellEvent {X T : Type*} (A : Set X) : Set (X × Option (Bool × T)) :=
  {p | subplanRetentionFlag p.2 = false ∧ p.1 ∈ A}

theorem measurableSet_retainedMarkedCellEvent
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))] {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (retainedMarkedCellEvent (T := T) A) :=
  (measurableSet_eq_fun ((measurable_of_countable subplanRetentionFlag).comp measurable_snd)
    measurable_const).inter (measurable_fst hA)

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))]

/-- The actual extraction probability is the literal original retained
marginal's cell mass. The global residual remains exactly the prescribed ξ. -/
theorem original_retained_cell_event_mass
    (ξ : Measure (X × Y)) (hξ : ξ ≤ π) {A : Set X} {B : Set Y}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let R := D.refineSubplan ξ hξ
    (R.types.sourceMarkedLaw μ) (retainedMarkedCellEvent (T := T) A) =
      ((π - ξ).map Prod.fst) A ∧
    (R.types.targetMarkedLaw ν) (retainedMarkedCellEvent (T := T) B) =
      ((π - ξ).map Prod.snd) B := by
  have h := D.refineSubplan_retained_cell_observation_laws ξ hξ hA hB
    id id measurable_id measurable_id
  constructor
  · have hs := congrArg (fun ρ : Measure X ↦ ρ univ) h.1
    simpa only [retainedMarkedCellEvent, id_eq, Measure.map_apply measurable_fst MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, Measure.map_id] using hs
  · have ht := congrArg (fun ρ : Measure Y ↦ ρ univ) h.2
    simpa only [retainedMarkedCellEvent, id_eq, Measure.map_apply measurable_fst MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, Measure.map_id] using ht

/-- The conditional observed point law times its actual extraction mass is
exactly the original retained physical marginal observed in that cell. This
identity remains valid for null cells without a positive-density assumption. -/
theorem original_retained_cell_conditional_point_measure
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g) :
    let R := D.refineSubplan ξ hξ
    let _instS : IsProbabilityMeasure (R.types.sourceMarkedLaw μ) := (R.types.marked_probabilities hπ).1
    let _instT : IsProbabilityMeasure (R.types.targetMarkedLaw ν) := (R.types.marked_probabilities hπ).2.1
    ((π - ξ).map Prod.fst) A •
      ((restrictedPointLaw (R.types.sourceMarkedLaw μ) (retainedMarkedCellEvent (T := T) A)).map
        (fun p ↦ f p.1)) = (((π - ξ).map Prod.fst).restrict A).map f ∧
    ((π - ξ).map Prod.snd) B •
      ((restrictedPointLaw (R.types.targetMarkedLaw ν) (retainedMarkedCellEvent (T := T) B)).map
        (fun p ↦ g p.1)) = (((π - ξ).map Prod.snd).restrict B).map g := by
  let R := D.refineSubplan ξ hξ
  let _instS : IsProbabilityMeasure (R.types.sourceMarkedLaw μ) := (R.types.marked_probabilities hπ).1
  let _instT : IsProbabilityMeasure (R.types.targetMarkedLaw ν) := (R.types.marked_probabilities hπ).2.1
  have hpoint := D.refineSubplan_retained_cell_observation_laws ξ hξ hA hB f g hf hg
  have hmass := D.original_retained_cell_event_mass ξ hξ hA hB
  dsimp only
  constructor
  · rw [← hmass.1, ← Measure.map_smul, measure_smul_restrictedPointLaw]
    exact hpoint.1
  · rw [← hmass.2, ← Measure.map_smul, measure_smul_restrictedPointLaw]
    exact hpoint.2

/-- Both actual finite retained-cell blocks are extracted from the unchanged
original marked arrays, in original index order. Their exact product law has
original binomial counts and the literal original conditional observed laws.
No iid assertion is made for adaptively unmatched endpoints. -/
theorem original_retained_cell_prefix_observation_law
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π) (N : ℕ)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g) :
    let R := D.refineSubplan ξ hξ
    let _instS : IsProbabilityMeasure (R.types.sourceMarkedLaw μ) := (R.types.marked_probabilities hπ).1
    let _instT : IsProbabilityMeasure (R.types.targetMarkedLaw ν) := (R.types.marked_probabilities hπ).2.1
    let ρS := (restrictedPointLaw (R.types.sourceMarkedLaw μ)
      (retainedMarkedCellEvent (T := T) A)).map (fun p ↦ f p.1)
    let ρT := (restrictedPointLaw (R.types.targetMarkedLaw ν)
      (retainedMarkedCellEvent (T := T) B)).map (fun p ↦ g p.1)
    let _instρS : IsProbabilityMeasure ρS :=
      Measure.isProbabilityMeasure_map (hf.comp measurable_fst).aemeasurable
    let _instρT : IsProbabilityMeasure ρT :=
      Measure.isProbabilityMeasure_map (hg.comp measurable_fst).aemeasurable
    (R.markedLaw N).map (Prod.map
      (fun x ↦ mapBlockData (fun p ↦ f p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent A) x))
      (fun y ↦ mapBlockData (fun p ↦ g p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent B) y))) =
      (blockDataLaw ρS (binomWeight N ((((π - ξ).map Prod.fst) A).toNNReal))).prod
      (blockDataLaw ρT (binomWeight N ((((π - ξ).map Prod.snd) B).toNNReal))) := by
  let R := D.refineSubplan ξ hξ
  let _instS : IsProbabilityMeasure (R.types.sourceMarkedLaw μ) := (R.types.marked_probabilities hπ).1
  let _instT : IsProbabilityMeasure (R.types.targetMarkedLaw ν) := (R.types.marked_probabilities hπ).2.1
  have hS := measurableSet_retainedMarkedCellEvent (T := T) hA
  have hT := measurableSet_retainedMarkedCellEvent (T := T) hB
  have hfS : Measurable (fun p : X × Option (Bool × T) ↦ f p.1) := hf.comp measurable_fst
  have hgT : Measurable (fun p : Y × Option (Bool × T) ↦ g p.1) := hg.comp measurable_fst
  have hs := finiteOriginalRestrictedData_map_law (R.types.sourceMarkedLaw μ) N hS _ hfS
  have ht := finiteOriginalRestrictedData_map_law (R.types.targetMarkedLaw ν) N hT _ hgT
  have hmass := D.original_retained_cell_event_mass ξ hξ hA hB
  have hmS : Measurable (fun x : Fin N → X × Option (Bool × T) ↦
      mapBlockData (fun p ↦ f p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent A) x)) :=
    (measurable_mapBlockData hfS).comp (measurable_finiteOriginalRestrictedData hS)
  have hmT : Measurable (fun y : Fin N → Y × Option (Bool × T) ↦
      mapBlockData (fun p ↦ g p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent B) y)) :=
    (measurable_mapBlockData hgT).comp (measurable_finiteOriginalRestrictedData hT)
  dsimp only
  rw [show R.markedLaw N = (Measure.pi (fun _ : Fin N ↦ R.types.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin N ↦ R.types.targetMarkedLaw ν)) from rfl,
    ← Measure.map_prod_map _ _ hmS hmT, hs, ht]
  have hmassS : (R.types.sourceMarkedLaw μ) (retainedMarkedCellEvent (T := T) A) =
      ((π - ξ).map Prod.fst) A := hmass.1
  have hmassT : (R.types.targetMarkedLaw ν) (retainedMarkedCellEvent (T := T) B) =
      ((π - ξ).map Prod.snd) B := hmass.2
  simp only [restrictionWeight, hmassS, hmassT]
  rfl

end PopulationTypedCostData
end OTSelector.Reconstruction
