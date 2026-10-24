import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkedCellPrefix

/-! Null retained cells have their exact empty original finite prefixes. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Canonical empty prefix; its point function has empty domain. -/
def emptyOriginalBlockData (X : Type*) : BlockData X := ⟨0, Fin.elim0⟩

/-- A null original binomial extraction reads no points, independently of any
unused conditional fallback law. -/
theorem blockDataLaw_binomWeight_zero {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ) :
    blockDataLaw ν (binomWeight N 0) = Measure.dirac (emptyOriginalBlockData X) := by
  have hz : (Measure.pi (fun _ : Fin 0 ↦ ν)).map (fun y ↦ (⟨0, y⟩ : BlockData X)) =
      Measure.dirac (emptyOriginalBlockData X) := by
    rw [Measure.pi_of_empty _ (fun i : Fin 0 ↦ Fin.elim0 i)]
    exact Measure.map_dirac' (f := fun y : Fin 0 → X ↦ (⟨0, y⟩ : BlockData X))
      (measurable_sigma_mk 0) (fun i : Fin 0 ↦ Fin.elim0 i)
  ext S hS
  rw [blockDataLaw, Measure.sum_apply _ hS, tsum_eq_single 0]
  · simp [binomWeight, hz]
  · intro m hm
    simp [binomWeight, hm]

/-- The original fixed iid sample has an empty observed prefix whenever its
literal extraction event is null. -/
theorem finiteOriginalRestrictedData_null_law
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ) {S : Set X}
    (hS : MeasurableSet S) (hnull : ν S = 0) (f : X → Y) (hf : Measurable f) :
    (Measure.pi (fun _ : Fin N ↦ ν)).map
      (fun x ↦ mapBlockData f (finiteOriginalRestrictedData S x)) =
      Measure.dirac (emptyOriginalBlockData Y) := by
  let _inst : IsProbabilityMeasure ((restrictedPointLaw ν S).map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have h := finiteOriginalRestrictedData_map_law ν N hS f hf
  dsimp only at h
  simpa only [restrictionWeight, hnull, ENNReal.toNNReal_zero, blockDataLaw_binomWeight_zero] using h

/-- Two null original retained marginal cells have exactly the empty paired
prefix in the same original global residual experiment. -/
theorem PopulationTypedCostData.original_retained_null_cell_prefix_law
    {X Y Z W T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π) (N : ℕ)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hnullA : ((π - ξ).map Prod.fst) A = 0) (hnullB : ((π - ξ).map Prod.snd) B = 0)
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g) :
    let R := D.refineSubplan ξ hξ
    (R.markedLaw N).map (Prod.map
      (fun x ↦ mapBlockData (fun p ↦ f p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent A) x))
      (fun y ↦ mapBlockData (fun p ↦ g p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent B) y))) =
      Measure.dirac (emptyOriginalBlockData Z, emptyOriginalBlockData W) := by
  let R := D.refineSubplan ξ hξ
  let _instS : IsProbabilityMeasure (R.types.sourceMarkedLaw μ) := (R.types.marked_probabilities hπ).1
  let _instT : IsProbabilityMeasure (R.types.targetMarkedLaw ν) := (R.types.marked_probabilities hπ).2.1
  let _instObsS : IsProbabilityMeasure ((restrictedPointLaw (R.types.sourceMarkedLaw μ)
      (retainedMarkedCellEvent (T := T) A)).map (fun p ↦ f p.1)) :=
    Measure.isProbabilityMeasure_map (hf.comp measurable_fst).aemeasurable
  let _instObsT : IsProbabilityMeasure ((restrictedPointLaw (R.types.targetMarkedLaw ν)
      (retainedMarkedCellEvent (T := T) B)).map (fun p ↦ g p.1)) :=
    Measure.isProbabilityMeasure_map (hg.comp measurable_fst).aemeasurable
  have h := D.original_retained_cell_prefix_observation_law hπ ξ hξ N hA hB f g hf hg
  dsimp only at h ⊢
  simpa only [hnullA, hnullB, ENNReal.toNNReal_zero, blockDataLaw_binomWeight_zero,
    Measure.dirac_prod_dirac] using h

end OTSelector.Reconstruction
