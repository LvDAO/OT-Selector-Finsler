import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkedCellPrefix
import OTSelector.Probability.FiniteMeasureConditioning

/-! Literal unnormalized original retained observation laws determine the exact
normalized finite-prefix model law and its unchanged original binomial count. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- A positive finite original observed restriction has its own normalized
point law at exactly its original binomial extraction count. -/
theorem finiteOriginalRestrictedData_normalized_model_law
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ) {S : Set X} (hS : MeasurableSet S)
    (f : X → Y) (hf : Measurable f) (τ : Measure Y) [IsFiniteMeasure τ]
    (hτ : 0 < τ.real univ) (hlaw : (ν.restrict S).map f = τ) :
    let _inst : IsProbabilityMeasure (normalizedFiniteLaw τ) := normalizedFiniteLaw_probability τ hτ
    (Measure.pi (fun _ : Fin N ↦ ν)).map
      (fun x ↦ mapBlockData f (finiteOriginalRestrictedData S x)) =
      blockDataLaw (normalizedFiniteLaw τ) (binomWeight N (τ univ).toNNReal) := by
  have hmass : ν S = τ univ := by
    have h := congrArg (fun ρ : Measure Y ↦ ρ univ) hlaw
    simpa only [Measure.map_apply hf MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ] using h
  have hpositive : ν S ≠ 0 := by
    rw [hmass]
    intro hz
    have : τ.real univ = 0 := by rw [measureReal_def, hz, ENNReal.toReal_zero]
    exact hτ.ne' this
  have hnorm : (normalizedFiniteLaw (ν.restrict S)).map f =
      normalizedFiniteLaw ((ν.restrict S).map f) := by
    have hm : ((ν.restrict S).map f).real univ = (ν.restrict S).real univ := by
      simp only [measureReal_def, Measure.map_apply hf MeasurableSet.univ, preimage_univ]
    simp only [normalizedFiniteLaw, hm, Measure.map_smul]
  have hpoint : (restrictedPointLaw ν S).map f = normalizedFiniteLaw τ := by
    rw [restrictedPointLaw, ite_eq_right hpositive,
      ← normalizedFiniteLaw_restrict_eq_cond ν S (measure_ne_top ν S), hnorm, hlaw]
  let _inst : IsProbabilityMeasure (normalizedFiniteLaw τ) := normalizedFiniteLaw_probability τ hτ
  have h := finiteOriginalRestrictedData_map_law ν N hS f hf
  dsimp only at h ⊢
  simpa only [restrictionWeight, hmass, hpoint] using h

/-- Exact original retained physical point laws supply the normalized model
prefixes inside the same global residual experiment. Both original counts stay
binomial at the actual model masses; no conditional-iid premise is added. -/
theorem PopulationTypedCostData.original_retained_prefix_normalized_model_law
    {X Y Z W T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (hπ : Vlasov.IsCoupling π μ ν) (ξ : Measure (X × Y)) (hξ : ξ ≤ π) (N : ℕ)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g)
    (τS : Measure Z) (τT : Measure W) [IsFiniteMeasure τS] [IsFiniteMeasure τT]
    (hτS : 0 < τS.real univ) (hτT : 0 < τT.real univ)
    (hsource : (((π - ξ).map Prod.fst).restrict A).map f = τS)
    (htarget : (((π - ξ).map Prod.snd).restrict B).map g = τT) :
    let R := D.refineSubplan ξ hξ
    let _instS : IsProbabilityMeasure (normalizedFiniteLaw τS) := normalizedFiniteLaw_probability τS hτS
    let _instT : IsProbabilityMeasure (normalizedFiniteLaw τT) := normalizedFiniteLaw_probability τT hτT
    (R.markedLaw N).map (Prod.map
      (fun x ↦ mapBlockData (fun p ↦ f p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent A) x))
      (fun y ↦ mapBlockData (fun p ↦ g p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent B) y))) =
      (blockDataLaw (normalizedFiniteLaw τS) (binomWeight N (τS univ).toNNReal)).prod
      (blockDataLaw (normalizedFiniteLaw τT) (binomWeight N (τT univ).toNNReal)) := by
  let R := D.refineSubplan ξ hξ
  let _instMarkedS : IsProbabilityMeasure (R.types.sourceMarkedLaw μ) := (R.types.marked_probabilities hπ).1
  let _instMarkedT : IsProbabilityMeasure (R.types.targetMarkedLaw ν) := (R.types.marked_probabilities hπ).2.1
  have hS := measurableSet_retainedMarkedCellEvent (T := T) hA
  have hT := measurableSet_retainedMarkedCellEvent (T := T) hB
  have hfS : Measurable (fun p : X × Option (Bool × T) ↦ f p.1) := hf.comp measurable_fst
  have hgT : Measurable (fun p : Y × Option (Bool × T) ↦ g p.1) := hg.comp measurable_fst
  have hphysical := D.refineSubplan_retained_cell_observation_laws ξ hξ hA hB f g hf hg
  have hs := finiteOriginalRestrictedData_normalized_model_law (R.types.sourceMarkedLaw μ) N hS
    _ hfS τS hτS (hphysical.1.trans hsource)
  have ht := finiteOriginalRestrictedData_normalized_model_law (R.types.targetMarkedLaw ν) N hT
    _ hgT τT hτT (hphysical.2.trans htarget)
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

end OTSelector.Reconstruction
