import OTSelector.Reconstruction.FinslerRelativeLawOriginalRawClassValue
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPrefixModelLaw

/-! Exact true-coordinate canonical means on the unchanged original marked experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- The original retained cell's canonical frozen optimizer has precisely the
finite-block mean dictated by its actual unnormalized physical observation
laws. Model integrability transfers in both directions on the same sample. -/
theorem PopulationTypedCostData.original_retained_raw_model_cost_integral
    {X Z C T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {π : Measure (X × X)} [IsFiniteMeasure π] {qAtlas : ℕ} {cost : X → X → ℝ}
    (D : PopulationTypedCostData π μ ν T qAtlas cost) (hπ : Vlasov.IsCoupling π μ ν)
    (ξ : Measure (X × X)) (hξ : ξ ≤ π) (N : ℕ)
    (a : X → Z) (cell : C → Set Z) (c : C) (hc : MeasurableSet (a ⁻¹' cell c))
    {A B : C → Type*} [∀ c, MeasurableSpace (A c)] [∀ c, MeasurableSpace (B c)] {q : ℕ}
    [Nonempty (A c)] [Nonempty (B c)]
    (readS : ∀ c, X → (Fin q → ℝ) × A c) (readT : ∀ c, X → (Fin q → ℝ) × B c)
    (hmS : Measurable (readS c)) (hmT : Measurable (readT c))
    (source : ∀ c, A c → ℝ) (target : ∀ c, B c → ℝ)
    (hs : Measurable (source c)) (ht : Measurable (target c))
    (r : C → ℝ) (kin : ∀ c, A c → B c → (Fin q → ℝ) → ℝ)
    (probe : ∀ c, A c → B c → ℝ) (tilt : ℝ)
    (hk : Measurable (Function.uncurry (fun p : A c × B c ↦ kin c p.1 p.2)))
    (hg : Measurable (Function.uncurry (probe c)))
    (τS : Measure ((Fin q → ℝ) × A c)) (τT : Measure ((Fin q → ℝ) × B c))
    [IsFiniteMeasure τS] [IsFiniteMeasure τT] (hτS : 0 < τS.real univ) (hτT : 0 < τT.real univ)
    (hsource : (((π - ξ).map Prod.fst).restrict (a ⁻¹' cell c)).map (readS c) = τS)
    (htarget : (((π - ξ).map Prod.snd).restrict (a ⁻¹' cell c)).map (readT c) = τT) :
    let R := D.refineSubplan ξ hξ
    let _instS : IsProbabilityMeasure (normalizedFiniteLaw τS) := normalizedFiniteLaw_probability τS hτS
    let _instT : IsProbabilityMeasure (normalizedFiniteLaw τT) := normalizedFiniteLaw_probability τT hτT
    let modelLaw := (blockDataLaw (normalizedFiniteLaw τS) (binomWeight N (τS univ).toNNReal)).prod
      (blockDataLaw (normalizedFiniteLaw τT) (binomWeight N (τT univ).toNNReal))
    let extra := originalCellScalarClassGraph readS readT source target
    let score := originalCellRawClassScore readS readT r kin probe tilt
    let value := fun sample ↦ (originalRetainedCellOptimizer a cell extra score c sample).cost (score c sample)
    let modelValue := fun d ↦ unclampedBlockLegalTilted q (source c) (target c) (r c) (kin c) (probe c) tilt d.1 d.2
    (Integrable value (R.markedLaw N) ↔ Integrable modelValue modelLaw) ∧
      (∫ sample, value sample ∂R.markedLaw N) = ∫ d, modelValue d ∂modelLaw := by
  let R := D.refineSubplan ξ hξ
  let obsS := fun x : Fin N → X × Option (Bool × T) ↦ mapBlockData (fun p ↦ readS c p.1)
    (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) x)
  let obsT := fun y : Fin N → X × Option (Bool × T) ↦ mapBlockData (fun p ↦ readT c p.1)
    (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) y)
  let obs := Prod.map obsS obsT
  have hobsS : Measurable obsS := (measurable_mapBlockData (hmS.comp measurable_fst)).comp
    (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent hc))
  have hobsT : Measurable obsT := (measurable_mapBlockData (hmT.comp measurable_fst)).comp
    (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent hc))
  have hobs : Measurable obs := hobsS.prodMap hobsT
  let F := fun d : BlockData ((Fin q → ℝ) × A c) × BlockData ((Fin q → ℝ) × B c) ↦ unclampedBlockLegalTilted q (source c) (target c) (r c) (kin c) (probe c) tilt d.1 d.2
  have hF : Measurable F := measurable_unclampedBlockLegalTilted q hs ht _ hk hg tilt
  have hlaw := D.original_retained_prefix_normalized_model_law hπ ξ hξ N hc hc
    (readS c) (readT c) hmS hmT τS τT hτS hτT hsource htarget
  dsimp only at hlaw ⊢
  have heq : (fun sample ↦ (originalRetainedCellOptimizer a cell
      (originalCellScalarClassGraph readS readT source target)
      (originalCellRawClassScore readS readT r kin probe tilt) c sample).cost
        (originalCellRawClassScore readS readT r kin probe tilt c sample)) = F ∘ obs := by
    funext sample
    exact originalRetainedCellOptimizer_raw_model_cost_eq_unclampedBlockLegalTilted a cell readS readT
      source target r kin probe tilt c sample
  rw [heq]
  constructor
  · have h := integrable_map_measure (μ := R.markedLaw N) hF.aestronglyMeasurable hobs.aemeasurable
    rw [hlaw] at h
    exact h.symm
  · have h := integral_map (μ := R.markedLaw N) hobs.aemeasurable hF.aestronglyMeasurable
    rw [hlaw] at h
    exact h.symm

end OTSelector.Reconstruction
