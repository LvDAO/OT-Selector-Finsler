import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineBinomial
import OTSelector.Probability.BinomialShapeLaw

/-! Actual affine physical finite-prefix costs under exact original binomial
shape laws. Shape restriction and count thinning precede any pressure limit. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Exact original binomial shape prefixes retain the original cube carrier,
including null shapes, whose count is zero. -/
theorem ae_binomialShapeBlockLaw_unitCube_two (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    ∀ᵐ d ∂(binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S),
      (∀ i, (d.1.2 i).1 ∈ unitCube q) ∧ (∀ j, (d.2.2 j).1 ∈ unitCube q) := by
  have hEvent : MeasurableSet {d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) |
      (∀ i, (d.1.2 i).1 ∈ unitCube q) ∧ (∀ j, (d.2.2 j).1 ∈ unitCube q)} :=
    ((measurableSet_blockSpatialCarrier (A := A) (measurableSet_unitCube q)).preimage measurable_fst).inter
      ((measurableSet_blockSpatialCarrier (A := B) (measurableSet_unitCube q)).preimage measurable_snd)
  rw [← map_shapeCloud_twoMarkedBinomialLaw q α β N p hS]
  apply (ae_map_iff ((measurable_shapeCloud (A := A) hS).prodMap
    (measurable_shapeCloud (A := B) hS)).aemeasurable hEvent).mpr
  have hac := twoMarkedCountLaw_absolutelyContinuous_poisson_one q α β
    (ProbabilityTheory.binomial N p)
  filter_upwards [hac.ae_le (ae_points_mem_unitCube_twoMarkedCloudLaw q α β 1)] with sample hs
  exact ⟨fun i ↦ hs.1 (shapeCloudEmbedding S sample.1 i),
    fun j ↦ hs.2 (shapeCloudEmbedding S sample.2 j)⟩

/-- The literal original finite shape-prefix physical mean differs from its
full-box binomial mean only by original hole mass times the finite-scale edge
budget. All physical density and affine factors are retained exactly. -/
theorem FiniteScalarBins.integrable_density_affine_binomialShapeLaw_compare
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap) (hgap : 0 < gap)
    (q : ℕ) (hq : 0 < q) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) (r density side : ℝ≥0) (hd : 0 < density) (origin : Fin q → ℝ)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ clockSet)
    (hsep : ∀ᵐ ab ∂α.prod β, gap ≤ |target ab.2 - source ab.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun ab : A × B ↦ kin ab.1 ab.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    let intensity := (r : ℝ) * density * side ^ q
    let scaledKin := fun a b v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * kin a b v
    let law := (binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)
    let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin g t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)
    Integrable value law ∧
    |(∫ d, value d ∂law) - (∫ sample, legalMarkedTilted q source target intensity scaledKin g t sample
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p))| ≤
      (2 * ((N : ℝ) * (p : ℝ)) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) * (intensity ^ (2 / (q : ℝ)) *
          (((density : ℝ) ^ (-(2 / (q : ℝ))) * C) * q) + |t| * G)) := by
  dsimp only
  let _instA : Nonempty A := nonempty_of_isProbabilityMeasure α
  let _instB : Nonempty B := nonempty_of_isProbabilityMeasure β
  let scaledKin := fun a b v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * kin a b v
  let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
    unclampedBlockLegalTilted q source target r kin g t
      (mapBlockData (affineMarkedPoint origin side) d.1)
      (mapBlockData (affineMarkedPoint origin side) d.2)
  let model := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
    blockLegalTilted q source target ((r : ℝ) * density * side ^ q) scaledKin g t d.1 d.2
  have hkm : Measurable (Function.uncurry (fun ab : A × B ↦ scaledKin ab.1 ab.2)) :=
    measurable_const.mul hk
  have hm : Measurable model := measurable_blockLegalTilted q hs ht _ hkm hg t
  obtain ⟨hI, hbound⟩ := D.integrable_density_affine_shapeBinomial_compare hgap q hq hs ht
    α β N p r density side hd origin hS hsource hsep hC hG hk hkb hhom hg hgb t
  have heqSource : (fun sample ↦ value (shapeCloud S sample.1, shapeCloud S sample.2))
      =ᵐ[twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)]
      (fun sample ↦ model (shapeCloud S sample.1, shapeCloud S sample.2)) :=
    ae_countLaw_unclampedBlockLegalTilted_affine_density q hq source target α β
      (ProbabilityTheory.binomial N p) S r.coe_nonneg (by exact_mod_cast hd) side.coe_nonneg
      origin kin hhom g t
  have hmodel := shapeCloud_binomial_integrable_integral q α β N p hS model hm (hI.congr heqSource)
  have heqModel : value =ᵐ[(binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)]
      model := by
    filter_upwards [ae_binomialShapeBlockLaw_unitCube_two q α β N p hS] with d hd'
    exact unclampedBlockLegalTilted_affine_density q hq source target r.coe_nonneg
      (by exact_mod_cast hd) side.coe_nonneg origin kin hhom g t d.1 d.2 hd'.1 hd'.2
  refine ⟨hmodel.1.congr heqModel.symm, ?_⟩
  rw [integral_congr_ae heqModel, hmodel.2, ← integral_congr_ae heqSource]
  exact hbound

end OTSelector.Reconstruction
