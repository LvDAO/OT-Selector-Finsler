import OTSelector.Reconstruction.FinslerRelativeLawLegalBinomialVarying
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineDensity
import OTSelector.Probability.MarkedCountBlockLaw

/-! True affine physical values on the exact original finite binomial prefixes. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The exact physical dilation is a changing quadratic multiplier on the same
finite legal graph and the same original stored prefix. -/
theorem unclampedBlockLegalTilted_affine_multiplier (q : ℕ) (hq : 0 < q)
    (source : A → ℝ) (target : B → ℝ) {r side : ℝ}
    (hr : 0 ≤ r) (hside : 0 ≤ side) (origin : Fin q → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    unclampedBlockLegalTilted q source target r kin probe t
      (mapBlockData (affineMarkedPoint origin side) dS)
      (mapBlockData (affineMarkedPoint origin side) dT) =
    unclampedBlockLegalTilted q source target 1
      (fun a b v ↦ (r ^ (2 / (q : ℝ)) * side ^ 2) * kin a b v) probe t dS dT := by
  rw [unclampedBlockLegalTilted_affine q hq source target hr hside origin kin hhom probe t]
  unfold unclampedBlockLegalTilted
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j _
  rw [rpow_affine_intensity q hq hr hside, Real.one_rpow, one_mul]

/-- Finite block-data expectation equals the original independently counted
cloud expectation, with the literal binomial prefix weights. -/
theorem binomialBlockLegalTilted_integrable_integral (q : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    let law := (blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
      (binomWeight N (Real.toNNReal (p : ℝ)))).prod
      (blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
        (binomWeight N (Real.toNNReal (p : ℝ))))
    let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      blockLegalTilted q source target r kin probe t d.1 d.2
    Integrable value law ∧ (∫ d, value d ∂law) =
      ∫ cloud, legalMarkedTilted q source target r kin probe t cloud
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p) := by
  let _instA : Nonempty A := nonempty_of_isProbabilityMeasure α
  let _instB : Nonempty B := nonempty_of_isProbabilityMeasure β
  let F := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
    blockLegalTilted q source target r kin probe t d.1 d.2
  let mk := Prod.map (fun z : MarkedCloudSpace q A ↦
    (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData ((Fin q → ℝ) × A)))
    (fun z : MarkedCloudSpace q B ↦
      (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData ((Fin q → ℝ) × B)))
  have hmk : Measurable mk := (measurable_blockDataMk q A).prodMap (measurable_blockDataMk q B)
  have hF : Measurable F := measurable_blockLegalTilted q hs ht r hk hp t
  have hmap : (twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)).map mk =
      (blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
        (binomWeight N (Real.toNNReal (p : ℝ)))).prod
        (blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
          (binomWeight N (Real.toNNReal (p : ℝ)))) :=
    twoMarkedBinomialLaw_map_prefix q α β N p
  have hi := integrable_legalMarkedTilted_countLaw q hs ht α β (ProbabilityTheory.binomial N p) (integrable_binomial _) hr hC hG
    hk hkb hp hpb t
  have hFi : Integrable F ((twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)).map mk) := by
    exact (integrable_map_measure hF.aestronglyMeasurable hmk.aemeasurable).mpr hi
  dsimp only
  constructor
  · rw [hmap] at hFi
    exact hFi
  · rw [← hmap]
    exact integral_map hmk.aemeasurable hF.aestronglyMeasurable

/-- The true untruncated physical affine competitor has exactly the original
binomial full-cube mean, including its actual sample-size dependent prefactor. -/
theorem affineBinomialBlock_integrable_integral (q : ℕ) (hq : 0 < q)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {side : ℝ} (hside : 0 ≤ side) (origin : Fin q → ℝ)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    let law := (blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
      (binomWeight N (Real.toNNReal (p : ℝ)))).prod
      (blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
        (binomWeight N (Real.toNNReal (p : ℝ))))
    let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target N kin probe t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)
    Integrable value law ∧ (∫ d, value d ∂law) =
      ∫ cloud, legalMarkedTilted q source target 1
        (fun a b v ↦ ((N : ℝ) ^ (2 / (q : ℝ)) * side ^ 2) * kin a b v) probe t cloud
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p) := by
  let pref := (N : ℝ) ^ (2 / (q : ℝ)) * side ^ 2
  have hpref : 0 ≤ pref := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (sq_nonneg _)
  have hki : ∀ a b v, |pref * kin a b v| ≤ (pref * C) * ∑ l, v l ^ 2 := by
    intro a b v
    rw [abs_mul, abs_of_nonneg hpref]
    exact (mul_le_mul_of_nonneg_left (hkb a b v) hpref).trans_eq (by ring)
  have hresult := binomialBlockLegalTilted_integrable_integral
    (kin := fun a b v ↦ pref * kin a b v) q hs ht α β N p
    (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg hpref hC) hG (hk.const_mul pref) hki hp hpb t
  let law := (blockDataLaw ((cubeMeasure (Fin q) 1).prod α)
    (binomWeight N (Real.toNNReal (p : ℝ)))).prod
    (blockDataLaw ((cubeMeasure (Fin q) 1).prod β)
      (binomWeight N (Real.toNNReal (p : ℝ))))
  have hcarrier : ∀ᵐ d ∂law,
      (∀ i, (d.1.2 i).1 ∈ unitCube q) ∧ (∀ j, (d.2.2 j).1 ∈ unitCube q) := by
    have hEvent : MeasurableSet {d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) |
      (∀ i, (d.1.2 i).1 ∈ unitCube q) ∧ (∀ j, (d.2.2 j).1 ∈ unitCube q)} :=
      ((measurableSet_blockSpatialCarrier (A := A) (measurableSet_unitCube q)).preimage measurable_fst).inter
        ((measurableSet_blockSpatialCarrier (A := B) (measurableSet_unitCube q)).preimage measurable_snd)
    rw [show law = _ from (twoMarkedBinomialLaw_map_prefix q α β N p).symm]
    apply (ae_map_iff ((measurable_blockDataMk q A).prodMap
      (measurable_blockDataMk q B)).aemeasurable hEvent).mpr
    have hac := twoMarkedCountLaw_absolutelyContinuous_poisson_one q α β
      (ProbabilityTheory.binomial N p)
    filter_upwards [hac.ae_le (ae_points_mem_unitCube_twoMarkedCloudLaw q α β 1)] with cloud hcloud
    exact ⟨fun i ↦ hcloud.1 i, fun j ↦ hcloud.2 j⟩
  have heq : (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target N kin probe t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)) =ᵐ[law]
      (fun d ↦ blockLegalTilted q source target 1 (fun a b v ↦ pref * kin a b v) probe t d.1 d.2) := by
    filter_upwards [hcarrier] with d hd
    rw [unclampedBlockLegalTilted_affine_multiplier q hq source target (Nat.cast_nonneg N)
      hside origin kin hhom probe t]
    exact unclampedBlockLegalTilted_eq_block q source target 1 _ probe t d.1 d.2 hd.1 hd.2
  exact ⟨hresult.1.congr heq.symm, (integral_congr_ae heq).trans hresult.2⟩

end OTSelector.Reconstruction
