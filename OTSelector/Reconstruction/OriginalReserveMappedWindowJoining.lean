import OTSelector.Reconstruction.OriginalReserveMappedWindowSampler
import OTSelector.Reconstruction.OriginalReservePhysicalWindowFullInput

/-! The whole original reserve and the actual unit-cube iid experiment share one joining. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The original cube sampler is kept as a complete marginal: positions remain
independent of its marks/count before marks-only deletion. The whole reserve is
an additional identity witness and is never inserted into that iid auxiliary data. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalReserve_fullMappedWindow_joining
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F)
    (hpoint : (cubeMeasure (Fin q) 1).map F =
      normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K))
    {A : Set ℝ} (hA : IsCompact A) (hα : α.support ⊆ A) (hβ : β.support ⊆ A) :
    ∃ J : ProbabilityMeasure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ),
      (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map
        Prod.fst = (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map
        Prod.snd = twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
        (p.1.2 : Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' K) =
            legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q F p.2) := by
  let : StandardBorelSpace (MarkedCloudSpace q ℝ) := by infer_instance
  let U : Set (LegalColoredInputPoint q) := (K ×ˢ A) ×ˢ univ
  have hU : IsCompact U := (hK.prod hA).prod isCompact_univ
  have hUK : U ⊆ (Prod.fst ∘ Prod.fst) ⁻¹' K := fun _ h ↦ h.1.1
  obtain ⟨J, hleft, hright, heq⟩ :=
    N.exists_originalReserve_window_joining_of_sampler hK hKpos hU hUK
      (twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal)
      (originalMappedReserveCloudArrays q F)
      (measurable_originalMappedReserveCloudArrays q hF)
      (map_originalMappedReserveCloudArrays q hK hKpos hF hpoint α β)
  have hclock : ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
      ∀ᵐ x ∂(p.1.2 : Measure (LegalColoredInputPoint q)), x.1.2 ∈ A := by
    have h : ∀ᵐ scene ∂(J : Measure
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map Prod.fst,
        ∀ᵐ x ∂(scene.2 : Measure (LegalColoredInputPoint q)), x.1.2 ∈ A := by
      rw [hleft]
      exact N.ae_ae_originalInput_clockCarrier hA.measurableSet hα hβ
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hrawpoints : ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal,
      ∀ᵐ x ∂legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q F ω), x ∈ U := by
    have hp : ∀ᵐ ω ∂(twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal).map
        (originalMappedReserveTwoCloud q F),
        ∀ᵐ x ∂legalInputTwoBlockMeasure q (originalPhysicalReserveCloudArrays q ω), x ∈ U := by
      rw [map_originalMappedReserveTwoCloud q hK hKpos hF hpoint α β]
      exact ae_originalPhysicalReserveCloudArrays_mem q hK hKpos α β
        ((show ∀ᵐ x ∂α, x ∈ α.support from α.support_mem_ae).mono fun _ h ↦ hα h) ((show ∀ᵐ x ∂β, x ∈ β.support from β.support_mem_ae).mono fun _ h ↦ hβ h)
    exact ae_of_ae_map (measurable_originalMappedReserveTwoCloud q hF).aemeasurable hp
  have hpoints : ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
      ∀ᵐ x ∂legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q F p.2), x ∈ U := by
    have h : ∀ᵐ ω ∂(J : Measure
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map Prod.snd,
        ∀ᵐ x ∂legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q F ω), x ∈ U := by
      rw [hright]
      exact hrawpoints
    exact ae_of_ae_map measurable_snd.aemeasurable h
  refine ⟨J, hleft, hright, ?_⟩
  filter_upwards [heq, hclock, hpoints] with p hp hc hx
  exact originalReserve_compactWindow_identity_extend_clockCarrier hK.measurableSet _ _ hc hx hp

end OTSelector.Reconstruction
