import OTSelector.Reconstruction.OriginalReservePhysicalWindowJoining
import OTSelector.Reconstruction.OriginalReservePhysicalWindowSupport

/-! The actual reserve-only joining identifies its complete original physical-window input. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Clock support extends the same compact marked-window identity to the
entire original physical-window input, retaining every mark and multiplicity. -/
theorem originalReserve_compactWindow_identity_extend_clockCarrier {q : ℕ}
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) {A : Set ℝ}
    (μ ν : Measure (LegalColoredInputPoint q))
    (hclock : ∀ᵐ p ∂μ, p.1.2 ∈ A)
    (hν : ∀ᵐ p ∂ν, p ∈ (K ×ˢ A) ×ˢ (univ : Set (Fin 2)))
    (heq : μ.restrict ((K ×ˢ A) ×ˢ (univ : Set (Fin 2))) =
      ν.restrict ((K ×ˢ A) ×ˢ (univ : Set (Fin 2)))) :
    μ.restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) = ν := by
  have hsub : ((K ×ˢ A) ×ˢ (univ : Set (Fin 2))) ⊆
      (Prod.fst ∘ Prod.fst) ⁻¹' K := fun _ h ↦ h.1.1
  have hμ : ∀ᵐ p ∂μ.restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K),
      p ∈ (K ×ˢ A) ×ˢ (univ : Set (Fin 2)) := by
    filter_upwards [ae_restrict_mem (hK.preimage (measurable_fst.comp measurable_fst)),
      ae_restrict_of_ae hclock] with p hp hc
    exact ⟨⟨hp, hc⟩, mem_univ _⟩
  have hμeq := Measure.restrict_eq_self_of_ae_mem hμ
  rw [Measure.restrict_restrict_of_subset hsub] at hμeq
  exact hμeq.symm.trans (heq.trans (Measure.restrict_eq_self_of_ae_mem hν))

/-- The original reserve scene and literal finite iid observations can be
joined with their full physical-window point measures equal. Compactness of the
actual original clock supports supplies the only clock carrier. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalReserve_fullPhysicalWindow_joining
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {A : Set ℝ} (hA : IsCompact A) (hα : α.support ⊆ A) (hβ : β.support ⊆ A) :
    ∃ J : ProbabilityMeasure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ),
      (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map
        Prod.fst = (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map
        Prod.snd = originalPhysicalReserveTwoCloudLaw q K α β ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
        (p.1.2 : Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' K) =
            legalInputTwoBlockMeasure q (originalPhysicalReserveCloudArrays q p.2) := by
  let U : Set (LegalColoredInputPoint q) := (K ×ˢ A) ×ˢ univ
  have hU : IsCompact U := (hK.prod hA).prod isCompact_univ
  have hUK : U ⊆ (Prod.fst ∘ Prod.fst) ⁻¹' K := fun _ h ↦ h.1.1
  obtain ⟨J, hleft, hright, heq⟩ := N.exists_originalReserve_physicalWindow_joining hK hKpos hU hUK
  have hclock : ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
      ∀ᵐ x ∂(p.1.2 : Measure (LegalColoredInputPoint q)), x.1.2 ∈ A := by
    have h : ∀ᵐ scene ∂(J : Measure
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map Prod.fst,
        ∀ᵐ x ∂(scene.2 : Measure (LegalColoredInputPoint q)), x.1.2 ∈ A := by
      rw [hleft]
      exact N.ae_ae_originalInput_clockCarrier hA.measurableSet hα hβ
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hpoints : ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
      ∀ᵐ x ∂legalInputTwoBlockMeasure q (originalPhysicalReserveCloudArrays q p.2), x ∈ U := by
    have h : ∀ᵐ ω ∂(J : Measure
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map Prod.snd,
        ∀ᵐ x ∂legalInputTwoBlockMeasure q (originalPhysicalReserveCloudArrays q ω), x ∈ U := by
      rw [hright]
      exact ae_originalPhysicalReserveCloudArrays_mem q hK hKpos α β
        ((show ∀ᵐ x ∂α, x ∈ α.support from α.support_mem_ae).mono fun _ h ↦ hα h) ((show ∀ᵐ x ∂β, x ∈ β.support from β.support_mem_ae).mono fun _ h ↦ hβ h)
    exact ae_of_ae_map measurable_snd.aemeasurable h
  refine ⟨J, hleft, hright, ?_⟩
  filter_upwards [heq, hclock, hpoints] with p hp hc hx
  exact originalReserve_compactWindow_identity_extend_clockCarrier hK.measurableSet _ _ hc hx hp

end OTSelector.Reconstruction
