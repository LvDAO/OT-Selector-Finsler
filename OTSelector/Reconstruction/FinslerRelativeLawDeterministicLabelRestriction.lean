import OTSelector.Reconstruction.FinslerRelativeLawOriginalPrefixModelLaw

/-! Deterministic label truncation preserves the same whole original population. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The discarded deterministic retained label mass joins the true residual. -/
def restrictOriginalRetainedResidual {X Z : Type*} [MeasurableSpace X]
    (χ ξ : Measure (X × X)) (a : X → Z) (G : Set Z) : Measure (X × X) :=
  ξ + χ.restrict {p | a p.1 ∉ G}

instance restrictOriginalRetainedResidual_finite
    {X Z : Type*} [MeasurableSpace X] (χ ξ : Measure (X × X))
    [IsFiniteMeasure χ] [IsFiniteMeasure ξ] (a : X → Z) (G : Set Z) :
    IsFiniteMeasure (restrictOriginalRetainedResidual χ ξ a G) := by
  unfold restrictOriginalRetainedResidual
  infer_instance

/-- Deterministic spatial truncation leaves the whole original coupling fixed. -/
theorem original_retained_label_restriction_split
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (χ ξ : Measure (X × X)) (a : X → Z) (ha : Measurable a)
    {G : Set Z} (hG : MeasurableSet G) :
    χ.restrict {p | a p.1 ∈ G} + restrictOriginalRetainedResidual χ ξ a G = χ + ξ := by
  calc
    _ = (χ.restrict {p | a p.1 ∈ G} + χ.restrict {p | a p.1 ∉ G}) + ξ := by
      unfold restrictOriginalRetainedResidual
      ac_rfl
    _ = χ + ξ := by
      change (χ.restrict ((a ∘ Prod.fst) ⁻¹' G) + χ.restrict ((a ∘ Prod.fst) ⁻¹' G)ᶜ) + ξ = _
      rw [Measure.restrict_add_restrict_compl ((ha.comp measurable_fst) hG)]

/-- The true residual remains a subplan of the same original whole population. -/
theorem restrictOriginalRetainedResidual_le
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (χ ξ : Measure (X × X)) (a : X → Z) (ha : Measurable a)
    {G : Set Z} (hG : MeasurableSet G) :
    restrictOriginalRetainedResidual χ ξ a G ≤ χ + ξ := by
  rw [← original_retained_label_restriction_split χ ξ a ha hG]
  exact Measure.le_add_left le_rfl

/-- The complement of the enlarged residual is exactly the original retained
plan restricted by the prescribed labels. No old edge selection enters. -/
theorem original_retained_label_restriction_complement
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G) :
    (χ + ξ) - restrictOriginalRetainedResidual χ ξ a G = χ.restrict {p | a p.1 ∈ G} := by
  rw [← original_retained_label_restriction_split χ ξ a ha hG, Measure.add_sub_cancel]

/-- The extra residual mass is bounded by the ORIGINAL label mass removed
inside the existing retained label support. This bound permits the prescribed
label set to depend deterministically on empirical order. -/
theorem restrictOriginalRetainedResidual_mass_le
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (χ ξ : Measure (X × X)) (μ ν : Measure X)
    (hwhole : Vlasov.IsCoupling (χ + ξ) μ ν)
    (a : X → Z) (ha : Measurable a) {K G : Set Z}
    (hK : MeasurableSet K) (hG : MeasurableSet G)
    (hsupport : ∀ᵐ p ∂χ, a p.1 ∈ K) :
    restrictOriginalRetainedResidual χ ξ a G univ ≤ ξ univ + (μ.map a) (K \ G) := by
  have he : {p : X × X | a p.1 ∉ G} =ᵐ[χ] {p | a p.1 ∈ K \ G} :=
    hsupport.mono fun p hp ↦ by
      change (a p.1 ∉ G) = (a p.1 ∈ K ∧ a p.1 ∉ G)
      exact propext (and_iff_right hp).symm
  have hdom : χ ≤ χ + ξ := Measure.le_add_right le_rfl
  have hm : χ {p | a p.1 ∉ G} ≤ (μ.map a) (K \ G) := by
    rw [measure_congr he]
    calc
      _ ≤ (χ + ξ) {p | a p.1 ∈ K \ G} := hdom _
      _ = μ (a ⁻¹' (K \ G)) := by
        rw [← hwhole.1, Measure.map_apply measurable_fst (ha (hK.diff hG))]
        rfl
      _ = (μ.map a) (K \ G) := (Measure.map_apply ha (hK.diff hG)).symm
  simpa only [restrictOriginalRetainedResidual, Measure.add_apply,
    Measure.restrict_apply_univ] using add_le_add (le_refl (ξ univ)) hm

/-- Source observations on every retained subcell are unchanged by the
prescribed deterministic label restriction. -/
theorem original_retained_label_restriction_source
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (χ : Measure (X × X)) (a : X → Z) (ha : Measurable a)
    {G L : Set Z} (hG : MeasurableSet G) (hsub : L ⊆ G) :
    ((χ.restrict {p | a p.1 ∈ G}).map Prod.fst).restrict (a ⁻¹' L) =
      (χ.map Prod.fst).restrict (a ⁻¹' L) := by
  change ((χ.restrict (Prod.fst ⁻¹' (a ⁻¹' G))).map Prod.fst).restrict (a ⁻¹' L) = _
  rw [← Measure.restrict_map measurable_fst (ha hG)]
  exact Measure.restrict_restrict_of_subset (preimage_mono hsub)

/-- Target observations on those same subcells are unchanged. The shared label
is read from the actual original retained population. -/
theorem original_retained_label_restriction_target
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (χ : Measure (X × X)) (a : X → Z) (ha : Measurable a)
    (hlabel : ∀ᵐ p ∂χ, a p.1 = a p.2)
    {G L : Set Z} (hG : MeasurableSet G) (hsub : L ⊆ G) :
    ((χ.restrict {p | a p.1 ∈ G}).map Prod.snd).restrict (a ⁻¹' L) =
      (χ.map Prod.snd).restrict (a ⁻¹' L) := by
  have he : {p : X × X | a p.1 ∈ G} =ᵐ[χ] {p | a p.2 ∈ G} :=
    hlabel.mono fun p hp ↦ by
      change (a p.1 ∈ G) = (a p.2 ∈ G)
      rw [hp]
  rw [Measure.restrict_congr_set he]
  change ((χ.restrict (Prod.snd ⁻¹' (a ⁻¹' G))).map Prod.snd).restrict (a ⁻¹' L) = _
  rw [← Measure.restrict_map measurable_snd (ha hG)]
  exact Measure.restrict_restrict_of_subset (preimage_mono hsub)

/-- Calibration and original marginal support supply the actual shared label
condition for every retained subplan of the rebuilt original population. -/
theorem original_calibrated_coupling_labels
    {X Z : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ ν : Measure X) (π χ : Measure (X × X)) (hπ : Vlasov.IsCoupling π μ ν) (hχ : χ ≤ π)
    (a : X → Z) (u : X → ℝ) {A : Set X}
    (horder : ∀ x ∈ A, ∀ y ∈ A, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνA : ∀ᵐ y ∂ν, y ∈ A)
    (hcal : ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2) :
    ∀ᵐ p ∂χ, a p.1 = a p.2 ∧ u p.1 ≤ u p.2 := by
  have hs : ∀ᵐ p ∂π, p.1 ∈ A := ae_of_ae_map measurable_fst.aemeasurable (hπ.1.symm ▸ hμA)
  have ht : ∀ᵐ p ∂π, p.2 ∈ A := ae_of_ae_map measurable_snd.aemeasurable (hπ.2.symm ▸ hνA)
  have h : ∀ᵐ p ∂π, a p.1 = a p.2 ∧ u p.1 ≤ u p.2 := by
    filter_upwards [hs, ht, hcal] with p hp hq hc
    exact (horder p.1 hp p.2 hq).mpr hc
  exact h.filter_mono (ae_mono hχ)

end OTSelector.Reconstruction
