import OTSelector.Reconstruction.OriginalIIDActualKineticFinite
import OTSelector.Reconstruction.OriginalIIDRootMassRecovery

/-! Full root integrals from the stored losses of nonnested finite original cores. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Finite disjoint root cores with vanishing omitted mass preserve one lower-integral
budget. Core families may change arbitrarily: clipping is fixed until the loss vanishes. -/
theorem lintegral_le_of_finite_root_core_losses
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : AEMeasurable f μ)
    (I : ℕ → Type*) [∀ n, Fintype (I n)]
    (cells : ∀ n, I n → Set Ω) (hmeas : ∀ n i, MeasurableSet (cells n i))
    (hdisjoint : ∀ n, Pairwise (fun i j ↦ Disjoint (cells n i) (cells n j)))
    (hcover : Tendsto (fun n ↦ μ (⋃ i, cells n i)ᶜ) atTop (𝓝 0))
    (C : ℝ≥0∞) (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, (∑ i, ∫⁻ x in cells n i, f x ∂μ) ≤ C+error n) :
    (∫⁻ x, f x ∂μ) ≤ C := by
  apply lintegral_le_of_uniform_natural_clipped_bounds μ f hf C
  intro k
  let B : ℝ≥0∞ := k
  have hB : B ≠ ⊤ := ENNReal.natCast_ne_top k
  have hmissing : Tendsto (fun n ↦ B*μ (⋃ i, cells n i)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hcover (Or.inr hB)
  have hlim : Tendsto (fun n ↦ C+error n+B*μ (⋃ i, cells n i)ᶜ) atTop (𝓝 C) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herror).add hmissing
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [hbound] with n hn
  have hU : MeasurableSet (⋃ i, cells n i) := MeasurableSet.iUnion (hmeas n)
  calc
    _ = (∫⁻ x in ⋃ i, cells n i, min B (f x) ∂μ) +
        ∫⁻ x in (⋃ i, cells n i)ᶜ, min B (f x) ∂μ :=
      (lintegral_add_compl (fun x ↦ min B (f x)) hU).symm
    _ ≤ (∑ i, ∫⁻ x in cells n i, f x ∂μ) + B*μ (⋃ i, cells n i)ᶜ := by
      apply add_le_add
      · rw [lintegral_iUnion (hmeas n) (hdisjoint n), tsum_fintype]
        exact Finset.sum_le_sum (fun i _ ↦ lintegral_mono (fun x ↦ min_le_right B (f x)))
      · exact (lintegral_mono (fun x ↦ min_le_left B (f x))).trans_eq (by simp)
    _ ≤ _ := add_le_add hn le_rfl

/-- A nonnegative real root field inherits global integrability and its actual real
mean bound from those finite original core integrals, without assuming a global budget. -/
theorem integrable_nonneg_of_finite_root_core_losses
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → ℝ) (hp : AEStronglyMeasurable p μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ p x)
    (I : ℕ → Type*) [∀ n, Fintype (I n)]
    (cells : ∀ n, I n → Set Ω) (hmeas : ∀ n i, MeasurableSet (cells n i))
    (hdisjoint : ∀ n, Pairwise (fun i j ↦ Disjoint (cells n i) (cells n j)))
    (hcover : Tendsto (fun n ↦ μ (⋃ i, cells n i)ᶜ) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      (∑ i, ∫⁻ x in cells n i, ENNReal.ofReal (p x) ∂μ) ≤ C+error n) :
    Integrable p μ ∧ (∫ x, p x ∂μ) ≤ C.toReal := by
  have hbudget := lintegral_le_of_finite_root_core_losses μ (fun x ↦ ENNReal.ofReal (p x))
    hp.aemeasurable.ennreal_ofReal I cells hmeas hdisjoint hcover C error herror hbound
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hp hnonneg).mp
    (ne_top_of_le_ne_top hC hbudget), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hp]
  exact ENNReal.toReal_mono hC hbudget

/-- An integrable signed root observable is recovered by nonnested finite disjoint
cores whenever their actual omitted mass vanishes. No pointwise coverage is needed. -/
theorem tendsto_finite_root_core_integrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → ℝ) (hp : Integrable p μ)
    (I : ℕ → Type*) [∀ n, Fintype (I n)]
    (cells : ∀ n, I n → Set Ω) (hmeas : ∀ n i, MeasurableSet (cells n i))
    (hdisjoint : ∀ n, Pairwise (fun i j ↦ Disjoint (cells n i) (cells n j)))
    (hcover : Tendsto (fun n ↦ μ (⋃ i, cells n i)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i, ∫ x in cells n i, p x ∂μ) atTop (𝓝 (∫ x, p x ∂μ)) := by
  have hm := hp.tendsto_setIntegral_nhds_zero hcover
  have hl := (tendsto_const_nhds (x := ∫ x, p x ∂μ)).sub hm
  simp only [sub_zero] at hl
  apply hl.congr'
  apply Eventually.of_forall
  intro n
  have hU : MeasurableSet (⋃ i, cells n i) := MeasurableSet.iUnion (hmeas n)
  have hsplit := integral_add_compl hU hp
  have hsum : (∫ x in ⋃ i, cells n i, p x ∂μ) = ∑ i, ∫ x in cells n i, p x ∂μ :=
    integral_iUnion_fintype (hmeas n) (hdisjoint n) (fun i ↦ hp.integrableOn)
  linarith

end OTSelector.Reconstruction
