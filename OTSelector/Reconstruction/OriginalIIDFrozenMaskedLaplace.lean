import OTSelector.MeasureTheory.ScaledDensityMask
import OTSelector.Reconstruction.OriginalIIDLocalIntensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Frozen microscopic Laplace limits with the original endpoint masks

Density-point boundary loss and exact Haar scaling yield the frozen endpoint
Laplace limit on one full-measure root set. That set supports every probability
mark law and compact spatial test, including mark laws and tests varying with
the root, without an uncountable intersection of exceptional sets.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- A bounded measurable test with finite spatial support is integrable against
coordinate volume times the unchanged original probability clock law. -/
theorem original_integrable_of_finite_spatial_support
    {q : ℕ} (α : Measure ℝ) [IsProbabilityMeasure α]
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : Measurable f) (hb : ∀ p, |f p| ≤ 1)
    {B : Set (Fin q → ℝ)} (hB : volume B < ⊤)
    (hsupp : ∀ p, p.1 ∉ B → f p = 0) :
    Integrable f ((volume : Measure (Fin q → ℝ)).prod α) := by
  let μ := (volume : Measure (Fin q → ℝ)).prod α
  have hfinite : μ (B ×ˢ (univ : Set ℝ)) < ⊤ := by
    simpa only [μ, Measure.prod_prod, measure_univ, mul_one] using hB
  have : IsFiniteMeasure (μ.restrict (B ×ˢ (univ : Set ℝ))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  apply (integrableOn_iff_integrable_of_support_subset (s := B ×ˢ (univ : Set ℝ)) ?_).mp
  · exact Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ hb)
  · intro p hp
    refine ⟨?_, mem_univ _⟩
    by_contra h
    exact hp (hsupp p h)

/-- Removing an endpoint's retained spatial mask costs at most the missing
spatial volume inside the test window. Only this endpoint's unchanged clock
probability law is used. -/
theorem original_abs_integral_spatial_mask_sub_le_missing_volume
    {q : ℕ} (α : Measure ℝ) [IsProbabilityMeasure α]
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : Measurable f) (hb : ∀ p, |f p| ≤ 1)
    {B K : Set (Fin q → ℝ)} (hBfinite : volume B < ⊤)
    (hK : MeasurableSet K) (hsupp : ∀ p, p.1 ∉ B → f p = 0) :
    |(∫ p in {p | p.1 ∈ K}, f p ∂((volume : Measure (Fin q → ℝ)).prod α)) -
        ∫ p, f p ∂((volume : Measure (Fin q → ℝ)).prod α)| ≤
      (volume (B \ K)).toReal := by
  let μ := (volume : Measure (Fin q → ℝ)).prod α
  let A : Set ((Fin q → ℝ) × ℝ) := {p | p.1 ∈ K}
  let missing : Set ((Fin q → ℝ) × ℝ) := (B \ K) ×ˢ univ
  have hA : MeasurableSet A := hK.preimage measurable_fst
  have hi : Integrable f μ := original_integrable_of_finite_spatial_support α hf hb hBfinite hsupp
  have hsub : missing ⊆ Aᶜ := fun p hp ↦ hp.1.2
  have hlocal : (∫ p in missing, f p ∂μ) = ∫ p in Aᶜ, f p ∂μ := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA.compl hsub
    intro p hp
    apply hsupp
    intro hpB
    exact hp.2 ⟨⟨hpB, hp.1⟩, mem_univ _⟩
  have hfinite : μ missing < ⊤ := by
    simp only [μ, missing, Measure.prod_prod, measure_univ, mul_one]
    exact lt_of_le_of_lt (measure_mono sdiff_subset) hBfinite
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := μ)
    (f := f) (C := 1) hfinite (fun p _ ↦ hb p)
  have hcomp := setIntegral_compl hA hi
  rw [← hlocal] at hcomp
  rw [abs_sub_comm, ← hcomp]
  simpa only [Real.norm_eq_abs, one_mul, μ, missing, measureReal_def,
    Measure.prod_prod, measure_univ, mul_one] using hbound

/-- At a root with vanishing scaled missing spatial volume, every eligible
original endpoint clock law and Laplace test has the frozen microscopic limit.
The hypothesis is the geometric density-point property, not a test limit. -/
theorem original_tendsto_scaled_masked_frozen_laplace_defect_at
    {q : ℕ} {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (H : (Fin q → ℝ) × ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ p, 0 ≤ H p)
    {R : ℝ} (hsupport : ∀ p, p.1 ∉ closedBall 0 R → H p = 0)
    (z : Fin q → ℝ)
    (hmask : Tendsto (fun n ↦ s n ^ q *
      (volume (closedBall z (R / s n) \ K)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n ↦ s n ^ q *
        ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K},
          1 - Real.exp (-H (s n • (p.1 - z), p.2))
          ∂((volume : Measure (Fin q → ℝ)).prod α)) atTop
        (𝓝 (∫ p, 1 - Real.exp (-H p)
          ∂((volume : Measure (Fin q → ℝ)).prod α))) := by
  let μ := (volume : Measure (Fin q → ℝ)).prod α
  let f : ℕ → (Fin q → ℝ) × ℝ → ℝ :=
    fun n p ↦ 1 - Real.exp (-H (s n • (p.1 - z), p.2))
  have hf n : Measurable (f n) := by
    apply measurable_const.sub
    apply Measurable.exp
    apply Measurable.neg
    apply hH.comp
    fun_prop
  have hb n p : |f n p| ≤ 1 :=
    original_laplace_defect_abs_le_one (fun p ↦ hH0 (s n • (p.1 - z), p.2)) p
  have hwindow n p (hp : p.1 ∉ closedBall z (R / s n)) : f n p = 0 := by
    have hout : s n • (p.1 - z) ∉ closedBall 0 R := by
      intro hscaled
      apply hp
      rw [mem_closedBall, dist_eq_norm] at hscaled ⊢
      rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (hs n)] at hscaled
      exact (le_div_iff₀ (hs n)).mpr (by nlinarith)
    simp only [f, hsupport (s n • (p.1 - z), p.2) hout, neg_zero, Real.exp_zero, sub_self]
  have hfull n : s n ^ q * ∫ p, f n p ∂μ =
      ∫ p, 1 - Real.exp (-H p) ∂μ := by
    have h := original_scale_pow_mul_frozen_haar_laplace_defect
      (volume : Measure (Fin q → ℝ)) (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ))
      (c := 1) (by simp) (hs n) (s n • z) α 1 H hH
    simpa only [ContinuousLinearEquiv.refl_apply, one_smul, one_mul, ENNReal.toReal_one,
      smul_sub, f, μ] using h
  have hbound n : |s n ^ q * (∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K}, f n p ∂μ) -
      ∫ p, 1 - Real.exp (-H p) ∂μ| ≤
        s n ^ q * (volume (closedBall z (R / s n) \ K)).toReal := by
    rw [← hfull n, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (hs n).le q)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (hs n).le q)
    exact original_abs_integral_spatial_mask_sub_le_missing_volume α (hf n) (hb n)
      measure_closedBall_lt_top hK (hwindow n)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hmask
  simpa only [Real.norm_eq_abs] using hbound n

/-- ONE full-measure set of roots works for EVERY probability mark law and
every eligible test. The exceptional set depends only on the spatial retained
set, scale sequence and support radius, so original conditional clocks may vary
with the root without an uncountable intersection of exceptional sets. -/
theorem original_ae_forall_tendsto_scaled_masked_frozen_laplace_defect
    {q : ℕ} {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ z ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ (α : Measure ℝ), ∀ (_ : IsProbabilityMeasure α),
      ∀ (H : (Fin q → ℝ) × ℝ → ℝ), Measurable H → (∀ p, 0 ≤ H p) →
        (∀ p, p.1 ∉ closedBall 0 R → H p = 0) →
      Tendsto (fun n ↦ s n ^ q *
        ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K},
          1 - Real.exp (-H (s n • (p.1 - z), p.2))
          ∂((volume : Measure (Fin q → ℝ)).prod α)) atTop
        (𝓝 (∫ p, 1 - Real.exp (-H p)
          ∂((volume : Measure (Fin q → ℝ)).prod α))) := by
  filter_upwards [OTSelector.Probability.ae_tendsto_scaled_missing_volume hK s hs hlarge hR]
    with z hmask
  intro α hα H hH hH0 hsupport
  have : IsProbabilityMeasure α := hα
  exact original_tendsto_scaled_masked_frozen_laplace_defect_at
    hK s hs α H hH hH0 hsupport z hmask

/-- Frozen original endpoint laws have their full-space Laplace defect after
microscopic scaling at almost every retained root. Measurable retained sets may
have empty interior. This is a consequence of Lebesgue density and the exact
Haar Jacobian; the limit is not an input assumption. -/
theorem original_ae_tendsto_scaled_masked_frozen_laplace_defect
    {q : ℕ} {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (H : (Fin q → ℝ) × ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ p, 0 ≤ H p)
    {R : ℝ} (hR : 0 < R)
    (hsupport : ∀ p, p.1 ∉ closedBall 0 R → H p = 0) :
    ∀ᵐ z ∂(volume : Measure (Fin q → ℝ)).restrict K,
      Tendsto (fun n ↦ s n ^ q *
        ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K},
          1 - Real.exp (-H (s n • (p.1 - z), p.2))
          ∂((volume : Measure (Fin q → ℝ)).prod α)) atTop
        (𝓝 (∫ p, 1 - Real.exp (-H p)
          ∂((volume : Measure (Fin q → ℝ)).prod α))) := by
  filter_upwards [original_ae_forall_tendsto_scaled_masked_frozen_laplace_defect
    hK s hs hlarge hR] with z hz
  exact hz α inferInstance H hH hH0 hsupport

/-- A root's frozen intensity is retained as a multiplicative factor. In the
physical seed application this is the full coordinate intensity, including the
native-Haar basis Jacobian; the original endpoint clock law remains unchanged. -/
theorem original_ae_tendsto_scaled_masked_frozen_intensity_laplace_defect
    {q : ℕ} {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (α : Measure ℝ) [IsProbabilityMeasure α] (Θ : (Fin q → ℝ) → ℝ≥0)
    (H : (Fin q → ℝ) × ℝ → ℝ) (hH : Measurable H) (hH0 : ∀ p, 0 ≤ H p)
    {R : ℝ} (hR : 0 < R)
    (hsupport : ∀ p, p.1 ∉ closedBall 0 R → H p = 0) :
    ∀ᵐ z ∂(volume : Measure (Fin q → ℝ)).restrict K,
      Tendsto (fun n ↦ s n ^ q *
        ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K},
          1 - Real.exp (-H (s n • (p.1 - z), p.2))
          ∂(Θ z • (volume : Measure (Fin q → ℝ)).prod α)) atTop
        (𝓝 ((Θ z : ℝ) * ∫ p, 1 - Real.exp (-H p)
          ∂((volume : Measure (Fin q → ℝ)).prod α))) := by
  filter_upwards [original_ae_tendsto_scaled_masked_frozen_laplace_defect
    hK s hs hlarge α H hH hH0 hR hsupport] with z hz
  have h := hz.const_mul (Θ z : ℝ)
  convert h using 1
  ext n
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  ring

/-- The original conditional mark law, frozen intensity and compact-spatial
test may ALL vary with the root. A single geometric density-point exceptional
set serves every root-dependent choice, with no joint continuity or countable
range assumption on the conditional mark family. -/
theorem original_ae_tendsto_scaled_masked_frozen_variable_laplace_defect
    {q : ℕ} {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (α : (Fin q → ℝ) → Measure ℝ) [∀ z, IsProbabilityMeasure (α z)]
    (Θ : (Fin q → ℝ) → ℝ≥0)
    (H : (Fin q → ℝ) → (Fin q → ℝ) × ℝ → ℝ)
    (hH : ∀ z, Measurable (H z)) (hH0 : ∀ z p, 0 ≤ H z p)
    {R : ℝ} (hR : 0 < R)
    (hsupport : ∀ z p, p.1 ∉ closedBall 0 R → H z p = 0) :
    ∀ᵐ z ∂(volume : Measure (Fin q → ℝ)).restrict K,
      Tendsto (fun n ↦ s n ^ q *
        ∫ p in {p : (Fin q → ℝ) × ℝ | p.1 ∈ K},
          1 - Real.exp (-H z (s n • (p.1 - z), p.2))
          ∂(Θ z • (volume : Measure (Fin q → ℝ)).prod (α z))) atTop
        (𝓝 ((Θ z : ℝ) * ∫ p, 1 - Real.exp (-H z p)
          ∂((volume : Measure (Fin q → ℝ)).prod (α z)))) := by
  filter_upwards [original_ae_forall_tendsto_scaled_masked_frozen_laplace_defect
    hK s hs hlarge hR] with z hz
  have h := (hz (α z) inferInstance (H z) (hH z) (hH0 z) (hsupport z)).const_mul (Θ z : ℝ)
  convert h using 1
  ext n
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  ring

end OTSelector.Reconstruction

