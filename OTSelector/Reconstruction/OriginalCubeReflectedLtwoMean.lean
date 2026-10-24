import OTSelector.Reconstruction.OriginalCubeTraceCompactnessCanonicalKernelLtwo
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedKernelMass
import Mathlib.MeasureTheory.Integral.Prod

/-! The genuine reflected scalar L2 response family is Bochner integrable with zero input mean. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- Genuine product integrability of the literal reflected response against every original
scalar L2 representative, using finite observation volume and compact input support. -/
theorem integrable_originalCubeReflectedInputResponse_mul_ltwo_prod
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (u : Lp ℝ 2 (volume.restrict (haarRootCube (Fin q) R))) :
    Integrable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦
      originalCubeReflectedInputResponse η R p.2 p.1 * u p.2)
      (volume.prod (volume.restrict (haarRootCube (Fin q) R))) := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (haarRootCube (Fin q) R)
  let K : Set (Fin q → ℝ) := haarRootCube (Fin q) (R + 1)
  let D : ℝ := ((3 : ℝ)^q + 1) * M
  have hD : 0 ≤ D := mul_nonneg (by positivity) hM
  have hu : Integrable u μ := (Lp.memLp u).integrable (by norm_num)
  have hK : Integrable (K.indicator (fun _ : Fin q → ℝ ↦ D)) volume := by
    apply (integrable_indicator_iff (show MeasurableSet K from measurableSet_Icc)).mpr
    exact integrableOn_const (μ := volume) (s := K) (C := D)
      (show IsCompact K from isCompact_Icc).measure_lt_top.ne
  have hmajor := hK.mul_prod hu.norm
  have hk : Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦
      originalCubeReflectedInputResponse η R p.2 p.1) :=
    (measurable_originalCubeReflectedInputResponse hη.measurable R).comp measurable_swap
  apply hmajor.mono' (hk.aestronglyMeasurable.mul (Lp.stronglyMeasurable u).comp_snd.aestronglyMeasurable)
  have hz : ∀ᵐ p : (Fin q → ℝ) × (Fin q → ℝ) ∂volume.prod μ,
      p.2 ∈ haarRootCube (Fin q) R :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hz] with p hp
  change ‖originalCubeReflectedInputResponse η R p.2 p.1 * u p.2‖ ≤
    K.indicator (fun _ : Fin q → ℝ ↦ D) p.1 * ‖u p.2‖
  by_cases hx : p.1 ∈ K
  · rw [indicator_of_mem hx, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs, Fintype.card_fin] using
        abs_originalCubeReflectedInputResponse_le hM hηM R p.2 p.1) (norm_nonneg _)
  · have hzero := originalCubeReflectedInputResponse_eq_zero_off_shell hηsupport hR hp
      (fun hs ↦ hx hs.1)
    simp only [hzero, zero_mul, norm_zero, indicator_of_notMem hx, le_refl]

/-- The actual scalar L2 response family is Bochner integrable over the full original
input Haar space, from its genuine compact support, strong measurability and norm bound. -/
theorem integrable_originalReflectedInputResponseLtwo
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {R : ℝ} (hR : 1 ≤ R) :
    Integrable (originalReflectedInputResponseLtwo hη hηsupport R) volume := by
  exact memLp_one_iff_integrable.mp <|
    (hasCompactSupport_originalReflectedInputResponseLtwo hη hηsupport hR).memLp_of_bound
      (stronglyMeasurable_originalReflectedInputResponseLtwo hη hηsupport R).aestronglyMeasurable
      ((((3 : ℝ)^q + 1) * M) * ((2 : ℝ)^q) ^ (1 / (2 : ℝ)))
      (ae_of_all _ (norm_originalReflectedInputResponseLtwo_le hη hηsupport hM hηM R))

/-- Unit mass and coordinate-evenness of the actual original kernel force the full-input
Bochner mean of the literal reflected L2 response family to vanish. -/
theorem integral_originalReflectedInputResponseLtwo_eq_zero
    (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηone : ∫ v, η v = 1)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {R : ℝ} (hR : 1 ≤ R) :
    (∫ x, originalReflectedInputResponseLtwo hη hηsupport R x) = 0 := by
  have hηcompact : HasCompactSupport η := by
    apply HasCompactSupport.intro (K := haarRootCube (Fin q) 1) isCompact_Icc
    intro z hz
    apply hηsupport
    by_contra! hn
    exact hz ((mem_haarRootCube_iff_norm_le (by norm_num) z).mpr hn.le)
  have hηI : Integrable η volume := hη.integrable_of_hasCompactSupport hηcompact
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _
    (integrable_originalReflectedInputResponseLtwo hη hηsupport hM hηM hR)
  intro u
  have hprod := integrable_originalCubeReflectedInputResponse_mul_ltwo_prod hη hηsupport hM hηM hR u
  calc
    _ = ∫ x, ∫ z in haarRootCube (Fin q) R,
        originalCubeReflectedInputResponse η R z x * u z := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x ↦ by
        change ⟪u, originalReflectedInputResponseLtwo hη hηsupport R x⟫_ℝ =
          ∫ z in haarRootCube (Fin q) R, originalCubeReflectedInputResponse η R z x * u z
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [originalReflectedInputResponseLtwo_ae hη hηsupport R x] with z hz
        simp only [hz, RCLike.inner_apply, conj_trivial])
    _ = ∫ z in haarRootCube (Fin q) R, ∫ x,
        originalCubeReflectedInputResponse η R z x * u z := integral_integral_swap hprod
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet (haarRootCube (Fin q) R) from measurableSet_Icc)] with z hz
      rw [integral_mul_const, integral_originalCubeReflectedInputResponse_input_eq_zero
        hηI hηone hηsupport hηeven hR hz, zero_mul]
      rfl

end OTSelector.Reconstruction
