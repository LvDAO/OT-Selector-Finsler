import OTSelector.Reconstruction.FinslerPhysicalSceneMacroProbeConvolution
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! Uniform microscopic shifts freeze the actual macroscopic clock probe.
The bound is uniform in the original edge and thus permits changing plans. -/
open Set Function Filter MeasureTheory
open scoped Topology CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/-- A compact macroscopic clock probe is uniformly insensitive to bounded
microscopic source offsets as the original physical scale diverges. -/
theorem eventually_uniform_macro_probe_shift_bound
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : ι → ℝ, ‖v‖ ≤ R → ∀ (x : ι → ℝ) (st : ℝ × ℝ),
      |g (x - (scale n)⁻¹ • v, st) - g (x, st)| < ε := by
  obtain ⟨δ, hδ, hg⟩ := Metric.uniformContinuous_iff.mp
    (CompactlySupportedContinuousMapClass.uniformContinuous g) ε hε
  have hi : Tendsto (fun n ↦ (scale n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hscale
  have hR : Tendsto (fun n ↦ R * (scale n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hi
  filter_upwards [(tendsto_order.mp hR).2 δ hδ] with n hn
  intro v hv x st
  have hnorm : ‖(scale n)⁻¹ • v‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hscalePos n))]
    calc
      (scale n)⁻¹ * ‖v‖ ≤ (scale n)⁻¹ * R :=
        mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (hscalePos n).le)
      _ = R * (scale n)⁻¹ := mul_comm _ _
      _ < δ := hn
  have hd : dist (x - (scale n)⁻¹ • v, st) (x, st) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm]
    simpa only [sub_right_comm, sub_self, zero_sub, norm_neg] using hnorm
  simpa only [Real.dist_eq] using hg hd

/-- The original plans may change with the scale. Their total mass alone
controls the compactly localized freezing error, uniformly in all clocks. -/
theorem eventually_lintegral_macro_probe_shift_bound
    {Z : Type*} [MeasurableSpace Z]
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (η : (ι → ℝ) → ℝ≥0∞) (R : ℝ)
    (hηsupport : ∀ v, R < ‖v‖ → η v = 0)
    (Γ : ℕ → Measure Z) (hΓ : ∀ n, Γ n univ ≤ 1)
    (x : ℕ → Z → (ι → ℝ)) (clock : Z → ℝ × ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (∫⁻ p, ∫⁻ v, η v * ENNReal.ofReal
        |g (x n p - (scale n)⁻¹ • v, clock p) - g (x n p, clock p)|
          ∂volume ∂Γ n) ≤ (∫⁻ v, η v ∂volume) * ENNReal.ofReal ε := by
  filter_upwards [eventually_uniform_macro_probe_shift_bound g scale hscalePos
    hscale R hε] with n hn
  calc
    _ ≤ ∫⁻ _p, ∫⁻ v, η v * ENNReal.ofReal ε ∂volume ∂Γ n := by
      apply lintegral_mono
      intro p
      apply lintegral_mono
      intro v
      by_cases hv : ‖v‖ ≤ R
      · simpa only [mul_comm] using mul_le_mul_right
          (ENNReal.ofReal_le_ofReal (hn v hv (x n p) (clock p)).le) (η v)
      · simp only [hηsupport v (lt_of_not_ge hv), zero_mul, le_refl]
    _ = ((∫⁻ v, η v ∂volume) * ENNReal.ofReal ε) * Γ n univ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_const]
    _ ≤ _ := by
      simpa only [one_mul, mul_comm] using
        mul_le_mul_right (hΓ n) ((∫⁻ v, η v ∂volume) * ENNReal.ofReal ε)

/-- Finite localized Haar mass upgrades the uniform estimate to vanishing
error for any sequence of original subprobability plans. -/
theorem tendsto_lintegral_macro_probe_shift_zero
    {Z : Type*} [MeasurableSpace Z]
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (η : (ι → ℝ) → ℝ≥0∞) (R : ℝ)
    (hηsupport : ∀ v, R < ‖v‖ → η v = 0)
    (hηfinite : (∫⁻ v, η v ∂volume) ≠ ∞)
    (Γ : ℕ → Measure Z) (hΓ : ∀ n, Γ n univ ≤ 1)
    (x : ℕ → Z → (ι → ℝ)) (clock : Z → ℝ × ℝ) :
    Tendsto (fun n ↦ ∫⁻ p, ∫⁻ v, η v * ENNReal.ofReal
      |g (x n p - (scale n)⁻¹ • v, clock p) - g (x n p, clock p)|
        ∂volume ∂Γ n) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hηfinite hε.ne'
  filter_upwards [eventually_lintegral_macro_probe_shift_bound g scale hscalePos
    hscale η R hηsupport Γ hΓ x clock (show 0 < (δ : ℝ) from hδ)] with n hn
  exact hn.trans (by simpa only [ENNReal.ofReal_coe_nnreal, mul_comm] using hδε.le)

/-- The source cutoff's support radius and finite Haar mass follow internally
from compact support. No compactness restriction on the original plans is used. -/
theorem tendsto_lintegral_compact_macro_probe_shift_zero
    {Z : Type*} [MeasurableSpace Z]
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (η : C_c(ι → ℝ, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (Γ : ℕ → Measure Z) (hΓ : ∀ n, Γ n univ ≤ 1)
    (x : ℕ → Z → (ι → ℝ)) (clock : Z → ℝ × ℝ) :
    Tendsto (fun n ↦ ∫⁻ p, ∫⁻ v, ENNReal.ofReal (η v) * ENNReal.ofReal
      |g (x n p - (scale n)⁻¹ • v, clock p) - g (x n p, clock p)|
        ∂volume ∂Γ n) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := η.hasCompactSupport.isCompact.isBounded.exists_norm_le
  have hs : ∀ v, R < ‖v‖ → ENNReal.ofReal (η v) = 0 := by
    intro v hv
    have hv' : v ∉ tsupport η := fun h ↦ (not_le_of_gt hv) (hR v h)
    simp only [image_eq_zero_of_notMem_tsupport hv', ENNReal.ofReal_zero]
  have hf : (∫⁻ v, ENNReal.ofReal (η v) ∂volume) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable η.continuous.aestronglyMeasurable
      (ae_of_all _ hη)).mpr
        (η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport)
  exact tendsto_lintegral_macro_probe_shift_zero g scale hscalePos hscale
    (fun v ↦ ENNReal.ofReal (η v)) R hs hf Γ hΓ x clock

end OTSelector.Reconstruction
