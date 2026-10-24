import OTSelector.Reconstruction.FinslerPhysicalSceneRootedReadoutConvolution

/-!
# Expected freezing error under the original changing experiment

Sample spaces, probability laws and transport plans may all change with the
sample size. Uniform compact-probe continuity controls the actual expectation.
-/
open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- A uniform microscopic shift bound controls every original subprobability
plan, without any measurable parametrization assumption on the family. -/
theorem lintegral_macro_probe_shift_le_of_uniform
    {Z : Type*} [MeasurableSpace Z]
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (η : (ι → ℝ) → ℝ≥0∞) (R a ε : ℝ)
    (hηsupport : ∀ v, R < ‖v‖ → η v = 0)
    (hshift : ∀ v : ι → ℝ, ‖v‖ ≤ R → ∀ (x : ι → ℝ) (st : ℝ × ℝ),
      |g (x - a • v, st) - g (x, st)| < ε)
    (Γ : Measure Z) (hΓ : Γ univ ≤ 1)
    (x : Z → (ι → ℝ)) (clock : Z → ℝ × ℝ) :
    (∫⁻ p, ∫⁻ v, η v * ENNReal.ofReal
      |g (x p - a • v, clock p) - g (x p, clock p)| ∂volume ∂Γ) ≤
        (∫⁻ v, η v ∂volume) * ENNReal.ofReal ε := by
  calc
    _ ≤ ∫⁻ _p, ∫⁻ v, η v * ENNReal.ofReal ε ∂volume ∂Γ := by
      apply lintegral_mono
      intro p
      apply lintegral_mono
      intro v
      by_cases hv : ‖v‖ ≤ R
      · simpa only [mul_comm] using mul_le_mul_right
          (ENNReal.ofReal_le_ofReal (hshift v hv (x p) (clock p)).le) (η v)
      · simp only [hηsupport v (lt_of_not_ge hv), zero_mul, le_refl]
    _ = ((∫⁻ v, η v ∂volume) * ENNReal.ofReal ε) * Γ univ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_const]
    _ ≤ _ := by
      simpa only [one_mul, mul_comm] using
        mul_le_mul_right hΓ ((∫⁻ v, η v ∂volume) * ENNReal.ofReal ε)

/-- Expected freezing error tends to zero on the same changing original
experiments, including changing finite sample spaces. No uniform integrability
or coupling across sample sizes is assumed. -/
theorem tendsto_expected_compact_macro_probe_shift_zero
    {Z : Type*} [MeasurableSpace Z]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (R : ∀ n, Measure (Ω n)) (hR : ∀ n, R n univ ≤ 1)
    (Γ : ∀ n, Ω n → Measure Z) (hΓ : ∀ n, ∀ᵐ ω ∂R n, Γ n ω univ ≤ 1)
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (η : C_c(ι → ℝ, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (x : ∀ n, Ω n → Z → (ι → ℝ)) (clock : ∀ n, Ω n → Z → ℝ × ℝ) :
    Tendsto (fun n ↦ ∫⁻ ω, ∫⁻ p, ∫⁻ v, ENNReal.ofReal (η v) * ENNReal.ofReal
      |g (x n ω p - (scale n)⁻¹ • v, clock n ω p) - g (x n ω p, clock n ω p)|
        ∂volume ∂Γ n ω ∂R n) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := η.hasCompactSupport.isCompact.isBounded.exists_norm_le
  have hs : ∀ v, B < ‖v‖ → ENNReal.ofReal (η v) = 0 := by
    intro v hv
    have hv' : v ∉ tsupport η := fun h ↦ (not_le_of_gt hv) (hB v h)
    simp only [image_eq_zero_of_notMem_tsupport hv', ENNReal.ofReal_zero]
  have hf : (∫⁻ v, ENNReal.ofReal (η v) ∂volume) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable η.continuous.aestronglyMeasurable
      (ae_of_all _ hη)).mpr
        (η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hf hε.ne'
  filter_upwards [eventually_uniform_macro_probe_shift_bound g scale hscalePos
    hscale B (show 0 < (δ : ℝ) from hδ)] with n hn
  have hb : (∫⁻ ω, ∫⁻ p, ∫⁻ v, ENNReal.ofReal (η v) * ENNReal.ofReal
      |g (x n ω p - (scale n)⁻¹ • v, clock n ω p) - g (x n ω p, clock n ω p)|
        ∂volume ∂Γ n ω ∂R n) ≤
          (∫⁻ v, ENNReal.ofReal (η v) ∂volume) * ENNReal.ofReal (δ : ℝ) := by
    calc
      _ ≤ ∫⁻ _ω, (∫⁻ v, ENNReal.ofReal (η v) ∂volume) *
          ENNReal.ofReal (δ : ℝ) ∂R n := by
        apply lintegral_mono_ae
        filter_upwards [hΓ n] with ω hω
        exact lintegral_macro_probe_shift_le_of_uniform g _ B (scale n)⁻¹
          (δ : ℝ) hs hn (Γ n ω) hω (x n ω) (clock n ω)
      _ ≤ _ := by
        rw [lintegral_const]
        simpa only [one_mul, mul_comm] using mul_le_mul_right (hR n)
          ((∫⁻ v, ENNReal.ofReal (η v) ∂volume) * ENNReal.ofReal (δ : ℝ))
  exact hb.trans (by simpa only [ENNReal.ofReal_coe_nnreal, mul_comm] using hδε.le)

/-- Actual normalized rooted readouts have vanishing expected freezing error
on their own original sample laws and arbitrary original root domains. -/
theorem tendsto_expected_physicalSceneMacroProbeFreezingError_zero
    {M : Type*} [MeasurableSpace M]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (R : ∀ n, Measure (Ω n)) (hR : ∀ n, R n univ ≤ 1)
    (Γ : ∀ n, Ω n → Measure (M × M)) [∀ n ω, SFinite (Γ n ω)]
    (hΓ : ∀ n, ∀ᵐ ω ∂R n, Γ n ω univ ≤ 1)
    (coord : ∀ n, Ω n → M → (ι → ℝ))
    (hcoord : ∀ n ω, Measurable (coord n ω))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (η : C_c(ι → ℝ, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (D : ∀ n, Ω n → Set (ι → ℝ)) :
    Tendsto (fun n ↦ ∫⁻ ω, ∫⁻ z, physicalSceneMacroProbeFreezingError
      (physicalSceneRootedPlan (Γ n ω) (coord n ω) u (N n) z) z (scale n) η g
        ∂cavityRootMeasure volume (D n ω) (N n) ∂R n) atTop (𝓝 0) := by
  have hh := tendsto_expected_compact_macro_probe_shift_zero R hR Γ hΓ g η hη
    scale hscalePos hscale (fun n ω p ↦ (scale n)⁻¹ • coord n ω p.1)
      (fun _ _ p ↦ (u p.1, u p.2))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hh ε hε] with n hn
  calc
    _ ≤ ∫⁻ ω, ∫⁻ z, physicalSceneMacroProbeFreezingError
        (physicalSceneRootedPlan (Γ n ω) (coord n ω) u (N n) z) z (scale n) η g
          ∂cavityRootMeasure volume univ (N n) ∂R n := by
      apply lintegral_mono
      intro ω
      have hm : cavityRootMeasure volume (D n ω) (N n) ≤
          cavityRootMeasure volume univ (N n) := by
        simp only [cavityRootMeasure, Measure.restrict_univ]
        intro A
        simp only [Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul_right (Measure.restrict_le_self A) _
      exact lintegral_mono' hm le_rfl
    _ = ∫⁻ ω, ∫⁻ p, ∫⁻ v, ENNReal.ofReal (η v) * ENNReal.ofReal
        |g ((scale n)⁻¹ • coord n ω p.1 - (scale n)⁻¹ • v, (u p.1, u p.2)) -
          g ((scale n)⁻¹ • coord n ω p.1, (u p.1, u p.2))|
            ∂volume ∂Γ n ω ∂R n := by
      apply lintegral_congr
      intro ω
      exact lintegral_physicalSceneMacroProbeFreezingError_eq (Γ n ω) (coord n ω)
        (hcoord n ω) u hu (N n) (hN n) (scale n) η g
    _ ≤ ε := hn

end OTSelector.Reconstruction
