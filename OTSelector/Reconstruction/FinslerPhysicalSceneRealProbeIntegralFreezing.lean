import OTSelector.Reconstruction.FinslerPhysicalSceneUniformRealProbeFreezing
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The original real probe integral freezes uniformly over all finite plans

Uniform signed convolution recovery is independent of the plan. The same
bound therefore survives changing original probability experiments.
-/
open Set Function Filter MeasureTheory
open scoped Topology CompactlySupported ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι Z : Type*} [Fintype ι] [MeasurableSpace Z]
local notation "V" => (ι → ℝ)

/-- Uniform real convolution recovery controls all finite original plans at
once; only their actual mass multiplies the error. -/
theorem eventually_uniform_plan_real_macro_probe_convolution_bound
    (g : C_c(V × (ℝ × ℝ), ℝ))
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v) (hηmass : (∫ v, η v ∂volume) = 1)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (π : Measure Z) [IsFiniteMeasure π]
      (x : Z → V), Measurable x → ∀ (clock : Z → ℝ × ℝ), Measurable clock →
      |(∫ p, ∫ v, η v * g (x p - (scale n)⁻¹ • v, clock p) ∂volume ∂π) -
        ∫ p, g (x p, clock p) ∂π| ≤ ε * π.real univ := by
  filter_upwards [eventually_uniform_real_macro_probe_convolution_bound g η hη hηmass
    scale hscalePos hscale hε] with n hn
  intro π _ x hx clock hclock
  let f : Z → ℝ := fun p ↦ ∫ v, η v * g (x p - (scale n)⁻¹ • v, clock p) ∂volume
  let b : Z → ℝ := fun p ↦ g (x p, clock p)
  have hb : Measurable b := g.continuous.measurable.comp (hx.prodMk hclock)
  have hj : Measurable (fun w : Z × V ↦
      η w.2 * g (x w.1 - (scale n)⁻¹ • w.2, clock w.1)) :=
    (η.continuous.measurable.comp measurable_snd).mul
      (g.continuous.measurable.comp
        (((hx.comp measurable_fst).sub ((measurable_const_smul _).comp measurable_snd)).prodMk
          (hclock.comp measurable_fst)))
  have hf : StronglyMeasurable f := hj.stronglyMeasurable.integral_prod_right'
  have hib : Integrable b π := Integrable.of_bound hb.aestronglyMeasurable
    ‖g.toBoundedContinuousFunction‖ (ae_of_all _ fun p ↦
      g.toBoundedContinuousFunction.norm_coe_le_norm (x p, clock p))
  have hid : Integrable (fun p ↦ f p - b p) π := Integrable.of_bound
    (hf.sub hb.stronglyMeasurable).aestronglyMeasurable ε
      (ae_of_all _ fun p ↦ by simpa only [Real.norm_eq_abs] using hn (x p) (clock p))
  have hif : Integrable f π :=
    (hid.add hib).congr (ae_of_all _ fun p ↦ sub_add_cancel (f p) (b p))
  change |(∫ p, f p ∂π) - ∫ p, b p ∂π| ≤ _
  rw [← integral_sub hif hib]
  simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const
    (μ := π) (f := fun p ↦ f p - b p)
      (ae_of_all _ fun p ↦ by simpa only [Real.norm_eq_abs] using hn (x p) (clock p))

/-- The real original probe and its same-plan compact Haar convolution have
vanishing expected absolute difference on changing original experiments. -/
theorem tendsto_expected_real_macro_probe_convolution_difference_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (R : ∀ n, Measure (Ω n)) (hR : ∀ n, R n univ ≤ 1)
    (π : ∀ n, Ω n → Measure Z) [∀ n ω, IsFiniteMeasure (π n ω)]
    (hπ : ∀ n, ∀ᵐ ω ∂R n, π n ω univ ≤ 1)
    (x : ∀ n, Ω n → Z → V) (hx : ∀ n ω, Measurable (x n ω))
    (clock : ∀ n, Ω n → Z → ℝ × ℝ) (hclock : ∀ n ω, Measurable (clock n ω))
    (g : C_c(V × (ℝ × ℝ), ℝ))
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v) (hηmass : (∫ v, η v ∂volume) = 1)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal
      |(∫ p, ∫ v, η v * g (x n ω p - (scale n)⁻¹ • v, clock n ω p) ∂volume ∂π n ω) -
        ∫ p, g (x n ω p, clock n ω p) ∂π n ω| ∂R n) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (by simp : (1 : ℝ≥0∞) ≠ ∞) hε.ne'
  filter_upwards [eventually_uniform_plan_real_macro_probe_convolution_bound
    (Z := Z) g η hη hηmass scale hscalePos hscale
      (show 0 < (δ : ℝ) from hδ)] with n hn
  calc
    _ ≤ ∫⁻ _ω, ENNReal.ofReal (δ : ℝ) ∂R n := by
      apply lintegral_mono_ae
      filter_upwards [hπ n] with ω hω
      apply ENNReal.ofReal_le_ofReal
      have hb := hn (π n ω) (x n ω) (hx n ω) (clock n ω) (hclock n ω)
      have hm : (π n ω).real univ ≤ 1 := by
        simpa only [measureReal_def, ENNReal.toReal_one] using
          ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hω
      exact hb.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hm δ.coe_nonneg)
    _ ≤ ENNReal.ofReal (δ : ℝ) := by
      rw [lintegral_const]
      simpa only [one_mul, mul_one, mul_comm] using mul_le_mul_right (hR n) (ENNReal.ofReal (δ : ℝ))
    _ ≤ ε := by simpa only [mul_one, ENNReal.ofReal_coe_nnreal] using hδε.le

end OTSelector.Reconstruction
