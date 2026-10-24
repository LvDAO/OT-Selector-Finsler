import OTSelector.Reconstruction.FinslerPhysicalSceneProbeFreezing

/-!
# Signed real macro probes freeze uniformly under the original Haar cutoff

A normalized nonnegative compact source cutoff averages microscopic shifts.
Its convolution converges uniformly on all original macroscopic clocks.
-/
open Set Function Filter MeasureTheory
open scoped Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- The original compact Haar convolution uniformly recovers the signed real
probe, with no compactness or density premise on the varying transport plans. -/
theorem eventually_uniform_real_macro_probe_convolution_bound
    (g : C_c((ι → ℝ) × (ℝ × ℝ), ℝ))
    (η : C_c(ι → ℝ, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (hηmass : (∫ v, η v ∂volume) = 1)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (x : ι → ℝ) (st : ℝ × ℝ),
      |(∫ v, η v * g (x - (scale n)⁻¹ • v, st) ∂volume) - g (x, st)| ≤ ε := by
  obtain ⟨R, hR⟩ := η.hasCompactSupport.isCompact.isBounded.exists_norm_le
  have hiη : Integrable η volume := η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport
  filter_upwards [eventually_uniform_macro_probe_shift_bound g scale hscalePos hscale R hε]
    with n hn
  intro x st
  have hshift : Measurable (fun v : ι → ℝ ↦ g (x - (scale n)⁻¹ • v, st)) := by
    exact g.continuous.measurable.comp
      ((measurable_const.sub (measurable_const_smul _)).prodMk measurable_const)
  have hib : Integrable (fun v : ι → ℝ ↦ η v * g (x, st)) volume := hiη.mul_const _
  have his : Integrable (fun v : ι → ℝ ↦ η v * g (x - (scale n)⁻¹ • v, st)) volume := by
    simpa only [mul_comm] using hiη.bdd_mul hshift.aestronglyMeasurable
      (ae_of_all _ (fun v ↦ g.toBoundedContinuousFunction.norm_coe_le_norm _))
  have hbase : (∫ v, η v * g (x, st) ∂volume) = g (x, st) := by
    rw [integral_mul_const, hηmass, one_mul]
  rw [← hbase, ← integral_sub his hib]
  calc
    _ ≤ ∫ v, |η v * g (x - (scale n)⁻¹ • v, st) - η v * g (x, st)| ∂volume := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun v : ι → ℝ ↦ η v * g (x - (scale n)⁻¹ • v, st) - η v * g (x, st))
    _ ≤ ∫ v, η v * ε ∂volume := by
      apply integral_mono (his.sub hib).abs (hiη.mul_const ε)
      intro v
      change |η v * g (x - (scale n)⁻¹ • v, st) - η v * g (x, st)| ≤ η v * ε
      by_cases hv : v ∈ tsupport η
      · rw [← mul_sub, abs_mul, abs_of_nonneg (hη v)]
        exact mul_le_mul_of_nonneg_left (hn v (hR v hv) x st).le (hη v)
      · rw [image_eq_zero_of_notMem_tsupport hv]
        simp
    _ = ε := by rw [integral_mul_const, hηmass, one_mul]

end OTSelector.Reconstruction
