import OTSelector.Reconstruction.OriginalCubeTraceCompactnessStationaryBound

/-! Homogeneous bounds in the original gradient energy for all smooth face tests. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Scalar normalization preserves the actual coordinate energy quadratically. -/
theorem boxCollarGradientEnergy_const_mul
    {q : ℕ} {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℝ) (a b : Fin q → ℝ) (h : ℝ) :
    boxCollarGradientEnergy (fun p ↦ c * f p) a b h =
      c^2 * boxCollarGradientEnergy f a b h := by
  have hd (p : (Fin q → ℝ) × ℝ) :
      fderiv ℝ (fun z ↦ c * f z) p = c • fderiv ℝ f p :=
    fderiv_const_mul (hf.differentiable (by norm_num) p) c
  simp only [boxCollarGradientEnergy, hd, smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul, Finset.mul_sum, mul_add]

/-- The actual common bound controls every smooth zero-mean test with its
original gradient energy, including tests whose energy is zero. -/
theorem smooth_trace_pairing_sq_le_originalTraceDualInfBound_mul_energy
    {q : ℕ} {g : (Fin q → ℝ) → ℝ}
    (hg : MemLp g 2 (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1))))
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hmean : (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1,
      f p) = 0) :
    (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g y * f (y, 0))^2 ≤
      originalTraceDualInfBound g * boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 := by
  let E := boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1
  have hE : 0 ≤ E := boxCollarGradientEnergy_nonneg f _ _ _
  by_cases hE0 : E = 0
  · have hface := smooth_unit_product_face_trace_sq_le_of_mean_zero hf hmean
    change (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), (f (y, 0))^2) ≤
      ((q + 2 : ℕ) : ℝ) * E at hface
    rw [hE0, mul_zero] at hface
    have htrace : MemLp (fun y ↦ f (y, 0)) 2
        (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1))) := by
      apply (memLp_two_iff_integrable_sq
        (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).2
      exact ((hf.continuous.comp (continuous_id.prodMk continuous_const)).pow 2).continuousOn.integrableOn_Icc
    have hcs := integral_mul_sq_le_of_memLp_two hg htrace
    change _ ≤ originalTraceDualInfBound g * E
    rw [hE0, mul_zero]
    exact hcs.trans (mul_nonpos_of_nonneg_of_nonpos
      (integral_nonneg (fun _ ↦ sq_nonneg _)) hface)
  · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hE0)
    let c := (Real.sqrt E)⁻¹
    have hc : c^2 * E = 1 := by
      dsimp only [c]
      calc
        _ = (Real.sqrt E)⁻¹^2 * (Real.sqrt E)^2 := by rw [Real.sq_sqrt hE]
        _ = 1 := by field_simp [(Real.sqrt_pos.mpr hEpos).ne']
    have hfc : ContDiff ℝ 1 (fun p ↦ c * f p) := contDiff_const.mul hf
    have hmc : (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1,
        c * f p) = 0 := by rw [integral_const_mul, hmean, mul_zero]
    have hec : boxCollarGradientEnergy (fun p ↦ c * f p) (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1 := by
      rw [boxCollarGradientEnergy_const_mul hf]
      exact hc.le
    have hn : (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g y * (c * f (y, 0)))^2 ≤
        originalTraceDualInfBound g :=
      le_ciInf (fun n ↦ smooth_unit_energy_trace_pairing_sq_le_originalDyadicTraceDualBound
        hg hfc hmc hec n)
    have hi : (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g y * (c * f (y, 0))) =
        c * (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g y * f (y, 0)) := by
      simp_rw [mul_left_comm (g _) c]
      exact integral_const_mul c _
    rw [hi] at hn
    change _ ≤ originalTraceDualInfBound g * E
    calc
      _ = (c^2 * E) * (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g y * f (y, 0))^2 := by
        rw [hc, one_mul]
      _ = (c * (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g y * f (y, 0)))^2 * E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hn hE

/-- The actual stationary common random bound supplies the homogeneous
square-root energy inequality for all smooth zero-mean tests simultaneously. -/
theorem ae_all_smooth_trace_pairing_abs_le_stationaryCubeTraceDualBound_sqrt_energy
    {q : ℕ} {G Ω : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : G → Ω → Ω) (hT : ∀ a, MeasurePreserving (T a) μ μ)
    (hzero : T 0 = id) (haddT : ∀ a b ω, T a (T b ω) = T (a+b) ω)
    (L : (Fin q → ℝ) →ₗ[ℝ] G)
    (hTjoint : Measurable (fun p : G × Ω ↦ T p.1 p.2))
    (offset : ℝ → G) (x : Lp ℝ 2 μ) (R : ℝ) :
    ∀ᵐ ω ∂μ, ∀ (f : (Fin q → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1, f p) = 0 →
      |∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
        stationaryScalarFaceReadout μ T L offset x R y ω * f (y, 0)| ≤
          Real.sqrt (stationaryCubeTraceDualBound μ T L offset x R ω) *
            Real.sqrt (boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1) := by
  have hm := (measurable_stationaryScalarFaceReadout μ T L hTjoint offset x R).comp measurable_swap
  have hprod := (integrable_sq_stationaryScalarFaceReadout_prod μ T hT hzero haddT L hTjoint
    offset x R (A := Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1))
    isCompact_Icc.measure_lt_top.ne).swap
  filter_upwards [hprod.prod_right_ae] with ω hω
  have hLp : MemLp (fun y ↦ stationaryScalarFaceReadout μ T L offset x R y ω) 2
      (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1))) :=
    (memLp_two_iff_integrable_sq
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hω
  intro f hf hmean
  have hs := smooth_trace_pairing_sq_le_originalTraceDualInfBound_mul_energy hLp hf hmean
  have hW := originalTraceDualInfBound_nonneg
    (fun y ↦ stationaryScalarFaceReadout μ T L offset x R y ω)
  have hE := boxCollarGradientEnergy_nonneg f (fun _ ↦ 0) (fun _ ↦ 1) 1
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [stationaryCubeTraceDualBound, sq_abs, mul_pow, Real.sq_sqrt hW, Real.sq_sqrt hE] using hs

end OTSelector.Reconstruction
