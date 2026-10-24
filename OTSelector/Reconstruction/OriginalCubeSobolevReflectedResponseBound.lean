import OTSelector.Reconstruction.OriginalCubeSobolevPoincareScale
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedKernelLp

/-! Actual reflected scalar input responses act uniformly on zero-mean cube gradient tests. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- A concrete dimension-and-amplitude constant for the actual reflected scalar response. -/
def cubeReflectedResponseSobolevConstant (q : ℕ) (M : ℝ) : ℝ :=
  (((3 : ℝ)^q + 1) * M) * (2 : ℝ)^q * cubeSobolevPoincareConstant q

/-- The actual response constant is nonnegative for a nonnegative kernel amplitude. -/
theorem cubeReflectedResponseSobolevConstant_nonneg (q : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ cubeReflectedResponseSobolevConstant q M :=
  mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM) (by positivity))
    (cubeSobolevPoincareConstant_nonneg q)

/-- The actual reflected response times a continuous test is genuinely integrable on the
literal cube, directly from original measurable bounded kernel data. -/
theorem integrable_originalCubeReflectedInputResponse_mul_continuous
    {q : ℕ} {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ v, |η v| ≤ M) (R : ℝ) (x : Fin q → ℝ)
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    Integrable (fun z ↦ originalCubeReflectedInputResponse η R z x * u z)
      (volume.restrict (haarRootCube (Fin q) R)) := by
  have hm : Measurable (fun z : Fin q → ℝ ↦ originalCubeReflectedInputResponse η R z x) :=
    (measurable_originalCubeReflectedInputResponse hη R).comp (measurable_id.prodMk measurable_const)
  apply (hu.continuousOn.integrableOn_Icc).bdd_mul hm.aestronglyMeasurable
  exact ae_of_all _ (fun z ↦ by simpa only [Real.norm_eq_abs] using
    abs_originalCubeReflectedInputResponse_le hM hηM R z x)

/-- The true reflected scalar response has a scale-independent gradient-dual bound. The
kernel need only be measurable, bounded and of unit range; no symmetry or normalization is used. -/
theorem abs_integral_originalCubeReflectedInputResponse_mul_le_sqrt_energy
    {q : ℕ} (hq : 2 < q) {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    (x : Fin q → ℝ) {u : (Fin q → ℝ) → ℝ} (hu : ContDiff ℝ 1 u)
    (hmean : (∫ z in haarRootCube (Fin q) R, u z) = 0) :
    |∫ z in haarRootCube (Fin q) R, originalCubeReflectedInputResponse η R z x * u z| ≤
      cubeReflectedResponseSobolevConstant q M * Real.sqrt
        (∑ k : Fin q, ∫ z in haarRootCube (Fin q) R,
          (fderiv ℝ u z (Pi.single k 1))^2) := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (haarRootCube (Fin q) R)
  let κ : (Fin q → ℝ) → ℝ := fun z ↦ originalCubeReflectedInputResponse η R z x
  let d : ℝ≥0 := Real.toNNReal (2 * (q : ℝ) / ((q : ℝ) + 2))
  let p : ℝ≥0 := Real.toNNReal (2 * (q : ℝ) / ((q : ℝ) - 2))
  let D : ℝ := ((3 : ℝ)^q + 1) * M
  let V : ℝ := (2 : ℝ)^q
  let E : ℝ := ∑ k : Fin q, ∫ z, (fderiv ℝ u z (Pi.single k 1))^2 ∂μ
  have hqR : (2 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hplus : (0 : ℝ) < (q : ℝ) + 2 := by linarith
  have hminus : (0 : ℝ) < (q : ℝ) - 2 := by linarith
  have hd : (d : ℝ) = 2 * (q : ℝ) / ((q : ℝ) + 2) :=
    Real.coe_toNNReal _ (le_of_lt (div_pos (mul_pos (by norm_num) hqpos) hplus))
  have hp : (p : ℝ) = 2 * (q : ℝ) / ((q : ℝ) - 2) :=
    Real.coe_toNNReal _ (le_of_lt (div_pos (mul_pos (by norm_num) hqpos) hminus))
  have hc : Real.HolderConjugate (d : ℝ) (p : ℝ) := by
    rw [hd, hp]
    apply Real.holderConjugate_iff.mpr
    refine ⟨(lt_div_iff₀ hplus).mpr (by linarith), ?_⟩
    field_simp [ne_of_gt hqpos]
    ring
  have hd0 : d ≠ 0 := by exact_mod_cast hc.ne_zero
  have hp0 : p ≠ 0 := by exact_mod_cast hc.symm.ne_zero
  have hκm : Measurable κ := (measurable_originalCubeReflectedInputResponse hη R).comp
    (measurable_id.prodMk measurable_const)
  have hpair : ‖∫ z, κ z * u z ∂μ‖ₑ ≤ eLpNorm κ d μ * eLpNorm u p μ := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    rw [eLpNorm_nnreal_eq_lintegral hd0, eLpNorm_nnreal_eq_lintegral hp0]
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
      hκm.enorm.aemeasurable hu.continuous.measurable.enorm.aemeasurable
    simpa only [Pi.mul_apply, enorm_mul] using hh
  have hD : 0 ≤ D := mul_nonneg (by positivity) hM
  have hV : 1 ≤ V := one_le_pow₀ (by norm_num)
  have hκLp : eLpNorm κ d μ ≤ ENNReal.ofReal (D * V) := by
    have hh := eLpNorm_originalCubeReflectedInputResponse_le hM hηM hηsupport d R x
    have hvpow : (ENNReal.ofReal V) ^ (1 / (d : ℝ)) ≤ ENNReal.ofReal V := by
      have hh := ENNReal.rpow_le_rpow_of_exponent_le
        (ENNReal.one_le_ofReal.mpr hV) (show 1 / (d : ℝ) ≤ 1 by simpa using hc.inv_lt_inv.le)
      simpa only [ENNReal.rpow_one] using hh
    calc
      _ ≤ ENNReal.ofReal D * (ENNReal.ofReal V) ^ (1 / (d : ℝ)) := by
        simpa only [Fintype.card_fin, ENNReal.coe_toReal] using hh
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal V := mul_le_mul le_rfl hvpow bot_le bot_le
      _ = _ := (ENNReal.ofReal_mul hD).symm
  have huLp : eLpNorm u p μ ≤ ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt E) := by
    simpa only [μ, p, ENNReal.ofReal, haarRootCube, E] using
      smooth_centered_cube_sobolev_poincare hq hR hu hmean
  have hbound : ENNReal.ofReal |∫ z, κ z * u z ∂μ| ≤
      ENNReal.ofReal (cubeReflectedResponseSobolevConstant q M * Real.sqrt E) := by
    calc
      _ = ‖∫ z, κ z * u z ∂μ‖ₑ := by rw [← ofReal_norm, Real.norm_eq_abs]
      _ ≤ _ := hpair
      _ ≤ ENNReal.ofReal (D * V) *
          ENNReal.ofReal (cubeSobolevPoincareConstant q * Real.sqrt E) :=
        mul_le_mul hκLp huLp bot_le bot_le
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hD (zero_le_one.trans hV))]
        congr 1
        dsimp [cubeReflectedResponseSobolevConstant, D, V]
        ring
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (cubeReflectedResponseSobolevConstant_nonneg q hM) (Real.sqrt_nonneg E))).mp hbound

end OTSelector.Reconstruction
