import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume
import Mathlib.MeasureTheory.Function.L2Space

/-! A genuine surface-scale second moment pays the actual quadratic-scale cut bad event. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- True surface-normalized L2 convergence gives the precise R² probability decay needed
for a physical-volume threshold. No independence between the cut and original input is used. -/
theorem tendsto_quadratic_cut_bad_probability_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q : ℕ} (hq : 0 < q) (X : ℝ → Ω → ℝ)
    (hX : ∀ R, 1 ≤ R → MemLp (X R) 2 P)
    (hsecond : Tendsto (fun R : ℝ ↦ ∫ sample,
      ((R^(q-1))⁻¹ * X R sample)^2 ∂P) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ ↦ R^2 * P.real {sample | ε*(2*R)^q ≤ |X R sample|})
      atTop (𝓝 0) := by
  have hlim := hsecond.const_mul (((ε*(2:ℝ)^q)^2)⁻¹)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hRp : 0 < R := by linarith
  have hthreshold : 0 < ε*(2*R)^q := mul_pos hε (pow_pos (by positivity) _)
  have hevent : {sample | ε*(2*R)^q ≤ |X R sample|} =
      {sample | (ε*(2*R)^q)^2 ≤ (X R sample)^2} := by
    ext sample
    change ε*(2*R)^q ≤ |X R sample| ↔ (ε*(2*R)^q)^2 ≤ (X R sample)^2
    rw [← sq_abs (X R sample)]
    exact (sq_le_sq₀ hthreshold.le (abs_nonneg _)).symm
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all P (fun sample ↦ sq_nonneg (X R sample))) (hX R hR).integrable_sq ((ε*(2*R)^q)^2)
  rw [← hevent] at hm
  have hp : P.real {sample | ε*(2*R)^q ≤ |X R sample|} ≤
      (∫ sample, (X R sample)^2 ∂P)/(ε*(2*R)^q)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hthreshold)).mpr
    simpa only [mul_comm] using hm
  calc
    _ ≤ R^2 * ((∫ sample, (X R sample)^2 ∂P)/(ε*(2*R)^q)^2) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg R)
    _ = ((ε*(2:ℝ)^q)^2)⁻¹ * (∫ sample, ((R^(q-1))⁻¹ * X R sample)^2 ∂P) := by
      simp_rw [mul_pow, integral_const_mul]
      have hpow : R^q = R^(q-1)*R := by
        conv_lhs => rw [show q = q-1+1 by omega, pow_succ]
      simp only [mul_pow, hpow]
      field_simp [hε.ne', hRp.ne', pow_ne_zero _ hRp.ne']

/-- The very same bad event admits a measurable enclosing event of exactly equal original
probability, so count-weighted selected-event consumers need no extra measurability premise. -/
theorem exists_measurable_cut_bad_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (threshold : ℝ) :
    ∃ B : Set Ω, MeasurableSet B ∧ {sample | threshold ≤ |X sample|} ⊆ B ∧
      P.real B = P.real {sample | threshold ≤ |X sample|} := by
  refine ⟨toMeasurable P {sample | threshold ≤ |X sample|}, measurableSet_toMeasurable _ _,
    subset_toMeasurable _ _, ?_⟩
  rw [measureReal_def, measureReal_def, measure_toMeasurable]

end OTSelector.Reconstruction
