import OTSelector.Reconstruction.OriginalCubeTraceCompactnessBounded
import OTSelector.Analysis.InnerProductSpace.FiniteCoefficientCauchy

/-! A literal common quadratic bound for all smooth unit-energy face tests. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- The original finite face readout is square-integrable on the full face. -/
theorem memLp_boxFaceStepLinear {ι : Type*} [Fintype ι]
    {I : Box ι} (π : Prepartition I) (c : π.boxes → ℝ) :
    MemLp (boxFaceStepLinear π c) 2 (volume.restrict I.Icc) := by
  classical
  let : IsFiniteMeasure (volume.restrict I.Icc) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  change MemLp (fun y ↦ ∑ J : π.boxes,
    c J * (J.1 : Set (ι → ℝ)).indicator (fun _ ↦ 1) y) 2 _
  exact memLp_finsetSum Finset.univ (fun J _ ↦
    ((memLp_const (1 : ℝ)).indicator J.1.measurableSet_coe).const_mul (c J))

/-- The literal pairing with a finite step readout is the finite sum of
original cell integrals, with no change of boundary representative. -/
theorem integral_mul_boxFaceStepLinear_eq_sum {ι : Type*} [Fintype ι]
    {I : Box ι} (π : Prepartition I) (c : π.boxes → ℝ)
    {g : (ι → ℝ) → ℝ} (hg : IntegrableOn g I.Icc volume) :
    (∫ y in I.Icc, g y * boxFaceStepLinear π c y) =
      ∑ J : π.boxes, c J * (∫ y in J.1.Icc, g y) := by
  classical
  have he (y : ι → ℝ) : g y * boxFaceStepLinear π c y =
      ∑ J : π.boxes, c J * (J.1 : Set (ι → ℝ)).indicator g y := by
    change g y * (∑ J : π.boxes,
      c J * (J.1 : Set (ι → ℝ)).indicator (fun _ ↦ 1) y) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J _
    by_cases hy : y ∈ (J.1 : Set (ι → ℝ)) <;> simp [hy, mul_comm]
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun J _ ↦ (hg.indicator J.1.measurableSet_coe).const_mul (c J))]
  apply Finset.sum_congr rfl
  intro J _
  rw [integral_const_mul, integral_indicator J.1.measurableSet_coe]
  change c J * (∫ y, g y ∂(volume.restrict I.Icc).restrict (J.1 : Set (ι → ℝ))) = _
  rw [Measure.restrict_restrict_of_subset (s := (J.1 : Set (ι → ℝ))) (t := I.Icc)
    (fun y hy ↦ Box.coe_subset_Icc (π.le_of_mem J.2 hy))]
  rw [setIntegral_congr_set J.1.coe_ae_eq_Icc]

/-- The exact common quadratic bound depends only on original face data and
finitely many original cell integrals, independently of the test function. -/
def originalDyadicTraceDualBound {q : ℕ} (g : (Fin q → ℝ) → ℝ) (n : ℕ) : ℝ :=
  2 * ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n) *
    (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), (g y)^2) +
  2 * (Fintype.card (originalDyadicFacePartition (ι := Fin q) n).boxes : ℝ) *
    ((((1 : ℝ) / 2^n)^(q + 1))⁻¹ * (((q + 1 : ℕ) : ℝ) / 2)) *
      (∑ J : (originalDyadicFacePartition (ι := Fin q) n).boxes,
        (∫ y in J.1.Icc, g y)^2)

/-- The actual common quadratic bound is nonnegative. -/
theorem originalDyadicTraceDualBound_nonneg
    {q : ℕ} (g : (Fin q → ℝ) → ℝ) (n : ℕ) :
    0 ≤ originalDyadicTraceDualBound g n := by
  unfold originalDyadicTraceDualBound
  positivity

/-- One literal nonnegative quantity simultaneously bounds the squared
pairing with every smooth mean-zero unit-gradient cube test. No supremum,
measurable-selection premise, or completed H1 dual norm is assumed. -/
theorem smooth_unit_energy_trace_pairing_sq_le_originalDyadicTraceDualBound
    {q : ℕ} {g : (Fin q → ℝ) → ℝ}
    (hg : MemLp g 2 (volume.restrict (Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1))))
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hmean : (∫ p in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1) ×ˢ Icc (0 : ℝ) 1,
      f p) = 0)
    (henergy : boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1)
    (n : ℕ) :
    (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1), g y * f (y, 0))^2 ≤
      originalDyadicTraceDualBound g n := by
  classical
  let I := originalUnitFaceBox (Fin q)
  let π := originalDyadicFacePartition (ι := Fin q) n
  let : IsFiniteMeasure (volume.restrict I.Icc) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hgc : IntegrableOn g I.Icc volume := MemLp.integrable (by norm_num) hg
  have htrace : MemLp (fun y ↦ f (y, 0)) 2 (volume.restrict I.Icc) := by
    apply (memLp_two_iff_integrable_sq
      (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).2
    exact ((hf.continuous.comp (continuous_id.prodMk continuous_const)).pow 2).continuousOn.integrableOn_Icc
  have hstep := memLp_boxFaceStepLinear π (originalDyadicTraceMeans f n)
  have herr := integral_mul_sq_le_of_memLp_two hg (htrace.sub hstep)
  have herror := smooth_originalDyadicTraceApprox_error_sq_le_unit_energy hf n
  have herror1 : (∫ y in I.Icc, (f (y, 0) - originalDyadicTraceApprox f n y)^2) ≤
      ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n) :=
    herror.trans (mul_le_of_le_one_right (by positivity) henergy)
  have hA := herr.trans (mul_le_mul_of_nonneg_left herror1
    (integral_nonneg (fun _ ↦ sq_nonneg (g _))))
  have hB := sum_mul_sq_le_fintype_card_mul_of_coeff_sq_le
    (originalDyadicTraceMeans f n) (fun J : π.boxes ↦ ∫ y in J.1.Icc, g y)
    (originalDyadicTraceMeans_sq_le_of_mean_zero_unit_energy hf hmean henergy n)
  rw [← integral_mul_boxFaceStepLinear_eq_sum π (originalDyadicTraceMeans f n) hgc] at hB
  have he : (∫ y in I.Icc, g y * (f (y, 0) - originalDyadicTraceApprox f n y)) =
      (∫ y in I.Icc, g y * f (y, 0)) -
        (∫ y in I.Icc, g y * originalDyadicTraceApprox f n y) := by
    simp_rw [mul_sub]
    exact integral_sub (hg.integrable_mul htrace) (hg.integrable_mul hstep)
  change (∫ y in I.Icc, g y * (f (y, 0) - originalDyadicTraceApprox f n y))^2 ≤ _ at hA
  rw [he] at hA
  change (∫ y in I.Icc, g y * originalDyadicTraceApprox f n y)^2 ≤ _ at hB
  unfold originalDyadicTraceDualBound
  change (∫ y in I.Icc, g y * f (y, 0))^2 ≤ _
  have hs := sq_nonneg ((∫ y in I.Icc, g y * (f (y, 0) - originalDyadicTraceApprox f n y)) -
    (∫ y in I.Icc, g y * originalDyadicTraceApprox f n y))
  rw [he] at hs
  nlinarith

end OTSelector.Reconstruction
