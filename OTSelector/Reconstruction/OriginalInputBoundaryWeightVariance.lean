import OTSelector.Reconstruction.OriginalPoissonSignedInputMoments
import OTSelector.Reconstruction.OriginalPathLengthRetention
import Mathlib.Analysis.Convolution

/-!
# The boundary weight of the unchanged original full Poisson input

For the centered cube of radius `R`, the weight is literally its indicator minus
its convolution with the nonnegative, unit-mass smoothing kernel. Every original
point is retained in the Poisson sum. The kernel is supported in the unit ball
for the coordinate norm. No assertion about adaptively selected ports is used.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι]

/-- The literal spatial full-input boundary weight in the paper; side length is `2 * R`. -/
def originalInputBoundaryWeight (η : (ι → ℝ) → ℝ) (R : ℝ) (x : ι → ℝ) : ℝ :=
  (haarRootCube ι R).indicator (fun _ ↦ (1 : ℝ)) x -
    ∫ w in haarRootCube ι R, η (w - x)

/-- The fixed-width inner-and-outer shell of the same centered cube. -/
def originalInputBoundaryShell (R : ℝ) : Set (ι → ℝ) :=
  haarRootCube ι (R + 1) \ haarRootCube ι (R - 1)

/-- The literal weight is Borel measurable for every measurable kernel. -/
theorem measurable_originalInputBoundaryWeight
    {η : (ι → ℝ) → ℝ} (hη : Measurable η) (R : ℝ) :
    Measurable (originalInputBoundaryWeight η R) := by
  apply (measurable_const.indicator measurableSet_Icc).sub
  have hm : StronglyMeasurable (fun p : (ι → ℝ) × (ι → ℝ) ↦ η (p.2 - p.1)) :=
    (hη.comp (measurable_snd.sub measurable_fst)).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume.restrict (haarRootCube ι R))).measurable

private theorem originalInputBoundarySmoothing_eq_convolution
    (η : (ι → ℝ) → ℝ) (R : ℝ) :
    (fun x ↦ ∫ w in haarRootCube ι R, η (w - x)) =
      MeasureTheory.convolution ((haarRootCube ι R).indicator (fun _ ↦ (1 : ℝ)))
        (fun y ↦ η (-y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, neg_sub]
  rw [← integral_indicator (s := haarRootCube ι R) measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ haarRootCube ι R <;> simp [hw]

/-- The spatial boundary weight is integrable over the entire original Haar space. -/
theorem integrable_originalInputBoundaryWeight
    {η : (ι → ℝ) → ℝ} (hη : Integrable η) (R : ℝ) :
    Integrable (originalInputBoundaryWeight η R) := by
  have hi : Integrable ((haarRootCube ι R).indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const isCompact_Icc.measure_ne_top)
  have hc := hi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hη.comp_neg
  rw [← originalInputBoundarySmoothing_eq_convolution] at hc
  exact hi.sub hc

/-- Smoothing preserves exactly the full Haar integral, including cancellation
between the two sides of the boundary. -/
theorem integral_originalInputBoundaryWeight_eq_zero
    {η : (ι → ℝ) → ℝ} (hη : Integrable η) (hηone : ∫ x, η x = 1) (R : ℝ) :
    (∫ x, originalInputBoundaryWeight η R x) = 0 := by
  have hi : Integrable ((haarRootCube ι R).indicator (fun _ ↦ (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const isCompact_Icc.measure_ne_top)
  have hc := hi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hη.comp_neg
  change (∫ x, ((haarRootCube ι R).indicator (fun _ ↦ (1 : ℝ)) -
    (fun x ↦ ∫ w in haarRootCube ι R, η (w - x))) x) = 0
  rw [originalInputBoundarySmoothing_eq_convolution]
  simp only [Pi.sub_apply]
  rw [integral_sub hi hc,
    integral_convolution _ hi hη.comp_neg, integral_neg_eq_self, hηone]
  simp

/-- A nonnegative unit-mass kernel keeps every smoothed indicator between zero and one. -/
theorem originalInputBoundarySmoothing_bounds
    {η : (ι → ℝ) → ℝ} (hη : Integrable η) (hηnonneg : ∀ x, 0 ≤ η x)
    (hηone : ∫ x, η x = 1) (R : ℝ) (x : ι → ℝ) :
    0 ≤ (∫ w in haarRootCube ι R, η (w - x)) ∧
      (∫ w in haarRootCube ι R, η (w - x)) ≤ 1 := by
  refine ⟨integral_nonneg (fun _ ↦ hηnonneg _), ?_⟩
  calc
    _ ≤ ∫ w, η (w - x) :=
      setIntegral_le_integral (hη.comp_sub_right x) (.of_forall (fun _ ↦ hηnonneg _))
    _ = 1 := by rw [integral_sub_right_eq_self, hηone]

/-- The full-input signed weight has absolute value at most one. -/
theorem abs_originalInputBoundaryWeight_le_one
    {η : (ι → ℝ) → ℝ} (hη : Integrable η) (hηnonneg : ∀ x, 0 ≤ η x)
    (hηone : ∫ x, η x = 1) (R : ℝ) (x : ι → ℝ) :
    |originalInputBoundaryWeight η R x| ≤ 1 := by
  have hs := originalInputBoundarySmoothing_bounds hη hηnonneg hηone R x
  unfold originalInputBoundaryWeight
  by_cases hx : x ∈ haarRootCube ι R
  · rw [indicator_of_mem hx]
    exact abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · rw [indicator_of_notMem hx]
    exact abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩

private theorem originalInputBoundarySmoothing_eq_one_inner
    {η : (ι → ℝ) → ℝ} (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    {x : ι → ℝ} (hx : x ∈ haarRootCube ι (R - 1)) :
    (∫ w in haarRootCube ι R, η (w - x)) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_sub_right_eq_self, hηone]
  intro w hw
  apply hηsupport
  by_contra! h
  apply hw
  apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R) w).mpr
  have hxn := (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R - 1) x).mp hx
  calc
    ‖w‖ = ‖(w - x) + x‖ := by congr 1; abel
    _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
    _ ≤ R := by linarith

private theorem originalInputBoundarySmoothing_eq_zero_outer
    {η : (ι → ℝ) → ℝ} (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0)
    {R : ℝ} (hR : 0 ≤ R) {x : ι → ℝ} (hx : x ∉ haarRootCube ι (R + 1)) :
    (∫ w in haarRootCube ι R, η (w - x)) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro w hw
  apply hηsupport
  by_contra! h
  apply hx
  apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R + 1) x).mpr
  have hwn := (mem_haarRootCube_iff_norm_le hR w).mp hw
  calc
    ‖x‖ = ‖w - (w - x)‖ := by congr 1; abel
    _ ≤ ‖w‖ + ‖w - x‖ := norm_sub_le _ _
    _ ≤ R + 1 := by linarith

/-- The literal weight vanishes outside a shell of width one on each side,
without restricting or thinning any original Poisson point. -/
theorem originalInputBoundaryWeight_eq_zero_off_shell
    {η : (ι → ℝ) → ℝ} (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (x : ι → ℝ) (hx : x ∉ originalInputBoundaryShell (ι := ι) R) :
    originalInputBoundaryWeight η R x = 0 := by
  have hR0 : 0 ≤ R := by linarith
  by_cases ho : x ∈ haarRootCube ι (R + 1)
  · have hi : x ∈ haarRootCube ι (R - 1) := by
      by_contra hn
      exact hx ⟨ho, hn⟩
    have hc : x ∈ haarRootCube ι R :=
      (mem_haarRootCube_iff_norm_le hR0 x).mpr
        (((mem_haarRootCube_iff_norm_le (by linarith) x).mp hi).trans (by linarith))
    simp only [originalInputBoundaryWeight, indicator_of_mem hc,
      originalInputBoundarySmoothing_eq_one_inner hηone hηsupport hR hi, sub_self]
  · have hc : x ∉ haarRootCube ι R := by
      intro hc
      exact ho ((mem_haarRootCube_iff_norm_le (by linarith) x).mpr
        (((mem_haarRootCube_iff_norm_le hR0 x).mp hc).trans (by linarith)))
    simp only [originalInputBoundaryWeight, indicator_of_notMem hc,
      originalInputBoundarySmoothing_eq_zero_outer hηsupport hR0 ho, sub_self]

/-- The exact Haar volume of the two-sided width-one boundary shell. -/
theorem volume_real_originalInputBoundaryShell {R : ℝ} (hR : 1 ≤ R) :
    volume.real (originalInputBoundaryShell (ι := ι) R) =
      (2 * (R + 1)) ^ Fintype.card ι - (2 * (R - 1)) ^ Fintype.card ι := by
  have hsub : haarRootCube ι (R - 1) ⊆ haarRootCube ι (R + 1) := by
    intro x hx
    exact (mem_haarRootCube_iff_norm_le (by linarith) x).mpr
      (((mem_haarRootCube_iff_norm_le (by linarith) x).mp hx).trans (by linarith))
  rw [originalInputBoundaryShell, measureReal_sdiff hsub measurableSet_Icc
    isCompact_Icc.measure_ne_top, volume_real_haarRootCube ι (by linarith),
    volume_real_haarRootCube ι (by linarith)]

/-- The width-one shell has the actual surface-order volume bound, also in dimension zero. -/
theorem volume_real_originalInputBoundaryShell_le {R : ℝ} (hR : 1 ≤ R) :
    volume.real (originalInputBoundaryShell (ι := ι) R) ≤
      (4 * (Fintype.card ι : ℝ) * 4 ^ (Fintype.card ι - 1)) *
        R ^ (Fintype.card ι - 1) := by
  rw [volume_real_originalInputBoundaryShell hR]
  calc
    _ ≤ |(2 * (R + 1)) ^ Fintype.card ι -
        (2 * (R - 1)) ^ Fintype.card ι| := le_abs_self _
    _ ≤ |2 * (R + 1) - 2 * (R - 1)| * (Fintype.card ι : ℝ) *
        max |2 * (R + 1)| |2 * (R - 1)| ^ (Fintype.card ι - 1) :=
      abs_pow_sub_pow_le _ _ _
    _ = 4 * (Fintype.card ι : ℝ) * (2 * (R + 1)) ^ (Fintype.card ι - 1) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 2 * (R + 1) - 2 * (R - 1)),
        abs_of_nonneg (by linarith : 0 ≤ 2 * (R + 1)),
        abs_of_nonneg (by linarith : 0 ≤ 2 * (R - 1)), max_eq_left (by linarith)]
      congr 2
      ring
    _ ≤ 4 * (Fintype.card ι : ℝ) * (4 * R) ^ (Fintype.card ι - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    _ = _ := by rw [mul_pow]; ring

/-- The deterministic class/color test keeps the original spatial weight and mark. -/
def originalInputClassBoundaryWeight {A : Type*} [MeasurableSpace A]
    (η : (ι → ℝ) → ℝ) (R : ℝ) (C : Set A) (p : (ι → ℝ) × A) : ℝ :=
  originalInputBoundaryWeight η R p.1 * C.indicator (fun _ ↦ (1 : ℝ)) p.2

variable {A : Type*} [MeasurableSpace A]

/-- Every original class test remains measurable. -/
theorem measurable_originalInputClassBoundaryWeight
    {η : (ι → ℝ) → ℝ} (hη : Measurable η) (R : ℝ)
    {C : Set A} (hC : MeasurableSet C) :
    Measurable (originalInputClassBoundaryWeight η R C) :=
  ((measurable_originalInputBoundaryWeight hη R).comp measurable_fst).mul
    ((measurable_const.indicator hC).comp measurable_snd)

/-- Every full-input class test has absolute value at most one. -/
theorem abs_originalInputClassBoundaryWeight_le_one
    {η : (ι → ℝ) → ℝ} (hη : Integrable η) (hηnonneg : ∀ x, 0 ≤ η x)
    (hηone : ∫ x, η x = 1) (R : ℝ) (C : Set A) (p : (ι → ℝ) × A) :
    |originalInputClassBoundaryWeight η R C p| ≤ 1 := by
  unfold originalInputClassBoundaryWeight
  by_cases hp : p.2 ∈ C
  · simpa only [indicator_of_mem hp, mul_one] using
      abs_originalInputBoundaryWeight_le_one hη hηnonneg hηone R p.1
  · simp only [indicator_of_notMem hp, mul_zero, abs_zero, zero_le_one]

/-- On the original enclosing window, each class has exactly zero signed Haar-clock mean. -/
theorem integral_originalInputClassBoundaryWeight_eq_zero
    {η : (ι → ℝ) → ℝ} (hη : Integrable η) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (α : Measure A) [IsProbabilityMeasure α] (C : Set A) :
    (∫ p, originalInputClassBoundaryWeight η R C p
      ∂((volume : Measure (ι → ℝ)).restrict (haarRootCube ι (R + 1))).prod α) = 0 := by
  unfold originalInputClassBoundaryWeight
  rw [integral_prod_mul]
  have hs : (∫ x in haarRootCube ι (R + 1), originalInputBoundaryWeight η R x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      integral_originalInputBoundaryWeight_eq_zero hη hηone R]
    intro x hx
    exact originalInputBoundaryWeight_eq_zero_off_shell hηone hηsupport hR x
      (fun hm ↦ hx hm.1)
  rw [hs, zero_mul]

/-- The squared spatial weight is bounded by the actual shell volume. -/
theorem integral_sq_originalInputBoundaryWeight_le_shell
    {η : (ι → ℝ) → ℝ} (hηm : Measurable η) (hη : Integrable η)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x, (originalInputBoundaryWeight η R x) ^ 2) ≤
      volume.real (originalInputBoundaryShell (ι := ι) R) := by
  let U := haarRootCube ι (R + 1)
  let S := originalInputBoundaryShell (ι := ι) R
  have hS : MeasurableSet S := measurableSet_Icc.diff measurableSet_Icc
  have hSU : S ⊆ U := sdiff_subset
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (show volume U < ∞ from isCompact_Icc.measure_lt_top)⟩
  have hm := measurable_originalInputBoundaryWeight hηm R
  have hb (x : ι → ℝ) : (originalInputBoundaryWeight η R x) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (abs_originalInputBoundaryWeight_le_one hη hηnonneg hηone R x)
  have hi : Integrable (fun x ↦ (originalInputBoundaryWeight η R x) ^ 2)
      (volume.restrict U) :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1
      (.of_forall (fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb x))
  have hzero (x : ι → ℝ) (hx : x ∉ S) : originalInputBoundaryWeight η R x = 0 :=
    originalInputBoundaryWeight_eq_zero_off_shell hηone hηsupport hR x hx
  calc
    _ = ∫ x in U, (originalInputBoundaryWeight η R x) ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [hzero x (fun hs ↦ hx (hSU hs)), zero_pow (by decide : 2 ≠ 0)]
    _ ≤ ∫ x in U, S.indicator (fun _ ↦ (1 : ℝ)) x := by
      apply integral_mono hi
        ((integrable_const (1 : ℝ)).indicator hS)
      intro x
      by_cases hx : x ∈ S
      · simpa only [indicator_of_mem hx] using hb x
      · simp only [indicator_of_notMem hx, hzero x hx, zero_pow (by decide : 2 ≠ 0), le_refl]
    _ = volume.real S := by
      rw [integral_indicator hS, integral_const, smul_eq_mul, mul_one,
        measureReal_def, Measure.restrict_apply_univ, Measure.restrict_apply hS,
        inter_eq_left.mpr hSU]
      rfl

/-- The exact class factor in the full physical second moment; no selected-point law occurs. -/
theorem integral_sq_originalInputClassBoundaryWeight
    {η : (ι → ℝ) → ℝ} (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (α : Measure A) [IsProbabilityMeasure α] {C : Set A} (hC : MeasurableSet C) :
    (∫ p, (originalInputClassBoundaryWeight η R C p) ^ 2
      ∂((volume : Measure (ι → ℝ)).restrict (haarRootCube ι (R + 1))).prod α) =
      α.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 := by
  have heq (p : (ι → ℝ) × A) :
      (originalInputClassBoundaryWeight η R C p) ^ 2 =
        (originalInputBoundaryWeight η R p.1) ^ 2 * C.indicator (fun _ ↦ (1 : ℝ)) p.2 := by
    by_cases hp : p.2 ∈ C <;> simp [originalInputClassBoundaryWeight, hp]
  simp_rw [heq]
  rw [integral_prod_mul (fun x ↦ (originalInputBoundaryWeight η R x) ^ 2)
    (C.indicator (fun _ ↦ (1 : ℝ))), integral_indicator hC, integral_const,
    smul_eq_mul, mul_one]
  have hset : (∫ x in haarRootCube ι (R + 1),
      (originalInputBoundaryWeight η R x) ^ 2) =
      ∫ x, (originalInputBoundaryWeight η R x) ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [originalInputBoundaryWeight_eq_zero_off_shell hηone hηsupport hR x
      (fun hs ↦ hx hs.1), zero_pow (by decide : 2 ≠ 0)]
  rw [hset]
  simpa only [measureReal_def, Measure.restrict_apply_univ] using
    mul_comm (∫ x, (originalInputBoundaryWeight η R x) ^ 2) (α.real C)

/-- Exact signed first and second moments under the unchanged original finite Poisson
block, stated with its physical intensity to keep the normalization visible. -/
theorem originalPoisson_classBoundaryWeight_moments_of_intensity
    {η : (ι → ℝ) → ℝ} (hηm : Measurable η) (hη : Integrable η)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (α : Measure A) [IsProbabilityMeasure α] {C : Set A} (hC : MeasurableSet C)
    (ν : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (hintensity : (r : ℝ≥0∞) • ν =
      ((volume : Measure (ι → ℝ)).restrict (haarRootCube ι (R + 1))).prod α) :
    (∫ b, legalInputBlockTest (originalInputClassBoundaryWeight η R C) b
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) = 0 ∧
    (∫ b, (legalInputBlockTest (originalInputClassBoundaryWeight η R C) b) ^ 2
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      α.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 ∧
    (∫ b, (legalInputBlockTest (originalInputClassBoundaryWeight η R C) b) ^ 2
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) ≤
      α.real C * ((4 * (Fintype.card ι : ℝ) * 4 ^ (Fintype.card ι - 1)) *
        R ^ (Fintype.card ι - 1)) := by
  let f := originalInputClassBoundaryWeight η R C
  have hf : Measurable f := measurable_originalInputClassBoundaryWeight hηm R hC
  have hb : ∀ p, |f p| ≤ 1 := abs_originalInputClassBoundaryWeight_le_one
    hη hηnonneg hηone R C
  have hmean : (r : ℝ) * ∫ p, f p ∂ν = 0 := by
    rw [← smul_eq_mul, ← ENNReal.coe_toReal, ← integral_smul_measure, hintensity]
    exact integral_originalInputClassBoundaryWeight_eq_zero hη hηone hηsupport hR α C
  have hfirst := integral_originalPoisson_blockTest ν r hf hb
  rw [hmean] at hfirst
  have hsecond := integral_sq_centered_originalPoisson_blockTest ν r hf zero_le_one hb
  rw [hmean] at hsecond
  simp only [sub_zero] at hsecond
  have hphysical : (r : ℝ) * ∫ p, (f p) ^ 2 ∂ν =
      α.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 := by
    rw [← smul_eq_mul, ← ENNReal.coe_toReal, ← integral_smul_measure, hintensity]
    exact integral_sq_originalInputClassBoundaryWeight hηone hηsupport hR α hC
  rw [hphysical] at hsecond
  refine ⟨hfirst, hsecond, ?_⟩
  rw [hsecond]
  exact mul_le_mul_of_nonneg_left
    ((integral_sq_originalInputBoundaryWeight_le_shell hηm hη hηnonneg hηone hηsupport hR).trans
      (volume_real_originalInputBoundaryShell_le hR)) (measureReal_nonneg)

/-- The original full-input Poisson window itself supplies the intensity equality.
For either original clock color `α`, every measurable class has zero mean and
surface-order variance under its unchanged original count-and-points law. -/
theorem originalInputBoundary_originalPoissonWindow_moments
    (q : ℕ) {η : (Fin q → ℝ) → ℝ} (hηm : Measurable η) (hη : Integrable η)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (α : Measure ℝ) [IsProbabilityMeasure α] {C : Set ℝ} (hC : MeasurableSet C) :
    let U := haarRootCube (Fin q) (R + 1)
    let ν := (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α
    let P := Measure.sum (fun n : ℕ ↦ (poissonMeasure (volume U).toNNReal {n}) •
      (Measure.pi (fun _ : Fin n ↦ ν)).map
        (fun y ↦ (⟨n, y⟩ : BlockData ((Fin q → ℝ) × ℝ))))
    (∫ b, legalInputBlockTest (originalInputClassBoundaryWeight η R C) b ∂P) = 0 ∧
    (∫ b, (legalInputBlockTest (originalInputClassBoundaryWeight η R C) b) ^ 2 ∂P) =
      α.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 ∧
    (∫ b, (legalInputBlockTest (originalInputClassBoundaryWeight η R C) b) ^ 2 ∂P) ≤
      α.real C * ((4 * (q : ℝ) * 4 ^ (q - 1)) * R ^ (q - 1)) := by
  dsimp only
  let U := haarRootCube (Fin q) (R + 1)
  let μ := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have hUfin : volume U ≠ ∞ := isCompact_Icc.measure_ne_top
  have hUpos : volume U ≠ 0 := by
    dsimp only [U]
    rw [volume_haarRootCube (Fin q) (by linarith)]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (pow_pos (by linarith : 0 < 2 * (R + 1)) (Fintype.card (Fin q))))
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  have : IsProbabilityMeasure μ := normalizedFiniteLaw_probability _ hmass
  have hintensity : ((volume U).toNNReal : ℝ≥0∞) • (μ.prod α) =
      ((volume : Measure (Fin q → ℝ)).restrict U).prod α := by
    rw [ENNReal.coe_toNNReal hUfin]
    exact physicalIntensity_smul_normalized_window q hUfin hUpos α
  simpa only [Fintype.card_fin, blockDataLaw, μ, U] using
    originalPoisson_classBoundaryWeight_moments_of_intensity hηm hη hηnonneg hηone
      hηsupport hR α hC (μ.prod α) (volume U).toNNReal hintensity

private theorem originalBoundaryBlockLaw_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    IsProbabilityMeasure (blockDataLaw ν (fun n ↦ poissonMeasure r {n})) := by
  rw [blockDataLaw_eq_map_cloud]
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_sigma_mk n).comp
    (measurable_pi_lambda _ (fun j : Fin n ↦ measurable_pi_apply (j : ℕ)))

/-- Both actual original colors in the existing full two-color Poisson window
have zero signed class mean and the same exact surface-order variance formula.
The only color-dependent factor is its original clock-class probability. -/
theorem originalInputBoundary_legalInputPoissonWindowLaw_color_moments
    (q : ℕ) {η : (Fin q → ℝ) → ℝ} (hηm : Measurable η) (hη : Integrable η)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C : Set ℝ} (hC : MeasurableSet C) (color : Fin 2) :
    let γ := if color = 0 then α else β
    let f := originalInputClassBoundaryWeight η R C
    let P := legalInputPoissonWindowLaw q (haarRootCube (Fin q) (R + 1)) α β
    (∫ b, legalInputBlockTest f (if color = 0 then b.1 else b.2) ∂P) = 0 ∧
    (∫ b, (legalInputBlockTest f (if color = 0 then b.1 else b.2)) ^ 2 ∂P) =
      γ.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 ∧
    (∫ b, (legalInputBlockTest f (if color = 0 then b.1 else b.2)) ^ 2 ∂P) ≤
      γ.real C * ((4 * (q : ℝ) * 4 ^ (q - 1)) * R ^ (q - 1)) := by
  let U := haarRootCube (Fin q) (R + 1)
  let μ := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have hUfin : volume U ≠ ∞ := isCompact_Icc.measure_ne_top
  have hUpos : volume U ≠ 0 := by
    dsimp only [U]
    rw [volume_haarRootCube (Fin q) (by linarith)]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (pow_pos (by linarith : 0 < 2 * (R + 1)) (Fintype.card (Fin q))))
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  have : IsProbabilityMeasure μ := normalizedFiniteLaw_probability _ hmass
  let P := blockDataLaw (μ.prod α) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  let Q := blockDataLaw (μ.prod β) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  have : IsProbabilityMeasure P := originalBoundaryBlockLaw_probability _ _
  have : IsProbabilityMeasure Q := originalBoundaryBlockLaw_probability _ _
  by_cases hc : color = 0
  · simp only [hc, ↓reduceIte]
    change (∫ b, legalInputBlockTest _ b.1 ∂P.prod Q) = 0 ∧
      (∫ b, (legalInputBlockTest _ b.1) ^ 2 ∂P.prod Q) = _ ∧
      (∫ b, (legalInputBlockTest _ b.1) ^ 2 ∂P.prod Q) ≤ _
    rw [integral_fun_fst (μ := P) (ν := Q),
      integral_fun_fst (μ := P) (ν := Q)
        (fun b ↦ (legalInputBlockTest (originalInputClassBoundaryWeight η R C) b) ^ 2)]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact originalInputBoundary_originalPoissonWindow_moments q hηm hη hηnonneg hηone
      hηsupport hR α hC
  · simp only [hc, ↓reduceIte]
    change (∫ b, legalInputBlockTest _ b.2 ∂P.prod Q) = 0 ∧
      (∫ b, (legalInputBlockTest _ b.2) ^ 2 ∂P.prod Q) = _ ∧
      (∫ b, (legalInputBlockTest _ b.2) ^ 2 ∂P.prod Q) ≤ _
    rw [integral_fun_snd (μ := P) (ν := Q),
      integral_fun_snd (μ := P) (ν := Q)
        (fun b ↦ (legalInputBlockTest (originalInputClassBoundaryWeight η R C) b) ^ 2)]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact originalInputBoundary_originalPoissonWindow_moments q hηm hη hηnonneg hηone
      hηsupport hR β hC

/-- The enclosing window does not omit any contribution of the full original
point measure: the same test vanishes identically outside it. -/
theorem integral_originalInputClassBoundaryWeight_restrict_outer
    {η : (ι → ℝ) → ℝ} (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (C : Set A) (μ : Measure ((ι → ℝ) × A)) :
    (∫ p in (haarRootCube ι (R + 1)) ×ˢ (univ : Set A),
      originalInputClassBoundaryWeight η R C p ∂μ) =
      ∫ p, originalInputClassBoundaryWeight η R C p ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hx : p.1 ∉ haarRootCube ι (R + 1) := fun hx ↦ hp ⟨hx, mem_univ _⟩
  unfold originalInputClassBoundaryWeight
  rw [originalInputBoundaryWeight_eq_zero_off_shell hηone hηsupport hR p.1
    (fun hs ↦ hx hs.1), zero_mul]

/-- Literal variance of either original full-input color/class, with an explicit
constant independent of the cube radius. Its side length is `L = 2 * R`. -/
theorem variance_originalInputBoundary_legalInputPoissonWindowLaw_color
    (q : ℕ) {η : (Fin q → ℝ) → ℝ} (hηm : Measurable η) (hη : Integrable η)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 < ‖x‖ → η x = 0) {R : ℝ} (hR : 1 ≤ R)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C : Set ℝ} (hC : MeasurableSet C) (color : Fin 2) :
    let γ := if color = 0 then α else β
    let f := fun b : BlockData ((Fin q → ℝ) × ℝ) × BlockData ((Fin q → ℝ) × ℝ) ↦
      legalInputBlockTest (originalInputClassBoundaryWeight η R C)
        (if color = 0 then b.1 else b.2)
    let P := legalInputPoissonWindowLaw q (haarRootCube (Fin q) (R + 1)) α β
    variance f P = γ.real C * ∫ x, (originalInputBoundaryWeight η R x) ^ 2 ∧
      variance f P ≤ γ.real C * ((4 * (q : ℝ) * 4 ^ (q - 1)) * R ^ (q - 1)) := by
  dsimp only
  have hf := measurable_legalInputBlockTest
    (measurable_originalInputClassBoundaryWeight hηm R hC)
  have hm : Measurable (fun b : BlockData ((Fin q → ℝ) × ℝ) ×
      BlockData ((Fin q → ℝ) × ℝ) ↦
      legalInputBlockTest (originalInputClassBoundaryWeight η R C)
        (if color = 0 then b.1 else b.2)) := by
    by_cases hc : color = 0
    · simpa only [hc, ↓reduceIte, Function.comp_def] using hf.comp measurable_fst
    · simpa only [hc, ↓reduceIte, Function.comp_def] using hf.comp measurable_snd
  have h := originalInputBoundary_legalInputPoissonWindowLaw_color_moments
    q hηm hη hηnonneg hηone hηsupport hR α β hC color
  dsimp only at h
  rw [variance_eq_integral hm.aemeasurable, h.1]
  simpa only [sub_zero] using h.2

end OTSelector.Reconstruction
