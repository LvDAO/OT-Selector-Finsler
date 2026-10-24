import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Analysis.Calculus.CompactKernelCurrent

Conditions: A locally integrable vector field and compactly supported C1 kernel, on the specified compact neighborhood of the evaluation point.

Objects: Integrability, measurability, derivative formula and C1 regularity of the compact convolution/current.

Proof detail: Enclose all shifted supports in one compact enlargement; dominate kernel and derivative by compact suprema times the locally integrable current, then differentiate under the integral and identify the resulting continuous derivative.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/html/sec_diffunderint.html): Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters).
- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38): Section 1.6.2, Theorems 1.6.5–1.6.7 (Fatou, monotone convergence, dominated convergence), p. 30.
- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.

Source relation: A locally integrable Bochner-valued compact-kernel generalization of the Leibniz rule, proved with the displayed domination. No traffic model is an assumption.
-/

/-! True C¹ smoothing of a vector-valued local traffic measure by a compactly supported kernel. -/

open Set Function Filter MeasureTheory Metric
open scoped BigOperators Pointwise Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

variable {P W : Type*} [MeasurableSpace P]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {q : ℕ} {σ : Measure P} {X : P → (Fin q → ℝ)} {V : P → W}

omit [NormedSpace ℝ W] in
/-- Local absolute traffic on compact sets generates a single integrable bound for all kernel
translates in a spatial neighborhood. The measure need not have finite total traffic. -/
theorem compact_kernel_local_traffic_bound
    {A : Type*} [NormedAddCommGroup A] {g : (Fin q → ℝ) → A}
    (hg : Continuous g) (hcg : HasCompactSupport g)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z₀ : Fin q → ℝ) :
    ∃ bound : P → ℝ, Integrable bound σ ∧
      ∀ z ∈ ball z₀ 1, ∀ p, ‖g (X p - z)‖ * ‖V p‖ ≤ bound p := by
  classical
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hcg.norm
  let B : Set (Fin q → ℝ) := tsupport g + closedBall z₀ 1
  have hB : IsCompact B := hcg.isCompact.add (isCompact_closedBall z₀ 1)
  refine ⟨fun p ↦ C * B.indicator (fun _ ↦ ‖V p‖) (X p),
    (htraffic B hB).const_mul C, ?_⟩
  intro z hz p
  change ‖g (X p - z)‖ * ‖V p‖ ≤ C * B.indicator (fun _ ↦ ‖V p‖) (X p)
  by_cases hp : X p ∈ B
  · rw [indicator_of_mem hp]
    exact mul_le_mul_of_nonneg_right (hC (mem_range_self _)) (norm_nonneg _)
  · have hzero : g (X p - z) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      apply hp
      exact mem_add.mpr ⟨X p - z, hx, z, ball_subset_closedBall hz, sub_add_cancel _ _⟩
    simp only [hzero, norm_zero, zero_mul, indicator_of_notMem hp, mul_zero, le_refl]

/-- The literal current integral exists for every translate under actual local absolute traffic. -/
theorem integrable_compact_kernel_current
    {η : (Fin q → ℝ) → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z : Fin q → ℝ) : Integrable (fun p ↦ η (X p - z) • V p) σ := by
  obtain ⟨bound, hint, hbound⟩ := compact_kernel_local_traffic_bound hη hcη htraffic z
  have hm : AEStronglyMeasurable (fun p ↦ η (X p - z)) σ :=
    (hη.measurable.comp (hX.sub measurable_const)).aestronglyMeasurable
  refine hint.mono' (hm.smul hV) ?_
  filter_upwards with p
  simpa only [norm_smul] using hbound z (mem_ball_self zero_lt_one) p

private theorem measurable_localTrafficSmoothingDerivative
    {η : (Fin q → ℝ) → ℝ} (hη : ContDiff ℝ 1 η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ) (z : Fin q → ℝ) :
    AEStronglyMeasurable
      (fun p ↦ (-(fderiv ℝ η (X p - z))).smulRight (V p)) σ := by
  apply (ContinuousLinearMap.smulRightL ℝ (Fin q → ℝ) W).continuous₂.comp_aestronglyMeasurable₂
    _ hV
  exact ((hη.continuous_fderiv one_ne_zero).neg.stronglyMeasurable.comp_measurable
    (hX.sub measurable_const)).aestronglyMeasurable

omit [MeasurableSpace P] in
private theorem norm_localTrafficSmoothingDerivative
    {η : (Fin q → ℝ) → ℝ} (z : Fin q → ℝ) (p : P) :
    ‖(-(fderiv ℝ η (X p - z))).smulRight (V p)‖ =
      ‖fderiv ℝ η (X p - z)‖ * ‖V p‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_neg]

/-- The actual derivative integrand is integrable using only local traffic, as is the current. -/
theorem integrable_compact_kernel_current_derivative
    {η : (Fin q → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z : Fin q → ℝ) :
    Integrable (fun p ↦ (-(fderiv ℝ η (X p - z))).smulRight (V p)) σ := by
  obtain ⟨bound, hint, hbound⟩ := compact_kernel_local_traffic_bound
    (hη.continuous_fderiv one_ne_zero) (hcη.fderiv ℝ) htraffic z
  refine hint.mono' (measurable_localTrafficSmoothingDerivative hη hX hV z) ?_
  filter_upwards with p
  rw [norm_localTrafficSmoothingDerivative]
  exact hbound z (mem_ball_self zero_lt_one) p

/-- The true current derivative is the integral of the differentiated original compact kernel.
The minus sign comes from the actual translate `X p - z`. -/
theorem hasFDerivAt_compact_kernel_current
    {η : (Fin q → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z₀ : Fin q → ℝ) :
    HasFDerivAt (fun z ↦ ∫ p, η (X p - z) • V p ∂σ)
      (∫ p, (-(fderiv ℝ η (X p - z₀))).smulRight (V p) ∂σ) z₀ := by
  obtain ⟨bound, hint, hbound⟩ := compact_kernel_local_traffic_bound
    (hη.continuous_fderiv one_ne_zero) (hcη.fderiv ℝ) htraffic z₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun z p ↦ (-(fderiv ℝ η (X p - z))).smulRight (V p))
    (ball_mem_nhds z₀ zero_lt_one)
    (Eventually.of_forall fun z ↦
      (integrable_compact_kernel_current hη.continuous hcη hX hV htraffic z).1)
    (integrable_compact_kernel_current hη.continuous hcη hX hV htraffic z₀)
    (measurable_localTrafficSmoothingDerivative hη hX hV z₀)
    ?_ hint ?_
  · filter_upwards with p z hz
    rw [norm_localTrafficSmoothingDerivative]
    exact hbound z hz p
  · filter_upwards with p z _
    have hd : HasFDerivAt (fun z ↦ η (X p - z))
        (-(fderiv ℝ η (X p - z))) z := by
      simpa only [zero_sub, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id,
        Function.comp_def] using
        (hη.differentiable one_ne_zero (X p - z)).hasFDerivAt.comp z
          ((hasFDerivAt_const (X p) z).sub (hasFDerivAt_id z))
    exact hd.smul_const (V p)

/-- Local absolute traffic and an actual C¹ compact kernel produce a C¹ spatial current.
No global traffic bound, differentiability premise for the current, or balance law is assumed. -/
theorem contDiff_compact_kernel_current
    {η : (Fin q → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ) :
    ContDiff ℝ 1 (fun z ↦ ∫ p, η (X p - z) • V p ∂σ) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun z ↦ ∫ p, (-(fderiv ℝ η (X p - z))).smulRight (V p) ∂σ, ?_,
    hasFDerivAt_compact_kernel_current hη hcη hX hV htraffic⟩
  rw [continuous_iff_continuousAt]
  intro z₀
  obtain ⟨bound, hint, hbound⟩ := compact_kernel_local_traffic_bound
    (hη.continuous_fderiv one_ne_zero) (hcη.fderiv ℝ) htraffic z₀
  apply continuousAt_of_dominated
    (Eventually.of_forall fun z ↦ measurable_localTrafficSmoothingDerivative hη hX hV z)
    ?_ hint ?_
  · filter_upwards [ball_mem_nhds z₀ zero_lt_one] with z hz
    filter_upwards with p
    rw [norm_localTrafficSmoothingDerivative]
    exact hbound z hz p
  · filter_upwards with p
    apply Continuous.continuousAt
    apply (ContinuousLinearMap.smulRightL ℝ (Fin q → ℝ) W).continuous₂.comp₂
      (((hη.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).neg)
      continuous_const

/-- In each actual direction the derivative is literally the differentiated scalar-kernel
integral, with its negative translate sign. -/
theorem fderiv_compact_kernel_current_apply
    {η : (Fin q → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z h : Fin q → ℝ) :
    fderiv ℝ (fun z ↦ ∫ p, η (X p - z) • V p ∂σ) z h =
      ∫ p, (-(fderiv ℝ η (X p - z) h)) • V p ∂σ := by
  rw [(hasFDerivAt_compact_kernel_current hη hcη hX hV htraffic z).fderiv,
    ContinuousLinearMap.integral_apply
      (integrable_compact_kernel_current_derivative hη hcη hX hV htraffic z)]
  rfl

end OTSelector.Reconstruction
