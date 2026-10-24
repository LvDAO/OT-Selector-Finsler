import OTSelector.Analysis.Calculus.SmoothCutoff
import OTSelector.Transport.Neumann.EndpointCoupling
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Conditions: A compact subset lies inside the interior of the larger compact smooth-test support in finite-dimensional real coordinates.

Objects: A genuine smooth cutoff supported in the larger compact and locally one around the smaller compact.

Proof detail: Use a finite collection of smooth local bumps subordinate to the open neighborhood and normalize/combine them to obtain an exact locally-one cutoff.

Sources: Hassler Whitney, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Smooth finite-dimensional localization from the classical partition construction; only the cutoff lemma is extracted, without the original Lipschitz-smoothing conclusions.
-/

/-!
# Lipschitz-preserving smooth approximation with pointwise gradient control

This file supplies the analytic input `CapturesLipschitzDual` of
`LegalRepairEndpointCoupling`.

* A genuine mollification of a `1`-Lipschitz function: convolution with a smooth
  normalized bump preserves the Lipschitz constant exactly, is smooth, and is
  uniformly close by the first moment of the bump.
* A smooth cutoff which is identically one on an open neighborhood of a compact
  set inside the interior of a larger compact set.

Their product keeps the exact dual value on the compact carrier and keeps the
physical gradient bounded there.
-/
open Set Metric MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Function
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction Convolution ContDiff ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Mollification -/

/-- The actual normalized smooth mollifier kernel. -/
def lipschitzMollifierKernel (b : ContDiffBump (0 : ι → ℝ)) : (ι → ℝ) → ℝ :=
  b.normed volume

/-- The literal mollification of a real function by the normalized bump. -/
def lipschitzMollification (b : ContDiffBump (0 : ι → ℝ)) (φ : (ι → ℝ) → ℝ) :
    (ι → ℝ) → ℝ :=
  φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] lipschitzMollifierKernel b

/-- The symmetric integral formula of the mollification. -/
theorem lipschitzMollification_apply (b : ContDiffBump (0 : ι → ℝ))
    (φ : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    lipschitzMollification b φ x =
      ∫ t, φ (x - t) * lipschitzMollifierKernel b t ∂volume := by
  rw [lipschitzMollification, convolution_lsmul_swap]
  simp only [smul_eq_mul]

/-- The mollification of a continuous function is smooth: the bump kernel is
smooth and compactly supported. -/
theorem contDiff_lipschitzMollification (b : ContDiffBump (0 : ι → ℝ))
    {φ : (ι → ℝ) → ℝ} (hφ : Continuous φ) :
    ContDiff ℝ ∞ (lipschitzMollification b φ) :=
  b.hasCompactSupport_normed.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hφ.locallyIntegrable b.contDiff_normed

/-- The kernel is nonnegative. -/
theorem kernel_nonneg (b : ContDiffBump (0 : ι → ℝ)) (t : ι → ℝ) :
    0 ≤ lipschitzMollifierKernel b t :=
  b.nonneg_normed t

/-- The kernel has unit mass. -/
theorem kernel_integral (b : ContDiffBump (0 : ι → ℝ)) :
    ∫ t, lipschitzMollifierKernel b t ∂volume = 1 :=
  b.integral_normed

/-- The kernel vanishes outside the ball of its outer radius. -/
theorem kernel_lt_rOut {b : ContDiffBump (0 : ι → ℝ)} {t : ι → ℝ}
    (ht : lipschitzMollifierKernel b t ≠ 0) : ‖t‖ < b.rOut := by
  have hmem : t ∈ Function.support (lipschitzMollifierKernel b) := by
    simpa only [Function.mem_support] using ht
  rw [lipschitzMollifierKernel, b.support_normed_eq] at hmem
  exact mem_ball_zero_iff.1 hmem

section MollificationBounds
variable {b : ContDiffBump (0 : ι → ℝ)} {φ : (ι → ℝ) → ℝ}

/-- The product of the Lipschitz function with the kernel is integrable. -/
theorem integrable_mul_kernel (hφ : LipschitzWith 1 φ) (x : ι → ℝ) :
    Integrable (fun t => φ (x - t) * lipschitzMollifierKernel b t) volume := by
  have hφc : Continuous φ := LipschitzWith.continuous hφ
  have hcont : Continuous
      (fun t : ι → ℝ => φ (x - t) * lipschitzMollifierKernel b t) :=
    Continuous.mul (Continuous.comp hφc (continuous_const.sub continuous_id))
      b.continuous_normed
  refine Integrable.mono' ((b.integrable_normed).const_mul (|φ x| + b.rOut))
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hgoal : |φ (x - t)| * lipschitzMollifierKernel b t ≤
      (|φ x| + b.rOut) * lipschitzMollifierKernel b t := by
    have hlip : |φ (x - t) - φ x| ≤ ‖t‖ := by
      have h := LipschitzWith.dist_le_mul hφ (x - t) x
      rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
      calc |φ (x - t) - φ x| ≤ ‖(x - t) - x‖ := h
        _ = ‖t‖ := by rw [show (x - t) - x = -t from by abel, norm_neg]
    have hφt : |φ (x - t)| ≤ |φ x| + ‖t‖ := by
      calc |φ (x - t)| = |(φ (x - t) - φ x) + φ x| := by ring_nf
        _ ≤ |φ (x - t) - φ x| + |φ x| := abs_add_le _ _
        _ ≤ ‖t‖ + |φ x| := by linarith
        _ = |φ x| + ‖t‖ := by ring
    by_cases hzero : lipschitzMollifierKernel b t = 0
    · rw [hzero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (by linarith [kernel_lt_rOut hzero])
        (kernel_nonneg b t)
  rw [Real.norm_eq_abs, abs_mul]
  change |φ (x - t)| * |b.normed volume t| ≤ (|φ x| + b.rOut) * b.normed volume t
  rw [abs_of_nonneg (b.nonneg_normed t)]
  exact hgoal

/-- The mollification is uniformly close to the Lipschitz function, with the
explicit error given by the outer radius of the bump. -/
theorem abs_lipschitzMollification_sub_le (hφ : LipschitzWith 1 φ) (x : ι → ℝ) :
    |lipschitzMollification b φ x - φ x| ≤ b.rOut := by
  have hφc : Continuous φ := LipschitzWith.continuous hφ
  have hρint : Integrable (lipschitzMollifierKernel b) volume := b.integrable_normed
  have hint : Integrable (fun t => φ (x - t) * lipschitzMollifierKernel b t) volume :=
    integrable_mul_kernel hφ x
  have hint2 : Integrable (fun t => φ x * lipschitzMollifierKernel b t) volume :=
    hρint.const_mul (φ x)
  have hsub : (∫ t, φ (x - t) * lipschitzMollifierKernel b t ∂volume) -
      (∫ t, φ x * lipschitzMollifierKernel b t ∂volume) =
      ∫ t, (φ (x - t) - φ x) * lipschitzMollifierKernel b t ∂volume := by
    rw [← integral_sub hint hint2]
    apply integral_congr_ae
    filter_upwards with t
    ring
  have hconst : (∫ t, φ x * lipschitzMollifierKernel b t ∂volume) = φ x := by
    rw [integral_const_mul, kernel_integral, mul_one]
  have hcont : Continuous
      (fun t : ι → ℝ => (φ (x - t) - φ x) * lipschitzMollifierKernel b t) :=
    Continuous.mul
      (Continuous.sub (Continuous.comp hφc (continuous_const.sub continuous_id))
        continuous_const) b.continuous_normed
  have hcontabs : Continuous
      (fun t : ι → ℝ => |φ (x - t) - φ x| * lipschitzMollifierKernel b t) :=
    (Continuous.abs
      (Continuous.sub (Continuous.comp hφc (continuous_const.sub continuous_id))
        continuous_const)).mul b.continuous_normed
  have hpt : ∀ t, |φ (x - t) - φ x| * lipschitzMollifierKernel b t ≤
      b.rOut * lipschitzMollifierKernel b t := by
    intro t
    have hlip : |φ (x - t) - φ x| ≤ ‖t‖ := by
      have h := LipschitzWith.dist_le_mul hφ (x - t) x
      rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
      calc |φ (x - t) - φ x| ≤ ‖(x - t) - x‖ := h
        _ = ‖t‖ := by rw [show (x - t) - x = -t from by abel, norm_neg]
    by_cases hzero : lipschitzMollifierKernel b t = 0
    · rw [hzero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (by linarith [kernel_lt_rOut hzero])
        (kernel_nonneg b t)
  have hleftInt : Integrable
      (fun t => |φ (x - t) - φ x| * lipschitzMollifierKernel b t) volume := by
    refine Integrable.mono' (hρint.const_mul b.rOut) hcontabs.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) (kernel_nonneg b t))]
    exact hpt t
  have hmono : (∫ t, |φ (x - t) - φ x| * lipschitzMollifierKernel b t ∂volume) ≤
      ∫ t, b.rOut * lipschitzMollifierKernel b t ∂volume :=
    integral_mono_ae hleftInt (hρint.const_mul b.rOut) (Eventually.of_forall hpt)
  have hright : (∫ t, b.rOut * lipschitzMollifierKernel b t ∂volume) = b.rOut := by
    rw [integral_const_mul, kernel_integral, mul_one]
  rw [lipschitzMollification_apply, ← hconst, hsub]
  calc |∫ t, (φ (x - t) - φ x) * lipschitzMollifierKernel b t ∂volume|
      = ‖∫ t, (φ (x - t) - φ x) * lipschitzMollifierKernel b t ∂volume‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, ‖(φ (x - t) - φ x) * lipschitzMollifierKernel b t‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = ∫ t, |φ (x - t) - φ x| * lipschitzMollifierKernel b t ∂volume := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg b t)]
    _ ≤ _ := hmono
    _ = b.rOut := hright

/-- Convolution with a smooth probability density preserves the Lipschitz
constant exactly. -/
theorem lipschitzWith_lipschitzMollification (hφ : LipschitzWith 1 φ) :
    LipschitzWith 1 (lipschitzMollification b φ) := by
  have hφc : Continuous φ := LipschitzWith.continuous hφ
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  have hρint : Integrable (lipschitzMollifierKernel b) volume := b.integrable_normed
  have hintp : Integrable (fun t => φ (p - t) * lipschitzMollifierKernel b t) volume :=
    integrable_mul_kernel hφ p
  have hintq : Integrable (fun t => φ (q - t) * lipschitzMollifierKernel b t) volume :=
    integrable_mul_kernel hφ q
  have hsub : (∫ t, φ (p - t) * lipschitzMollifierKernel b t ∂volume) -
      (∫ t, φ (q - t) * lipschitzMollifierKernel b t ∂volume) =
      ∫ t, (φ (p - t) - φ (q - t)) * lipschitzMollifierKernel b t ∂volume := by
    rw [← integral_sub hintp hintq]
    apply integral_congr_ae
    filter_upwards with t
    ring
  have hpt : ∀ t, |φ (p - t) - φ (q - t)| * lipschitzMollifierKernel b t ≤
      ‖p - q‖ * lipschitzMollifierKernel b t := by
    intro t
    have hlip : |φ (p - t) - φ (q - t)| ≤ ‖p - q‖ := by
      have h := LipschitzWith.dist_le_mul hφ (p - t) (q - t)
      rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
      calc |φ (p - t) - φ (q - t)| ≤ ‖(p - t) - (q - t)‖ := h
        _ = ‖p - q‖ := by rw [show (p - t) - (q - t) = p - q from by abel]
    exact mul_le_mul_of_nonneg_right hlip (kernel_nonneg b t)
  have hcontabs : Continuous
      (fun t : ι → ℝ => |φ (p - t) - φ (q - t)| * lipschitzMollifierKernel b t) :=
    (Continuous.abs
      (Continuous.sub (Continuous.comp hφc (continuous_const.sub continuous_id))
        (Continuous.comp hφc (continuous_const.sub continuous_id)))).mul
      b.continuous_normed
  have hleftInt : Integrable
      (fun t => |φ (p - t) - φ (q - t)| * lipschitzMollifierKernel b t) volume := by
    refine Integrable.mono' (hρint.const_mul ‖p - q‖) hcontabs.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) (kernel_nonneg b t))]
    exact hpt t
  have hmono : (∫ t, |φ (p - t) - φ (q - t)| * lipschitzMollifierKernel b t ∂volume) ≤
      ∫ t, ‖p - q‖ * lipschitzMollifierKernel b t ∂volume :=
    integral_mono_ae hleftInt (hρint.const_mul ‖p - q‖) (Eventually.of_forall hpt)
  have hright : (∫ t, ‖p - q‖ * lipschitzMollifierKernel b t ∂volume) = ‖p - q‖ := by
    rw [integral_const_mul, kernel_integral, mul_one]
  rw [lipschitzMollification_apply, lipschitzMollification_apply, hsub]
  calc |∫ t, (φ (p - t) - φ (q - t)) * lipschitzMollifierKernel b t ∂volume|
      = ‖∫ t, (φ (p - t) - φ (q - t)) * lipschitzMollifierKernel b t ∂volume‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, ‖(φ (p - t) - φ (q - t)) * lipschitzMollifierKernel b t‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = ∫ t, |φ (p - t) - φ (q - t)| * lipschitzMollifierKernel b t ∂volume := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg b t)]
    _ ≤ _ := hmono
    _ = ‖p - q‖ := hright

end MollificationBounds

/-! ## Smooth cutoff -/



/-! ## Pointwise gradient control and the capture statement -/

/-- The packed physical gradient of a smooth `1`-Lipschitz function is bounded in
squared norm by the cardinality of the coordinate index type. -/
theorem packedGradient_norm_sq_le_card
    {g : (ι → ℝ) → ℝ} (_hg : ContDiff ℝ ∞ g) (hlip : LipschitzWith 1 g)
    (x : ι → ℝ) :
    ‖physicalCoordinateGradient ι (fderiv ℝ g x)‖ ^ 2 ≤ (Fintype.card ι : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [physicalCoordinateGradient_apply]
  have hcomp : ∀ i : ι, (fderiv ℝ g x (Pi.single i 1)) ^ 2 ≤ 1 := by
    intro i
    have hle : |fderiv ℝ g x (Pi.single i 1)| ≤ 1 := by
      calc |fderiv ℝ g x (Pi.single i 1)|
          = ‖fderiv ℝ g x (Pi.single i 1)‖ := rfl
        _ ≤ ‖fderiv ℝ g x‖ * ‖Pi.single i 1‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * 1 := by
            refine mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hlip) ?_ (norm_nonneg _) ?_
            · rw [Pi.norm_single]
              norm_num
            · norm_num
        _ = 1 := one_mul 1
    have hle' := abs_le.mp hle
    nlinarith [hle'.1, hle'.2]
  calc ∑ i : ι, (fderiv ℝ g x (Pi.single i 1)) ^ 2
      ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hcomp i
    _ = (Fintype.card ι : ℝ) := by simp

/-- If the physical gradient of a smooth test agrees with the gradient of a
`1`-Lipschitz smooth function almost everywhere on the reference carrier, then
the test has the explicit Neumann energy bound. -/
theorem smoothPhysicalGradientLtwo_norm_le_of_ae_eq
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (ψ : 𝓓_{K}(ι → ℝ, ℝ)) {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hlip : LipschitzWith 1 g)
    (hagree : ∀ᵐ x ∂μ, fderiv ℝ ψ x = fderiv ℝ g x) :
    ‖smoothPhysicalGradientLtwo K μ ψ‖ ≤
      Real.sqrt ((Fintype.card ι : ℝ) * (μ univ).toReal) := by
  set j := smoothPhysicalGradientLtwo K μ ψ with hj
  have hjmem : MemLp (⇑j) 2 μ := Lp.memLp j
  have hjint : Integrable (fun x => ‖j x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hjmem.aestronglyMeasurable).mp hjmem
  have hpack_eq : (fun x => ‖j x‖ ^ 2) =ᵐ[μ]
      (fun x => ‖physicalCoordinateGradient ι (fderiv ℝ ψ x)‖ ^ 2) := by
    filter_upwards [smoothPhysicalGradientLtwo_ae K μ ψ] with x hx
    rw [hx]
  have hpack_int : Integrable
      (fun x => ‖physicalCoordinateGradient ι (fderiv ℝ ψ x)‖ ^ 2) μ :=
    hjint.congr hpack_eq
  have hbound_ae : (fun x => ‖physicalCoordinateGradient ι (fderiv ℝ ψ x)‖ ^ 2) ≤ᵐ[μ]
      (fun _ => (Fintype.card ι : ℝ)) := by
    filter_upwards [hagree] with x hx
    rw [hx]
    exact packedGradient_norm_sq_le_card hg hlip x
  have hIntLe : (∫ x, ‖physicalCoordinateGradient ι (fderiv ℝ ψ x)‖ ^ 2 ∂μ) ≤
      ∫ _x : ι → ℝ, (Fintype.card ι : ℝ) ∂μ :=
    integral_mono_ae hpack_int (integrable_const _) hbound_ae
  have hcardint : (∫ _x : ι → ℝ, (Fintype.card ι : ℝ) ∂μ) =
      (Fintype.card ι : ℝ) * (μ univ).toReal := by
    rw [integral_const, smul_eq_mul, mul_comm]
    rfl
  have hsq : ‖j‖ ^ 2 ≤ (Fintype.card ι : ℝ) * (μ univ).toReal := by
    rw [physicalFlux_norm_sq, integral_congr_ae hpack_eq]
    exact hIntLe.trans_eq hcardint
  calc ‖j‖ = Real.sqrt (‖j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg j)).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * (μ univ).toReal) := Real.sqrt_le_sqrt hsq

/-- **The capture theorem.** On a finite reference measure carried by a compact
set inside the interior of the test carrier, the compactly supported smooth tests
capture every `1`-Lipschitz dual value with physical gradient norm at most
`sqrt (card ι * μ univ)`. -/
theorem capturesLipschitzDual_of_compact_support
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ)
    (hprobS : IsProbabilityMeasure (residualDensityMeasure μ f))
    (hprobT : IsProbabilityMeasure (residualDensityMeasure μ g))
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀)
    (hμsupp : ∀ᵐ x ∂μ, x ∈ K₀)
    (hK₀K : K₀ ⊆ interior (K : Set (ι → ℝ))) :
    CapturesLipschitzDual K μ f g
      (Real.sqrt ((Fintype.card ι : ℝ) * (μ univ).toReal)) := by
  intro φ hφ ε hε
  have hφc : Continuous φ := LipschitzWith.continuous hφ
  obtain ⟨χ, hχsmooth, hχsupp, U, hUopen, hK₀U, hχone⟩ :=
    exists_contDiff_cutoff K hK₀ hK₀K
  let b : ContDiffBump (0 : ι → ℝ) :=
    ⟨ε / 8, ε / 4, by linarith, by linarith⟩
  have hbclose : ∀ x, |lipschitzMollification b φ x - φ x| ≤ ε / 2 := by
    intro x
    have h := abs_lipschitzMollification_sub_le (b := b) hφ x
    have hr : b.rOut = ε / 4 := rfl
    rw [hr] at h
    linarith
  have hg_contDiff : ContDiff ℝ ∞ (lipschitzMollification b φ) :=
    contDiff_lipschitzMollification b hφc
  have hg_lip : LipschitzWith 1 (lipschitzMollification b φ) :=
    lipschitzWith_lipschitzMollification hφ
  let ψ : (ι → ℝ) → ℝ := fun y => χ y * lipschitzMollification b φ y
  have hψsmooth : ContDiff ℝ ∞ ψ := hχsmooth.mul hg_contDiff
  have hψsupp : Function.support ψ ⊆ (K : Set (ι → ℝ)) := by
    intro y hy
    have hχne : χ y ≠ 0 := by
      intro h0
      refine hy ?_
      simp [ψ, h0]
    exact hχsupp (by simpa only [Function.mem_support] using hχne)
  let ψtest : 𝓓_{K}(ι → ℝ, ℝ) := ContDiffMapSupportedIn.of_support_subset hψsmooth hψsupp
  have hνsuppS : ∀ᵐ y ∂(residualDensityMeasure μ f), y ∈ K₀ :=
    (Measure.AbsolutelyContinuous.ae_le
      (MeasureTheory.withDensity_absolutelyContinuous μ (fun y => ENNReal.ofReal (f y))))
      hμsupp
  have hνsuppT : ∀ᵐ y ∂(residualDensityMeasure μ g), y ∈ K₀ :=
    (Measure.AbsolutelyContinuous.ae_le
      (MeasureTheory.withDensity_absolutelyContinuous μ (fun y => ENNReal.ofReal (g y))))
      hμsupp
  obtain ⟨R, hR⟩ := hK₀.isBounded.exists_norm_le
  have hφbound : ∀ y ∈ K₀, |φ y| ≤ |φ 0| + R := by
    intro y hy
    have h := LipschitzWith.dist_le_mul hφ y 0
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_zero_right] at h
    have h2 : |φ y| ≤ |φ y - φ 0| + |φ 0| := by
      calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
        _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
    linarith [hR y hy]
  have hφ_intS : Integrable φ (residualDensityMeasure μ f) := by
    refine Integrable.mono' (integrable_const (|φ 0| + R + 1)) hφc.aestronglyMeasurable ?_
    filter_upwards [hνsuppS] with y hy
    rw [Real.norm_eq_abs]
    linarith [hφbound y hy]
  have hg_intS : Integrable (lipschitzMollification b φ) (residualDensityMeasure μ f) := by
    refine Integrable.mono' (integrable_const (|φ 0| + R + ε / 2 + 1))
      hg_contDiff.continuous.aestronglyMeasurable ?_
    filter_upwards [hνsuppS] with y hy
    have h1 : |φ y| ≤ |φ 0| + R := hφbound y hy
    have h2 : |lipschitzMollification b φ y - φ y| ≤ ε / 2 := hbclose y
    have h3 : |lipschitzMollification b φ y| ≤ |φ y| + ε / 2 := by
      calc |lipschitzMollification b φ y|
          = |φ y + (lipschitzMollification b φ y - φ y)| := by ring_nf
        _ ≤ |φ y| + |lipschitzMollification b φ y - φ y| := abs_add_le _ _
        _ ≤ |φ y| + ε / 2 := by linarith
    rw [Real.norm_eq_abs]
    linarith
  have hφ_intT : Integrable φ (residualDensityMeasure μ g) := by
    refine Integrable.mono' (integrable_const (|φ 0| + R + 1)) hφc.aestronglyMeasurable ?_
    filter_upwards [hνsuppT] with y hy
    rw [Real.norm_eq_abs]
    linarith [hφbound y hy]
  have hg_intT : Integrable (lipschitzMollification b φ) (residualDensityMeasure μ g) := by
    refine Integrable.mono' (integrable_const (|φ 0| + R + ε / 2 + 1))
      hg_contDiff.continuous.aestronglyMeasurable ?_
    filter_upwards [hνsuppT] with y hy
    have h1 : |φ y| ≤ |φ 0| + R := hφbound y hy
    have h2 : |lipschitzMollification b φ y - φ y| ≤ ε / 2 := hbclose y
    have h3 : |lipschitzMollification b φ y| ≤ |φ y| + ε / 2 := by
      calc |lipschitzMollification b φ y|
          = |φ y + (lipschitzMollification b φ y - φ y)| := by ring_nf
        _ ≤ |φ y| + |lipschitzMollification b φ y - φ y| := abs_add_le _ _
        _ ≤ |φ y| + ε / 2 := by linarith
    rw [Real.norm_eq_abs]
    linarith
  have hcloseS : |(∫ y, φ y ∂(residualDensityMeasure μ f)) -
      ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ f)| ≤ ε / 2 := by
    rw [← integral_sub hφ_intS hg_intS]
    have hpt : ∀ᵐ y ∂(residualDensityMeasure μ f),
        ‖φ y - lipschitzMollification b φ y‖ ≤ ε / 2 := by
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hbclose y
    calc |∫ y, (φ y - lipschitzMollification b φ y) ∂(residualDensityMeasure μ f)|
        = ‖∫ y, (φ y - lipschitzMollification b φ y) ∂(residualDensityMeasure μ f)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖φ y - lipschitzMollification b φ y‖ ∂(residualDensityMeasure μ f) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _y, (ε / 2) ∂(residualDensityMeasure μ f) := by
          refine integral_mono_ae ?_ (integrable_const _) hpt
          refine Integrable.mono' (integrable_const (ε / 2))
            ((hφc.sub hg_contDiff.continuous).norm.aestronglyMeasurable) ?_
          filter_upwards [hpt] with y hy
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hy
      _ = ε / 2 := by
          rw [integral_const, smul_eq_mul]
          simp [Measure.real, measure_univ]
  have hcloseT : |(∫ y, φ y ∂(residualDensityMeasure μ g)) -
      ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ g)| ≤ ε / 2 := by
    rw [← integral_sub hφ_intT hg_intT]
    have hpt : ∀ᵐ y ∂(residualDensityMeasure μ g),
        ‖φ y - lipschitzMollification b φ y‖ ≤ ε / 2 := by
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hbclose y
    calc |∫ y, (φ y - lipschitzMollification b φ y) ∂(residualDensityMeasure μ g)|
        = ‖∫ y, (φ y - lipschitzMollification b φ y) ∂(residualDensityMeasure μ g)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖φ y - lipschitzMollification b φ y‖ ∂(residualDensityMeasure μ g) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _y, (ε / 2) ∂(residualDensityMeasure μ g) := by
          refine integral_mono_ae ?_ (integrable_const _) hpt
          refine Integrable.mono' (integrable_const (ε / 2))
            ((hφc.sub hg_contDiff.continuous).norm.aestronglyMeasurable) ?_
          filter_upwards [hpt] with y hy
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hy
      _ = ε / 2 := by
          rw [integral_const, smul_eq_mul]
          simp [Measure.real, measure_univ]
  have hvalS : (∫ y, ψtest y ∂(residualDensityMeasure μ f)) =
      ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ f) := by
    apply integral_congr_ae
    filter_upwards [hνsuppS] with y hy
    have hyU : y ∈ U := hK₀U hy
    show χ y * lipschitzMollification b φ y = lipschitzMollification b φ y
    rw [hχone y hyU, one_mul]
  have hvalT : (∫ y, ψtest y ∂(residualDensityMeasure μ g)) =
      ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ g) := by
    apply integral_congr_ae
    filter_upwards [hνsuppT] with y hy
    have hyU : y ∈ U := hK₀U hy
    show χ y * lipschitzMollification b φ y = lipschitzMollification b φ y
    rw [hχone y hyU, one_mul]
  have hagree : ∀ᵐ x ∂μ, fderiv ℝ ψtest x = fderiv ℝ (lipschitzMollification b φ) x := by
    filter_upwards [hμsupp] with x hx
    have hxU : x ∈ U := hK₀U hx
    have hev : ψ =ᶠ[𝓝 x] lipschitzMollification b φ := by
      filter_upwards [IsOpen.mem_nhds hUopen hxU] with y hy
      show χ y * lipschitzMollification b φ y = lipschitzMollification b φ y
      rw [hχone y hy, one_mul]
    exact Filter.EventuallyEq.fderiv_eq hev
  refine ⟨ψtest, ?_, ?_⟩
  · exact smoothPhysicalGradientLtwo_norm_le_of_ae_eq K μ ψtest hg_contDiff hg_lip hagree
  · rw [hvalS, hvalT]
    have h1 : ((∫ y, φ y ∂(residualDensityMeasure μ f)) -
        ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ f)) -
        ((∫ y, φ y ∂(residualDensityMeasure μ g)) -
        ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ g))
        = ((∫ y, φ y ∂(residualDensityMeasure μ f)) -
          ∫ y, φ y ∂(residualDensityMeasure μ g)) -
          ((∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ f)) -
          ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ g)) := by
      ring
    set A : ℝ := (∫ y, φ y ∂(residualDensityMeasure μ f)) -
      ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ f) with hA
    set B : ℝ := (∫ y, φ y ∂(residualDensityMeasure μ g)) -
      ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ g) with hB
    have hAB : (∫ y, φ y ∂(residualDensityMeasure μ f)) -
          ∫ y, φ y ∂(residualDensityMeasure μ g) -
          ((∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ f)) -
          ∫ y, lipschitzMollification b φ y ∂(residualDensityMeasure μ g)) = A - B := by
      rw [hA, hB]
      ring
    rw [hAB]
    calc |A - B| ≤ |A| + |B| := by
          rw [sub_eq_add_neg]
          have h := abs_add_le A (-B)
          rwa [abs_neg] at h
      _ ≤ ε / 2 + ε / 2 := by
          rw [hA, hB]
          linarith [hcloseS, hcloseT]
      _ = ε := by ring

end OTSelector.Reconstruction
