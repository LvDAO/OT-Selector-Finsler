import OTSelector.Reconstruction.FinslerOriginalKernelMarkedPoisson
import OTSelector.Probability.MarkedCloudCoupling
import OTSelector.Probability.MarkedPressureBlockSubadditivity
import OTSelector.Probability.MarkedPressureLimitBlock
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Block subadditivity for kernel-marked clouds

This module completes the Poisson side of the kernel-marked pressure lane:

* kernelCloudCouple / twoKernelCloudCouple are the prefix couplings of
  kernel-marked clouds at intensities rho and rho + delta: one common
  kernel-marked iid marked sequence with coupled Poisson counts.  The mark law is
  irrelevant to the construction, so the independent-mark coupling of
  MarkedCloudCoupling lifts verbatim;
* kernelMarkedScalePressure_block_le is the scale-level block comparison for
  coordinate-dependent mark kernels, with the same repair error as the
  independent-mark lane, conditional on the intensity-level comparison;
* at constant kernels the intensity-level comparison holds exactly
  (kernelMarkedPressure_le_blockScale_add_repair_const), giving the scale block
  comparison, the scale-pressure limit and, combined with the de-Poissonization
  of the kernel-marked lane, the fixed-size marked pressure limit.

The exact obstruction for genuinely position-dependent kernels is documented at
the end: the fixed-block leaf expectation identity needs the block-rescaled
marked sequence to have the same kernel-marked law, i.e. the mark kernel must be
invariant under the block rescaling, which for all block sizes forces a constant
kernel.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Topology ContDiff
open Metric
open OTSelector.Probability OTSelector.Geometry

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The prefix coupling of kernel-marked clouds -/

/-- The coupling of two kernel-marked clouds at intensities rho and rho + delta:
one common kernel-marked iid marked sequence and coupled Poisson counts. -/
noncomputable def kernelCloudCouple (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] (rho delta : ℝ≥0) :
    Measure ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) :=
  (OTSelector.Probability.countCouple rho delta).prod (kernelMarkedSeqLaw q A K)

/-- The smaller marginal of the kernel-marked cloud coupling is the kernel-marked
cloud at intensity rho. -/
theorem kernelCloudCouple_map_small (q : ℕ) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] (rho delta : ℝ≥0) :
    (kernelCloudCouple q A K rho delta).map (OTSelector.Probability.coupledSmall (q := q)) =
      kernelMarkedCloudLaw q A K rho := by
  unfold kernelCloudCouple OTSelector.Probability.coupledSmall kernelMarkedCloudLaw
  rw [show (fun z : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) => (z.1.1, z.2)) =
      Prod.map Prod.fst id from rfl]
  rw [← Measure.map_prod_map]
  · rw [OTSelector.Probability.countCouple_map_fst, Measure.map_id]
  · exact measurable_fst
  · exact measurable_id

/-- The larger marginal of the kernel-marked cloud coupling is the kernel-marked
cloud at intensity rho + delta. -/
theorem kernelCloudCouple_map_large (q : ℕ) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] (rho delta : ℝ≥0) :
    (kernelCloudCouple q A K rho delta).map (OTSelector.Probability.coupledLarge (q := q)) =
      kernelMarkedCloudLaw q A K (rho + delta) := by
  unfold kernelCloudCouple OTSelector.Probability.coupledLarge kernelMarkedCloudLaw
  rw [show (fun z : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) => (z.1.2, z.2)) =
      Prod.map Prod.snd id from rfl]
  rw [← Measure.map_prod_map]
  · rw [OTSelector.Probability.countCouple_map_snd, Measure.map_id]
  · exact measurable_snd
  · exact measurable_id

/-- The two-cloud prefix coupling of kernel-marked clouds. -/
noncomputable def twoKernelCloudCouple (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (rho delta : ℝ≥0) :
    Measure (((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B))) :=
  (kernelCloudCouple q A Ks rho delta).prod (kernelCloudCouple q B Kt rho delta)

/-- The rho two-cloud marginal of the kernel-marked coupling. -/
theorem twoKernelCloudCouple_map_small (q : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (rho delta : ℝ≥0) :
    (twoKernelCloudCouple q A B Ks Kt rho delta).map
        (fun z => (OTSelector.Probability.coupledSmall (q := q) z.1,
          OTSelector.Probability.coupledSmall (q := q) z.2)) =
      twoKernelMarkedCloudLaw q A B Ks Kt rho := by
  haveI hcount : IsProbabilityMeasure (OTSelector.Probability.countCouple rho delta) := by
    unfold OTSelector.Probability.countCouple
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI hcloudA : IsProbabilityMeasure (kernelCloudCouple q A Ks rho delta) := by
    unfold kernelCloudCouple
    infer_instance
  haveI hcloud : IsProbabilityMeasure (kernelCloudCouple q B Kt rho delta) := by
    unfold kernelCloudCouple
    infer_instance
  unfold twoKernelCloudCouple twoKernelMarkedCloudLaw
  rw [show (fun z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
        ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      (OTSelector.Probability.coupledSmall (q := q) z.1,
        OTSelector.Probability.coupledSmall (q := q) z.2)) =
      Prod.map (OTSelector.Probability.coupledSmall (q := q))
        (OTSelector.Probability.coupledSmall (q := q)) from rfl]
  rw [← Measure.map_prod_map]
  · rw [kernelCloudCouple_map_small, kernelCloudCouple_map_small]
  · exact OTSelector.Probability.measurable_coupledSmall q
  · exact OTSelector.Probability.measurable_coupledSmall q

/-- The rho + delta two-cloud marginal of the kernel-marked coupling. -/
theorem twoKernelCloudCouple_map_large (q : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (rho delta : ℝ≥0) :
    (twoKernelCloudCouple q A B Ks Kt rho delta).map
        (fun z => (OTSelector.Probability.coupledLarge (q := q) z.1,
          OTSelector.Probability.coupledLarge (q := q) z.2)) =
      twoKernelMarkedCloudLaw q A B Ks Kt (rho + delta) := by
  haveI hcount : IsProbabilityMeasure (OTSelector.Probability.countCouple rho delta) := by
    unfold OTSelector.Probability.countCouple
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI hcloudA : IsProbabilityMeasure (kernelCloudCouple q A Ks rho delta) := by
    unfold kernelCloudCouple
    infer_instance
  haveI hcloud : IsProbabilityMeasure (kernelCloudCouple q B Kt rho delta) := by
    unfold kernelCloudCouple
    infer_instance
  unfold twoKernelCloudCouple twoKernelMarkedCloudLaw
  rw [show (fun z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
        ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      (OTSelector.Probability.coupledLarge (q := q) z.1,
        OTSelector.Probability.coupledLarge (q := q) z.2)) =
      Prod.map (OTSelector.Probability.coupledLarge (q := q))
        (OTSelector.Probability.coupledLarge (q := q)) from rfl]
  rw [← Measure.map_prod_map]
  · rw [kernelCloudCouple_map_large, kernelCloudCouple_map_large]
  · exact OTSelector.Probability.measurable_coupledLarge q
  · exact OTSelector.Probability.measurable_coupledLarge q

theorem kernelMarkedScalePressure_block_le
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hpressure : ∀ R : ℝ≥0,
      kernelMarkedPressure q A B Ks Kt R kin g t ≤
        (((m ^ q : ℕ) : ℝ)) *
            kernelMarkedPressure q A B Ks Kt (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
          gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
            (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
              Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))))
    {L : ℝ} (hL : 0 < L) :
    kernelMarkedScalePressure q A B Ks Kt kin g ((m : ℝ) * L) t ≤
      kernelMarkedScalePressure q A B Ks Kt kin g L t +
        gridRepairError q (gridRepairConstant q) C G t L := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmL : (0 : ℝ) < (m : ℝ) * L := mul_pos hmR hL
  have hLq : (0 : ℝ) < L ^ q := pow_pos hL q
  rw [kernelMarkedScalePressure_of_pos q A B Ks Kt hmL, kernelMarkedScalePressure_of_pos q A B Ks Kt hL]
  -- The reduced intensity is `L ^ q`.
  have hred : ((Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) = L ^ q := by
    rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity)]
    push_cast
    exact mul_pow_div_pow q m hm L
  have hred_eq : (Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0)) =
      Real.toNNReal (L ^ q) := by
    apply NNReal.coe_injective
    rw [hred, Real.coe_toNNReal _ hLq.le]
  -- Rewrite the pressure comparison at intensity `(m L) ^ q` in plain real form.
  have hbase := hpressure (Real.toNNReal (((m : ℝ) * L) ^ q))
  have hcoe : ((Real.toNNReal (((m : ℝ) * L) ^ q) : ℝ≥0) : ℝ) = ((m : ℝ) * L) ^ q :=
    Real.coe_toNNReal _ (by positivity)
  rw [hcoe, mul_pow_div_pow q m hm L] at hbase
  -- The first term simplifies to the pressure at scale `L`.
  have hfirst : ((((m ^ q : ℕ) : ℝ)) *
        kernelMarkedPressure q A B Ks Kt
          (Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0)) kin g t) /
        (((m : ℝ) * L) ^ q) =
      kernelMarkedPressure q A B Ks Kt (Real.toNNReal (L ^ q)) kin g t / L ^ q := by
    rw [hred_eq, mul_pow]
    field_simp
    rw [Nat.cast_pow]
    ring
  -- The error term simplifies to `gridRepairError` at scale `L`.
  have hLrpow : ∀ a : ℝ, Real.rpow (L ^ q) a = L ^ ((q : ℝ) * a) := by
    intro a
    rw [← Real.rpow_natCast L q]
    exact (Real.rpow_mul hL.le (q : ℝ) a).symm
  have herr : (gridRepairConstant q * (C + |t| * G) * (((m : ℝ) * L) ^ q) *
        (Real.rpow (L ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow (L ^ q) (-(1 / 2)))) /
        (((m : ℝ) * L) ^ q) =
      gridRepairError q (gridRepairConstant q) C G t L := by
    rw [hLrpow, hLrpow]
    have h1 : (q : ℝ) * (2 / (q : ℝ) - 1 / 2) = 2 - (q : ℝ) / 2 := by
      field_simp
    have h2 : (q : ℝ) * (-(1 / 2)) = -((q : ℝ) / 2) := by ring
    rw [h1, h2]
    unfold gridRepairError
    rw [mul_pow]
    field_simp
    rfl
  calc kernelMarkedPressure q A B Ks Kt (Real.toNNReal (((m : ℝ) * L) ^ q)) kin g t /
        (((m : ℝ) * L) ^ q)
      ≤ ((((m ^ q : ℕ) : ℝ)) *
          kernelMarkedPressure q A B Ks Kt
            (Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
        gridRepairConstant q * (C + |t| * G) * (((m : ℝ) * L) ^ q) *
          (Real.rpow (L ^ q) (2 / (q : ℝ) - 1 / 2) +
            Real.rpow (L ^ q) (-(1 / 2)))) /
        (((m : ℝ) * L) ^ q) :=
        div_le_div_of_nonneg_right hbase (le_of_lt (pow_pos hmL q))
    _ = kernelMarkedPressure q A B Ks Kt (Real.toNNReal (L ^ q)) kin g t / L ^ q +
          gridRepairError q (gridRepairConstant q) C G t L := by
        rw [add_div, hfirst, herr]

/-! ## Block subadditivity at constant kernels -/

/-- **Intensity-level block comparison at constant kernels.**  For constant mark
kernels the kernel-marked block comparison is exactly the independent-mark one. -/
theorem kernelMarkedPressure_le_blockScale_add_repair_const
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    kernelMarkedPressure q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) R kin g t ≤
      (((m ^ q : ℕ) : ℝ)) * kernelMarkedPressure q A B
          (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β)
          (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
        gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
          (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
            Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))) := by
  rw [kernelMarkedPressure_const q A B α β R kin g t,
    kernelMarkedPressure_const q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t]
  exact markedPressure_le_blockScale_add_repair q m J hq hm hJ hJ2 α β R hC0 hG0
    hkin hkin_nonneg hkin_bound hkin_homog hg hgb

/-- **Scale-level block comparison at constant kernels.** -/
theorem kernelMarkedScalePressure_block_le_const
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {L : ℝ} (hL : 0 < L) :
    kernelMarkedScalePressure q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) kin g ((m : ℝ) * L) t ≤
      kernelMarkedScalePressure q A B (Kernel.const (Fin q → ℝ) α)
          (Kernel.const (Fin q → ℝ) β) kin g L t +
        gridRepairError q (gridRepairConstant q) C G t L :=
  kernelMarkedScalePressure_block_le q m J hq hm hJ hJ2
    (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β)
    (fun R => kernelMarkedPressure_le_blockScale_add_repair_const q m J hq hm hJ hJ2
      α β R hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb) hL

/-! ## The pressure limit at constant kernels -/

/-- **Scale-pressure limit at constant kernels.**  The kernel-marked scale
pressure at constant kernels inherits the independent-mark limit. -/
theorem exists_kernelMarkedScalePressure_limit_const
    (q : ℕ) (hq : 4 < q)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R => kernelMarkedScalePressure q A B
          (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) kin g R t)
        atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ Set.univ p ∧ LipschitzWith ⟨G, hG0⟩ p := by
  obtain ⟨p, hp, hconc, hlip⟩ :=
    exists_markedScalePressure_limit q hq α β hC0 hG0
      hkin hkin_nonneg hkin_bound hkin_homog hg hgb
  refine ⟨p, fun t => ?_, hconc, hlip⟩
  have hpt := hp t
  rwa [show (fun R => kernelMarkedScalePressure q A B
        (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) kin g R t) =
      fun R => markedScalePressure q A B α β kin g R t from by
    funext R
    exact kernelMarkedScalePressure_const q A B α β kin g R t]

/-- **Fixed-size marked pressure limit at constant kernels.**  Composing the
scale-pressure limit with the de-Poissonization of the kernel-marked lane gives
the fixed-size pressure limit for kernel-marked clouds at constant kernels. -/
theorem tendsto_kernelMarkedFixedPressure_div_const
    (q : ℕ) (hq : 4 < q)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ → ℝ}
    (hp : ∀ t, Tendsto (fun R => kernelMarkedScalePressure q A B
        (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) kin g R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun n : ℕ =>
        (∫ x, markedFixedValue q (n : ℝ) t kin g n x ∂(twoKernelMarkedCloudLaw q A B (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) (n : ℝ≥0))) / (n : ℝ))
      atTop (𝓝 (p t)) :=
  tendsto_kernelMarkedFixedPressure_div q hq hC0 hG0 hkin hkin_bound hg hgb
    (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) p hp

/-- **The complete marked pressure limit chain at constant kernels.** -/
theorem exists_kernelMarked_limit_const
    (q : ℕ) (hq : 4 < q)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R => kernelMarkedScalePressure q A B
          (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) kin g R t)
        atTop (𝓝 (p t))) ∧
      (∀ t, Tendsto (fun n : ℕ =>
          (∫ x, markedFixedValue q (n : ℝ) t kin g n x ∂(twoKernelMarkedCloudLaw q A B (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) (n : ℝ≥0))) / (n : ℝ))
        atTop (𝓝 (p t))) := by
  obtain ⟨p, hp, -, -⟩ :=
    exists_kernelMarkedScalePressure_limit_const q hq α β hC0 hG0
      hkin hkin_nonneg hkin_bound hkin_homog hg hgb
  exact ⟨p, hp, tendsto_kernelMarkedFixedPressure_div_const q hq α β hC0 hG0
    hkin hkin_bound hg hgb hp⟩

/-! ## The obstruction for genuinely position-dependent kernels

The intensity-level block comparison of the independent-mark lane is proved from
the deterministic grid comparison together with the **fixed-leaf expectation
identity**: the expected sum of the optimal leaf-block values at intensity R
equals m^q times the pressure at the reduced intensity R / m^q.  That identity
compares the law of the points of one leaf block, rescaled to the unit cube, with
the cloud law at reduced intensity.

For a coordinate-dependent mark kernel K this comparison fails in general.  A
point of the block at position x carries the mark drawn from K x; after the block
rescaling its position is x' = m (x - corner), but its mark is still drawn from
K (corner + x'/m), whereas the reduced-intensity kernel-marked cloud would draw
the mark from K x'.  Hence the leaf identity requires the block-rescaling
invariance

  K (corner + x'/m) = K x'  for every block and every rescaling factor m,

which for all block sizes and all positions forces K to be an almost everywhere
constant kernel.  The prefix coupling and the scale-level block comparison above
are mark-law agnostic; the intensity-level comparison, and hence the general
kernel-marked pressure limit, therefore remains open beyond the constant-kernel
case without a new quantitative comparison of the mark kernel's modulus of
continuity against the block scale.
-/

end OTSelector.Reconstruction
