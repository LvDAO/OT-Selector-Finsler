import OTSelector.Reconstruction.FinslerOriginalConditionalKernelPressure
import OTSelector.Probability.MarkedDePoissonization
import OTSelector.Probability.MarkedPressureLimit
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Kernel-marked Poisson clouds and de-Poissonization

The marked pressure lane is built on two independent marked Poisson clouds with
iid marks `α`, `β`.  The population atlas, however, produces marks conditionally on
the seed label (the clock coordinate): the marked points of a cell have the law
`cubeMeasure ⊗ₘ K`, with `K` a coordinate-dependent Markov kernel.  This module
lifts the conditional-kernel model of `FinslerOriginalConditionalKernelPressure` to the
Poisson cloud and to the marked pressure limit theory:

* `kernelMarkedSeqLaw` is the iid sequence law of kernel-marked cube points,
  `Measure.infinitePi (fun _ => cubeMeasure ⊗ₘ K)`;
* `kernelMarkedCloudLaw` is the kernel-marked Poisson cloud law (Poisson count times
  the kernel-marked iid sequence), and `twoKernelMarkedCloudLaw` its two-cloud form;
* `kernelMarkedPressure` and `kernelMarkedScalePressure` are the Poissonized marked
  pressure and its scale-normalized form for coordinate-dependent marks.

The main results are:

* `map_kernelMarkedCounts_twoKernelMarkedCloudLaw`: the two cloud counts are independent
  Poisson variables, exactly as in the independent-mark lane;
* `integral_abs_mSourceCount_sub_le_kernel` and the target counterpart: the count
  deviation bounds hold for the kernel-marked cloud;
* `abs_kernelMarkedPressure_sub_fixed_div_le`: **de-Poissonization** — the
  kernel-marked Poissonized pressure and the fixed-sample-size expectation of the
  marked block value differ by `O(n^{-1/2})` after division by `n`, with the same
  explicit constant as the independent-mark lane;
* `tendsto_kernelMarkedFixedPressure_div`: the fixed-size pressure inherits the
  Poissonized pressure limit;
* `twoKernelMarkedCloudLaw_const`, `kernelMarkedPressure_const` and
  `kernelMarkedScalePressure_const`: the constant-kernel special case recovers the
  existing independent-mark results exactly.

The concrete instantiation of `K` as the normalized clock density
`t ↦ J(t,w) ρ(t,w)` is not constructed here: the cube-partition lane supplies the
unnormalized Haar/Fubini form, and the normalized Markov kernel (joint
measurability plus a.e. positivity of the normalizer) is the remaining producer
step.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Topology
open OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## Kernel-marked clouds -/

/-- The iid sequence law of kernel-marked cube points: positions are cube-uniform
and the mark is drawn from the coordinate-dependent kernel given the position. -/
noncomputable def kernelMarkedSeqLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] : Measure (ℕ → (Fin q → ℝ) × A) :=
  haveI hc : IsProbabilityMeasure (OTSelector.Probability.cubeMeasure (Fin q) 1) :=
    OTSelector.Probability.isProbabilityMeasure_cubeMeasure (by norm_num)
  letI : ∀ _ : ℕ, IsProbabilityMeasure
      (OTSelector.Probability.cubeMeasure (Fin q) 1 ⊗ₘ K) := fun _ => inferInstance
  Measure.infinitePi fun _ : ℕ => OTSelector.Probability.cubeMeasure (Fin q) 1 ⊗ₘ K

instance isProbabilityMeasure_kernelMarkedSeqLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] :
    IsProbabilityMeasure (kernelMarkedSeqLaw q A K) := by
  unfold kernelMarkedSeqLaw
  infer_instance

/-- The kernel-marked Poisson cloud law: a Poisson count times the kernel-marked
iid sequence of cube points. -/
noncomputable def kernelMarkedCloudLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] (r : ℝ≥0) :
    Measure (MarkedCloudSpace q A) :=
  (poissonMeasure r).prod (kernelMarkedSeqLaw q A K)

instance isProbabilityMeasure_kernelMarkedCloudLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] (r : ℝ≥0) :
    IsProbabilityMeasure (kernelMarkedCloudLaw q A K r) := by
  unfold kernelMarkedCloudLaw
  infer_instance

/-- Two independent kernel-marked Poisson clouds with common mean count. -/
noncomputable def twoKernelMarkedCloudLaw (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    Measure (TwoMarkedCloudSpace q A B) :=
  (kernelMarkedCloudLaw q A Ks r).prod (kernelMarkedCloudLaw q B Kt r)

instance isProbabilityMeasure_twoKernelMarkedCloudLaw (q : ℕ) (A B : Type*)
    [MeasurableSpace A] [MeasurableSpace B] (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    IsProbabilityMeasure (twoKernelMarkedCloudLaw q A B Ks Kt r) := by
  unfold twoKernelMarkedCloudLaw
  infer_instance

/-- The kernel-marked marked Poissonized pressure. -/
noncomputable def kernelMarkedPressure (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, markedTilted (q := q) (r := (r : ℝ)) kin g t ω
    ∂(twoKernelMarkedCloudLaw q A B Ks Kt r)

/-- The scale-normalized kernel-marked pressure: intensity `R ^ q` normalized by
`R ^ q`, and zero at nonpositive scales. -/
noncomputable def kernelMarkedScalePressure (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (R t : ℝ) : ℝ :=
  if 0 < R then kernelMarkedPressure q A B Ks Kt (Real.toNNReal (R ^ q)) kin g t / R ^ q else 0

/-- The value of the scale-normalized kernel-marked pressure at a positive
scale. -/
theorem kernelMarkedScalePressure_of_pos (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {R t : ℝ} (hR : 0 < R) :
    kernelMarkedScalePressure q A B Ks Kt kin g R t =
      kernelMarkedPressure q A B Ks Kt (Real.toNNReal (R ^ q)) kin g t / R ^ q := by
  unfold kernelMarkedScalePressure
  rw [if_pos hR]

/-! ## The constant-kernel reduction -/

/-- The kernel-marked sequence law with constant kernel is the independent-mark
sequence law. -/
theorem kernelMarkedSeqLaw_const (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] :
    kernelMarkedSeqLaw q A (Kernel.const (Fin q → ℝ) α) = markedSeqLaw (q := q) A α := by
  unfold kernelMarkedSeqLaw markedSeqLaw
  simp only [Measure.compProd_const]

/-- The kernel-marked cloud law with constant kernel is the independent-mark
cloud law. -/
theorem kernelMarkedCloudLaw_const (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (r : ℝ≥0) :
    kernelMarkedCloudLaw q A (Kernel.const (Fin q → ℝ) α) r =
      markedPoissonLaw (q := q) A α r := by
  unfold kernelMarkedCloudLaw markedPoissonLaw
  rw [kernelMarkedSeqLaw_const]

/-- The two-cloud kernel-marked law with constant kernels is the
independent-mark two-cloud law. -/
theorem twoKernelMarkedCloudLaw_const (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    twoKernelMarkedCloudLaw q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) r =
      twoMarkedCloudLaw (q := q) A B α β r := by
  unfold twoKernelMarkedCloudLaw twoMarkedCloudLaw
  rw [kernelMarkedCloudLaw_const, kernelMarkedCloudLaw_const]

/-- **The constant-kernel reduction of the pressure.**  For constant mark kernels
the kernel-marked Poissonized pressure is exactly the independent-mark pressure:
the existing independent-mark limit theory is the constant-kernel special case. -/
theorem kernelMarkedPressure_const (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) :
    kernelMarkedPressure q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) r kin g t =
      markedPressure q A B α β r kin g t := by
  unfold kernelMarkedPressure markedPressure
  rw [twoKernelMarkedCloudLaw_const]

/-- The scale-normalized pressure reduces to the independent-mark scale pressure
for constant kernels. -/
theorem kernelMarkedScalePressure_const (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (R t : ℝ) :
    kernelMarkedScalePressure q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) kin g R t =
      markedScalePressure q A B α β kin g R t := by
  unfold kernelMarkedScalePressure markedScalePressure
  rw [kernelMarkedPressure_const]

/-! ## Count laws and count integrability -/

/-- The source count is integrable under the kernel-marked cloud law. -/
theorem integrable_mSourceCount_kernel (q : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B => ((mSourceCount ω : ℕ) : ℝ))
      (twoKernelMarkedCloudLaw q A B Ks Kt r) := by
  have h1 : Integrable (fun z : MarkedCloudSpace q A => ((z.1 : ℕ) : ℝ))
      (kernelMarkedCloudLaw q A Ks r) := by
    unfold kernelMarkedCloudLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  unfold twoKernelMarkedCloudLaw mSourceCount
  exact h1.comp_fst _

/-- The target count is integrable under the kernel-marked cloud law. -/
theorem integrable_mTargetCount_kernel (q : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B => ((mTargetCount ω : ℕ) : ℝ))
      (twoKernelMarkedCloudLaw q A B Ks Kt r) := by
  have h1 : Integrable (fun z : MarkedCloudSpace q B => ((z.1 : ℕ) : ℝ))
      (kernelMarkedCloudLaw q B Kt r) := by
    unfold kernelMarkedCloudLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  unfold twoKernelMarkedCloudLaw mTargetCount
  exact h1.comp_snd _

/-- The minimum count is integrable under the kernel-marked cloud law. -/
theorem integrable_mMinCount_kernel (q : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ))
      (twoKernelMarkedCloudLaw q A B Ks Kt r) := by
  have hsrc := integrable_mSourceCount_kernel q Ks Kt r
  have htgt := integrable_mTargetCount_kernel q Ks Kt r
  refine (hsrc.add htgt).mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable
      (Measurable.comp measurable_from_nat
        ((measurable_mSourceCount q).min (measurable_mTargetCount q)))
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ≤ (mSourceCount ω : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ (mSourceCount ω : ℝ) + (mTargetCount ω : ℝ) :=
          le_add_of_nonneg_right (Nat.cast_nonneg _)

/-- **The joint law of the kernel-marked cloud counts.**  The two counts are
independent Poisson variables, exactly as in the independent-mark lane: the mark
kernel does not affect the count law. -/
theorem map_kernelMarkedCounts_twoKernelMarkedCloudLaw (q : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    (twoKernelMarkedCloudLaw q A B Ks Kt r).map
        (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) =
      (poissonMeasure r).prod (poissonMeasure r) := by
  have hsrc : (kernelMarkedCloudLaw q A Ks r).map
      (fun z : MarkedCloudSpace q A => z.1) = poissonMeasure r := by
    rw [kernelMarkedCloudLaw, Measure.map_fst_prod, measure_univ, one_smul]
  have htgt : (kernelMarkedCloudLaw q B Kt r).map
      (fun z : MarkedCloudSpace q B => z.1) = poissonMeasure r := by
    rw [kernelMarkedCloudLaw, Measure.map_fst_prod, measure_univ, one_smul]
  have hcomp : (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) =
      Prod.map (fun z : MarkedCloudSpace q A => z.1)
        (fun z : MarkedCloudSpace q B => z.1) := rfl
  rw [hcomp, twoKernelMarkedCloudLaw,
    ← Measure.map_prod_map _ _ measurable_fst measurable_fst, hsrc, htgt]

/-! ## Count deviation bounds -/

theorem integral_abs_mSourceCount_sub_le_kernel (q : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        |((mSourceCount ω : ℕ) : ℝ) - (r : ℝ)|
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt r) ≤ Real.sqrt (r : ℝ) := by
  have hmap := map_kernelMarkedCounts_twoKernelMarkedCloudLaw q Ks Kt r
  have hmeas : Measurable
      (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) :=
    (measurable_mSourceCount q).prodMk (measurable_mTargetCount q)
  have hcont : Continuous (fun z : ℕ × ℕ => |(z.1 : ℝ) - (r : ℝ)|) := by
    continuity
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable, hmap]
  have hfst : Measure.map Prod.fst ((poissonMeasure r).prod (poissonMeasure r)) =
      poissonMeasure r := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  calc ∫ z : ℕ × ℕ, |(z.1 : ℝ) - (r : ℝ)|
        ∂((poissonMeasure r).prod (poissonMeasure r))
      = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂Measure.map Prod.fst
          ((poissonMeasure r).prod (poissonMeasure r)) := by
        rw [integral_map measurable_fst.aemeasurable (by fun_prop :
          AEStronglyMeasurable (fun n : ℕ => |(n : ℝ) - (r : ℝ)|)
            (Measure.map Prod.fst ((poissonMeasure r).prod (poissonMeasure r))))]
    _ = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂(poissonMeasure r) := by rw [hfst]
    _ ≤ Real.sqrt (r : ℝ) := integral_abs_sub_id_poissonMeasure_le r

/-- The expected deviation of the target Poisson count from `r` is at most
`sqrt r`. -/
theorem integral_abs_mTargetCount_sub_le_kernel (q : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        |((mTargetCount ω : ℕ) : ℝ) - (r : ℝ)|
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt r) ≤ Real.sqrt (r : ℝ) := by
  have hmap := map_kernelMarkedCounts_twoKernelMarkedCloudLaw q Ks Kt r
  have hmeas : Measurable
      (fun ω : TwoMarkedCloudSpace q A B => (mSourceCount ω, mTargetCount ω)) :=
    (measurable_mSourceCount q).prodMk (measurable_mTargetCount q)
  have hcont : Continuous (fun z : ℕ × ℕ => |(z.2 : ℝ) - (r : ℝ)|) := by
    continuity
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable, hmap]
  have hsnd : Measure.map Prod.snd ((poissonMeasure r).prod (poissonMeasure r)) =
      poissonMeasure r := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  calc ∫ z : ℕ × ℕ, |(z.2 : ℝ) - (r : ℝ)|
        ∂((poissonMeasure r).prod (poissonMeasure r))
      = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂Measure.map Prod.snd
          ((poissonMeasure r).prod (poissonMeasure r)) := by
        rw [integral_map measurable_snd.aemeasurable (by fun_prop :
          AEStronglyMeasurable (fun n : ℕ => |(n : ℝ) - (r : ℝ)|)
            (Measure.map Prod.snd ((poissonMeasure r).prod (poissonMeasure r))))]
    _ = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂(poissonMeasure r) := by rw [hsnd]
    _ ≤ Real.sqrt (r : ℝ) := integral_abs_sub_id_poissonMeasure_le r

/-! ## Integrability of the Poissonized marked value -/

theorem integrable_markedTilted_kernel (q : ℕ) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) {C G : ℝ}
    (hr : 0 ≤ (r : ℝ)) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (markedTilted (q := q) (r := (r : ℝ)) kin g t)
      (twoKernelMarkedCloudLaw q A B Ks Kt r) := by
  have hmeas := measurable_markedTilted (q := q) (r := (r : ℝ)) (C := C) (G := G)
    hr hC0 hG0 hkin hkin_bound hg hgb t
  have hcount := integrable_mMinCount_kernel q Ks Kt r
  have hbound : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) *
        (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G))
      (twoKernelMarkedCloudLaw q A B Ks Kt r) :=
    hcount.mul_const _
  refine hbound.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  unfold markedTilted tiltedCloudValue
  have hpt : ∀ i : Fin (mSourceCount ω), ∀ j : Fin (mTargetCount ω),
      |mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
          t * mProbe g ω (i : ℕ) (j : ℕ)| ≤
        r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
    intro i j
    have h1 := abs_mKineticCost_le q hr hC0 hkin_bound ω (i : ℕ) (j : ℕ)
    have h2 := abs_mProbe_le q hgb ω (i : ℕ) (j : ℕ)
    calc |mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) + t * mProbe g ω (i : ℕ) (j : ℕ)|
        ≤ |mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ)| +
            |t * mProbe g ω (i : ℕ) (j : ℕ)| := abs_add_le _ _
      _ ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
          rw [abs_mul]
          gcongr
  calc |PartialMatching.maxCardValue
        (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
          mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
            t * mProbe g ω (i : ℕ) (j : ℕ))|
      ≤ ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) *
          (r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) :=
        PartialMatching.abs_maxCardValue_perturbed_le
          (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
            mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ))
          (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
            mProbe g ω (i : ℕ) (j : ℕ))
          (fun i j => abs_mKineticCost_le q hr hC0 hkin_bound ω (i : ℕ) (j : ℕ))
          (mul_nonneg (Real.rpow_nonneg hr _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
          (fun i j => abs_mProbe_le q hgb ω (i : ℕ) (j : ℕ))
          hG0

/-! ## De-Poissonization -/

theorem abs_kernelMarkedPressure_sub_fixed_div_le
    (q : ℕ) {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] {n : ℕ} (hn : 0 < n) :
    |kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t / (n : ℝ) -
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))) / (n : ℝ)| ≤
      4 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  classical
  set Bnd : ℝ := (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G with hBnd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hBnd0 : 0 ≤ Bnd := by
    rw [hBnd]
    have h1 : 0 ≤ (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) := by positivity
    have h2 : 0 ≤ |t| * G := by positivity
    linarith
  -- Integrability of the Poissonized marked value.
  have hIntT : Integrable (markedTilted q (n : ℝ) kin g t)
      (twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) :=
    integrable_markedTilted_kernel q Ks Kt (n : ℝ≥0) (by positivity) hC0 hG0
      hkin hkin_bound hg hgb t
  -- Integrability and boundedness of the fixed value.
  have hmeas_fixed : Measurable (markedFixedValue q (n : ℝ) t kin g n) := by
    unfold markedFixedValue
    exact PartialMatching.measurable_maxCardValue _
      (fun i j => (measurable_mKineticCost q (n : ℝ) hkin (i : ℕ) (j : ℕ)).add
        ((measurable_mProbe q hg (i : ℕ) (j : ℕ)).const_mul t))
  have hbound_fixed : ∀ ω : TwoMarkedCloudSpace q A B,
      |markedFixedValue q (n : ℝ) t kin g n ω| ≤ (n : ℝ) * Bnd := by
    intro ω
    unfold markedFixedValue
    have h := PartialMatching.abs_maxCardValue_perturbed_le
      (c := fun i : Fin n => fun j : Fin n =>
        mKineticCost q (n : ℝ) kin ω (i : ℕ) (j : ℕ))
      (g := fun i : Fin n => fun j : Fin n => mProbe g ω (i : ℕ) (j : ℕ))
      (Bc := (n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ))) (G := G) (t := t)
      (fun i j => abs_mKineticCost_le (q := q) (r := (n : ℝ)) (C := C)
        (by positivity) hC0 hkin_bound ω (i : ℕ) (j : ℕ))
      (by positivity) (fun i j => hgb _ _) hG0
    simpa [Bnd, min_self] using h
  have hIntF : Integrable (markedFixedValue q (n : ℝ) t kin g n)
      (twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) :=
    Integrable.mono' (integrable_const ((n : ℝ) * Bnd))
      hmeas_fixed.aestronglyMeasurable (Filter.Eventually.of_forall hbound_fixed)
  -- The pointwise stability bound.
  have hstab : ∀ ω : TwoMarkedCloudSpace q A B,
      |markedTilted q (n : ℝ) kin g t ω - markedFixedValue q (n : ℝ) t kin g n ω| ≤
        2 * Bnd * (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|) := by
    intro ω
    have := abs_markedTilted_sub_fixedMatrix_le (q := q) (r := (n : ℝ)) (t := t)
      (C := C) (G := G) (by positivity) hC0 hG0 hkin_bound hgb ω n
    simpa [markedFixedValue, Bnd, mul_assoc] using this
  -- The integrals of the count deviations.
  have hcount : ∫ ω : TwoMarkedCloudSpace q A B,
      (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
        |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) ≤
      2 * Real.sqrt (n : ℝ) := by
    have h1 := integral_abs_mSourceCount_sub_le_kernel q Ks Kt (n : ℝ≥0)
    have h2 := integral_abs_mTargetCount_sub_le_kernel q Ks Kt (n : ℝ≥0)
    have h1' : ∫ ω : TwoMarkedCloudSpace q A B,
        |((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)|
        ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) ≤ Real.sqrt (n : ℝ) := by
      simpa only [NNReal.coe_natCast] using h1
    have h2' : ∫ ω : TwoMarkedCloudSpace q A B,
        |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|
        ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) ≤ Real.sqrt (n : ℝ) := by
      simpa only [NNReal.coe_natCast] using h2
    have hi1 : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        |((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)|)
        (twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) :=
      (((integrable_mSourceCount_kernel q Ks Kt (n : ℝ≥0)).sub
        (integrable_const (n : ℝ)))).abs
    have hi2 : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
        (twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) :=
      (((integrable_mTargetCount_kernel q Ks Kt (n : ℝ≥0)).sub
        (integrable_const (n : ℝ)))).abs
    rw [integral_add hi1 hi2]
    linarith [h1', h2']
  -- Integrability of the difference.
  have hdiff_int : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      markedTilted q (n : ℝ) kin g t ω - markedFixedValue q (n : ℝ) t kin g n ω)
      (twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) :=
    hIntT.sub hIntF
  -- Triangle inequality.
  have htri : |kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t -
        ∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))| ≤
      2 * Bnd * (2 * Real.sqrt (n : ℝ)) := by
    have hrepr : kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t =
        ∫ ω, markedTilted q (n : ℝ) kin g t ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) := rfl
    rw [hrepr]
    have habs : |∫ ω, markedTilted q (n : ℝ) kin g t ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) -
        ∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))| ≤
        ∫ ω, |markedTilted q (n : ℝ) kin g t ω -
          markedFixedValue q (n : ℝ) t kin g n ω|
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) := by
      rw [← integral_sub hIntT hIntF]
      exact abs_integral_le_integral_abs
    refine habs.trans ?_
    have hmono : ∫ ω, |markedTilted q (n : ℝ) kin g t ω -
          markedFixedValue q (n : ℝ) t kin g n ω|
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) ≤
        ∫ ω, 2 * Bnd * (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) := by
      apply integral_mono _ _ hstab
      · exact hdiff_int.abs
      · exact ((((integrable_mSourceCount_kernel q Ks Kt (n : ℝ≥0)).sub
            (integrable_const (n : ℝ))).abs).add
            (((integrable_mTargetCount_kernel q Ks Kt (n : ℝ≥0)).sub
              (integrable_const (n : ℝ))).abs)) |>.const_mul (2 * Bnd)
    refine hmono.trans ?_
    calc ∫ ω, 2 * Bnd * (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
          |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))
        = 2 * Bnd * ∫ ω, (|((mSourceCount ω : ℕ) : ℝ) - (n : ℝ)| +
            |((mTargetCount ω : ℕ) : ℝ) - (n : ℝ)|)
            ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0)) := by
          rw [integral_const_mul]
      _ ≤ 2 * Bnd * (2 * Real.sqrt (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hcount
          positivity
  -- Divide by `n`.
  have hdiv : |kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t / (n : ℝ) -
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))) / (n : ℝ)| =
      |kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t -
        ∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))| / (n : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hnR]
  rw [hdiv]
  refine (div_le_div_of_nonneg_right htri hnR.le).trans ?_
  rw [hBnd, show (2 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (2 * Real.sqrt (n : ℝ))) / (n : ℝ) =
      4 * ((n : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) from by
    rw [show Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _]
    have hnne : (n : ℝ) ≠ 0 := hnR.ne'
    rw [show (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / (n : ℝ) ^ (1 / 2 : ℝ) from by
      rw [Real.rpow_neg hnR.le]
      simp [one_div]]
    have hsq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      norm_num
    field_simp
    rw [hsq]
    ring]

/-! ## The de-Poissonized pressure limit -/

theorem tendsto_kernelMarkedFixedPressure_div
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => kernelMarkedScalePressure q A B Ks Kt kin g R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun n : ℕ =>
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))) / (n : ℝ))
      atTop (𝓝 (p t)) := by
  intro t
  have hq0 : 0 < q := by omega
  -- The Poissonized limit along the scale `n ^ (1/q)`.
  have hR : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (q : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (q : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hp' := (hp t).comp hR
  have heq : (fun n : ℕ =>
        kernelMarkedScalePressure q A B Ks Kt kin g ((n : ℝ) ^ (1 / (q : ℝ))) t) =ᶠ[atTop]
      (fun n : ℕ => kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hpow : ((n : ℝ) ^ (1 / (q : ℝ))) ^ q = (n : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      have hq1 : (1 / (q : ℝ)) * (q : ℝ) = 1 := by field_simp
      rw [hq1, Real.rpow_one]
    have htoNN : Real.toNNReal (((n : ℝ) ^ (1 / (q : ℝ))) ^ q) = (n : ℝ≥0) := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ (by positivity), hpow]
      simp
    rw [kernelMarkedScalePressure_of_pos q A B Ks Kt (by positivity), htoNN, hpow]
  have hP : Tendsto (fun n : ℕ =>
      kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t / (n : ℝ)) atTop (𝓝 (p t)) :=
    hp'.congr' heq
  -- The de-Poissonization difference vanishes.
  have hd : Tendsto (fun n : ℕ =>
      kernelMarkedPressure q A B Ks Kt (n : ℝ≥0) kin g t / (n : ℝ) -
        (∫ ω, markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt (n : ℝ≥0))) / (n : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_dePoissonError_zero hq C G t)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 < n := hn
    simpa only [Real.norm_eq_abs] using
      abs_kernelMarkedPressure_sub_fixed_div_le (q := q) (t := t) (C := C) (G := G)
        hC0 hG0 hkin hkin_bound hg hgb Ks Kt (n := n) hn0
  have hF := hP.sub hd
  simpa only [sub_sub_cancel, sub_zero] using hF


end OTSelector.Reconstruction
