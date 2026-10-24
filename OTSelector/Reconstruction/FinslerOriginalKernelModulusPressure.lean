import OTSelector.Reconstruction.FinslerOriginalKernelMarkedPoisson

/-!
# Modulus of continuity versus block scale for the kernel-marked pressure

The block subadditivity of the kernel-marked pressure lane has two halves. The
independent-mark half is proved in the block-comparison modules; the constant
kernel case is the exact special case of the kernel-marked lane. For a
coordinate-dependent mark kernel the block decomposition is not
law-preserving: the points of one leaf block carry marks drawn from the kernel at
their original positions, so the block cloud marked point law is the point law
of the block-rescaled kernel, not that of the original kernel.

This module formalizes the two structural reductions on which a modulus-of-
continuity route must rest, and isolates the exact quantitative comparison that
remains:

* the kernel-marked cloud law, hence the kernel-marked pressure and the scale
  pressure, depend on the mark kernel only through the marked point law (the
  composition of the cube measure with the kernel);
* the block-rescaling action on mark kernels (the block corner map
  xloc |-> corner c + xloc / m) produces Markov kernels, and it fixes constant
  kernels exactly, so at constant kernels the aggregate block comparison of the
  local kernels is an identity with zero error (the sharp case);
* consequently any modulus of continuity of the kernel can only enter through
  the marked point laws of the block-rescaled kernels.

The remaining quantitative input is documented at the end of the file.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The marked point law of a mark kernel -/

/-- The marked point law of the mark kernel: the joint law of a cube position
and its mark. -/
noncomputable def markedPointLaw (q : ℕ) (K : Kernel (Fin q → ℝ) A) :
    Measure ((Fin q → ℝ) × A) :=
  OTSelector.Probability.cubeMeasure (Fin q) 1 ⊗ₘ K

/-- The kernel-marked sequence law only sees the marked point law. -/
theorem kernelMarkedSeqLaw_congr (q : ℕ)
    {K Knew : Kernel (Fin q → ℝ) A} [IsMarkovKernel K] [IsMarkovKernel Knew]
    (h : markedPointLaw q K = markedPointLaw q Knew) :
    kernelMarkedSeqLaw q A K = kernelMarkedSeqLaw q A Knew := by
  unfold kernelMarkedSeqLaw markedPointLaw at *
  rw [show (fun _ : ℕ => OTSelector.Probability.cubeMeasure (Fin q) 1 ⊗ₘ K) =
      (fun _ : ℕ => OTSelector.Probability.cubeMeasure (Fin q) 1 ⊗ₘ Knew) from
    funext fun _ => h]

/-- The kernel-marked cloud law only sees the marked point law. -/
theorem kernelMarkedCloudLaw_congr (q : ℕ)
    {K Knew : Kernel (Fin q → ℝ) A} [IsMarkovKernel K] [IsMarkovKernel Knew]
    (h : markedPointLaw q K = markedPointLaw q Knew) (r : ℝ≥0) :
    kernelMarkedCloudLaw q A K r = kernelMarkedCloudLaw q A Knew r := by
  unfold kernelMarkedCloudLaw
  rw [kernelMarkedSeqLaw_congr q h]

/-- The two-cloud kernel-marked law only sees the two marked point laws. -/
theorem twoKernelMarkedCloudLaw_congr (q : ℕ) (r : ℝ≥0)
    {Ks Ksnew : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks] [IsMarkovKernel Ksnew]
    {Kt Ktnew : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt] [IsMarkovKernel Ktnew]
    (hs : markedPointLaw q Ks = markedPointLaw q Ksnew)
    (ht : markedPointLaw q Kt = markedPointLaw q Ktnew) :
    twoKernelMarkedCloudLaw q A B Ks Kt r = twoKernelMarkedCloudLaw q A B Ksnew Ktnew r := by
  unfold twoKernelMarkedCloudLaw
  rw [kernelMarkedCloudLaw_congr q hs r, kernelMarkedCloudLaw_congr q ht r]

/-- **The kernel-marked pressure only sees the marked point laws.** -/
theorem kernelMarkedPressure_eq_of_markedPointLaw (q : ℕ)
    {Ks Ksnew : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks] [IsMarkovKernel Ksnew]
    {Kt Ktnew : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt] [IsMarkovKernel Ktnew]
    (hs : markedPointLaw q Ks = markedPointLaw q Ksnew)
    (ht : markedPointLaw q Kt = markedPointLaw q Ktnew)
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) :
    kernelMarkedPressure q A B Ks Kt r kin g t =
      kernelMarkedPressure q A B Ksnew Ktnew r kin g t := by
  unfold kernelMarkedPressure
  rw [twoKernelMarkedCloudLaw_congr q r hs ht]

/-- **The kernel-marked scale pressure only sees the marked point laws.** -/
theorem kernelMarkedScalePressure_eq_of_markedPointLaw (q : ℕ)
    {Ks Ksnew : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks] [IsMarkovKernel Ksnew]
    {Kt Ktnew : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt] [IsMarkovKernel Ktnew]
    (hs : markedPointLaw q Ks = markedPointLaw q Ksnew)
    (ht : markedPointLaw q Kt = markedPointLaw q Ktnew)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (R t : ℝ) :
    kernelMarkedScalePressure q A B Ks Kt kin g R t =
      kernelMarkedScalePressure q A B Ksnew Ktnew kin g R t := by
  unfold kernelMarkedScalePressure
  rw [kernelMarkedPressure_eq_of_markedPointLaw q hs ht]

/-! ## The block-rescaling action on mark kernels -/

/-- The corner of the block with label c, as a point of the cube. -/
noncomputable def blockCorner {q m : ℕ} (c : Fin q → Fin m) : Fin q → ℝ :=
  fun l => (c l).val / m

/-- The block-rescaling map of the block with label c: the local coordinate
xloc of a point of the block corresponds to the cube position
corner c + xloc / m. -/
noncomputable def blockRescaleMap {q m : ℕ} (c : Fin q → Fin m) :
    (Fin q → ℝ) → (Fin q → ℝ) :=
  fun x => fun l => blockCorner c l + x l / m

/-- The block-rescaling map is continuous, hence measurable. -/
theorem measurable_blockRescaleMap {q m : ℕ} (c : Fin q → Fin m) :
    Measurable (blockRescaleMap c) := by
  unfold blockRescaleMap blockCorner
  fun_prop

/-- **The block-rescaled kernel**: the mark kernel of the leaf-block cloud with
label c, expressed in local cube coordinates. -/
noncomputable def blockLocalKernel {q m : ℕ} (K : Kernel (Fin q → ℝ) A)
    (c : Fin q → Fin m) : Kernel (Fin q → ℝ) A where
  toFun x := K (blockRescaleMap c x)
  measurable' := K.measurable.comp (measurable_blockRescaleMap c)

/-- The block-rescaled kernel evaluated at a local position. -/
theorem blockLocalKernel_apply {q m : ℕ} (K : Kernel (Fin q → ℝ) A)
    (c : Fin q → Fin m) (x : Fin q → ℝ) :
    blockLocalKernel K c x = K (blockRescaleMap c x) := rfl

/-- The block-rescaled kernel of a Markov kernel is Markov. -/
instance instIsMarkovKernelBlockLocalKernel {q m : ℕ} (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] (c : Fin q → Fin m) :
    IsMarkovKernel (blockLocalKernel K c) where
  isProbabilityMeasure x :=
    (inferInstance : IsMarkovKernel K).isProbabilityMeasure (blockRescaleMap c x)

/-- A constant kernel is fixed by the block rescaling. -/
theorem blockLocalKernel_const {q m : ℕ} (α : Measure A) (c : Fin q → Fin m) :
    blockLocalKernel (Kernel.const (Fin q → ℝ) α) c = Kernel.const (Fin q → ℝ) α := by
  ext x
  rw [blockLocalKernel_apply, Kernel.const_apply, Kernel.const_apply]

/-! ## The aggregate block pressure of the block-rescaled kernels -/

/-- The aggregate pressure of the block-rescaled kernels at one block scale.
This sum is what a law-level leaf-block expectation identity produces in place
of the single pressure of the reference kernel when the mark kernel depends on
the position. -/
noncomputable def blockKernelPressureSum (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) : ℝ :=
  ∑ c : Fin q → Fin m,
    kernelMarkedPressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c) r kin g t

/-- **Sharp case: the aggregate block pressure at constant kernels.**  At a
constant mark kernel every block-rescaled kernel is the reference kernel, so the
aggregate block pressure is exactly the reference pressure scaled by the number
of blocks, with zero modulus error. -/
theorem blockKernelPressureSum_const (q m : ℕ)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) :
    blockKernelPressureSum q m (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) r kin g t =
      ((m ^ q : ℕ) : ℝ) * markedPressure q A B α β r kin g t := by
  have hterm : ∀ c : Fin q → Fin m,
      kernelMarkedPressure q A B (blockLocalKernel (Kernel.const (Fin q → ℝ) α) c)
          (blockLocalKernel (Kernel.const (Fin q → ℝ) β) c) r kin g t =
        markedPressure q A B α β r kin g t := by
    intro c
    have hsp : markedPointLaw q (blockLocalKernel (Kernel.const (Fin q → ℝ) α) c) =
        markedPointLaw q (Kernel.const (Fin q → ℝ) α) := by
      unfold markedPointLaw
      exact congrArg (fun K : Kernel (Fin q → ℝ) A =>
        (OTSelector.Probability.cubeMeasure (Fin q) 1) ⊗ₘ K) (blockLocalKernel_const α c)
    have htp : markedPointLaw q (blockLocalKernel (Kernel.const (Fin q → ℝ) β) c) =
        markedPointLaw q (Kernel.const (Fin q → ℝ) β) := by
      unfold markedPointLaw
      exact congrArg (fun K : Kernel (Fin q → ℝ) B =>
        (OTSelector.Probability.cubeMeasure (Fin q) 1) ⊗ₘ K) (blockLocalKernel_const β c)
    exact (kernelMarkedPressure_eq_of_markedPointLaw q hsp htp r kin g t).trans
      (kernelMarkedPressure_const q A B α β r kin g t)
  unfold blockKernelPressureSum
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const,
    Finset.card_univ, Fintype.card_fun]
  simp only [Fintype.card_fin, nsmul_eq_mul]

/-- The aggregate block comparison at one block scale: the quantitative
inequality that a modulus of continuity of the mark kernel is meant to supply. -/
noncomputable def BlockKernelComparison (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (err : ℝ) : Prop :=
  ∀ (r : ℝ≥0) (t : ℝ),
    blockKernelPressureSum q m Ks Kt r kin g t ≤
      ((m ^ q : ℕ) : ℝ) * kernelMarkedPressure q A B Ks Kt r kin g t + err

/-- **The sharp case of the aggregate block comparison.**  Constant kernels
satisfy the aggregate block comparison with zero error, which is the exact
constant-kernel reduction of the kernel-marked block subadditivity. -/
theorem blockKernelComparison_const (q m : ℕ)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) :
    BlockKernelComparison q m (Kernel.const (Fin q → ℝ) α)
      (Kernel.const (Fin q → ℝ) β) kin g 0 := by
  intro r t
  rw [blockKernelPressureSum_const, kernelMarkedPressure_const]
  simp

/-- The aggregate block pressure is invariant under changes of the mark kernels
that preserve the marked point laws of all block-rescaled kernels. -/
theorem blockKernelPressureSum_eq_of_blockMarkedPointLaw (q m : ℕ)
    {Ks Ksnew : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks] [IsMarkovKernel Ksnew]
    {Kt Ktnew : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt] [IsMarkovKernel Ktnew]
    (hs : ∀ c : Fin q → Fin m,
      markedPointLaw q (blockLocalKernel Ks c) = markedPointLaw q (blockLocalKernel Ksnew c))
    (ht : ∀ c : Fin q → Fin m,
      markedPointLaw q (blockLocalKernel Kt c) = markedPointLaw q (blockLocalKernel Ktnew c))
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) :
    blockKernelPressureSum q m Ks Kt r kin g t =
      blockKernelPressureSum q m Ksnew Ktnew r kin g t := by
  unfold blockKernelPressureSum
  exact Finset.sum_congr rfl fun c _ =>
    kernelMarkedPressure_eq_of_markedPointLaw q (hs c) (ht c) r kin g t

/-! ## The remaining quantitative input

The structural reductions above show that the kernel-marked block comparison is
governed entirely by the marked point laws of the block-rescaled kernels,
namely the composition of the cube measure with blockLocalKernel K c, and that
at constant kernels the aggregate block comparison is an identity with zero
error.  Two quantitative inputs are still missing, and they are the exact
content of the modulus-of-continuity route.

1. The law-level leaf-block decomposition.  The independent-mark lane proves the
   identity: the expected sum over blocks of the optimal block value equals
   (m ^ q) times the marked pressure at intensity R / m ^ q.  It uses that the
   rescaled points of one leaf block are, in law, a reduced-intensity marked
   cloud.  For a coordinate-dependent kernel the block cloud carries the
   block-rescaled kernel blockLocalKernel K c, so the identity can only hold
   with the aggregate blockKernelPressureSum on the right, and its proof needs
   the same measure-theoretic block decomposition applied to the kernel-marked
   cloud law.

2. Pressure stability under the marked point law.  Turning a modulus of
   continuity of K into an error bound for BlockKernelComparison requires a
   perturbation estimate of the marked pressure with respect to the marked point
   law: if two clouds are coupled pointwise with marks agreeing except on an
   event of probability delta, then the matching values differ by at most the
   edge-cost discrepancy over the differing matched pairs.  Since the edge costs
   are only controlled by C times the squared displacement, this estimate has to
   be paired with an integrability estimate for the kinetic cost along the
   optimal matching.

   The relevant scale is not the block scale 1 / m: in the block cloud a matched
   pair sits at local distance r ^ (-1 / q) and hence at original displacement
   r ^ (-1 / q) / m = R ^ (-1 / q), the same pairing scale as in the reference
   cloud at intensity R.  The modulus that a block comparison can absorb is
   therefore the kernel modulus at the pairing scale R ^ (-1 / q), multiplied by
   the number of blocks; the block scale itself only controls the intra-block
   variation of the mark law.

A modulus of continuity of the kernel alone therefore does not close the
aggregate block comparison: it must be combined with the two inputs above.  The
constant-kernel case is the sharp special case where both inputs degenerate (the
block-rescaled kernels coincide with the reference kernel and no pressure
stability estimate is needed), and it is the case proved exactly in this lane.
-/

end OTSelector.Reconstruction
