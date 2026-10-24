import OTSelector.Reconstruction.FinslerOriginalKernelCouplingConstruction
import OTSelector.Reconstruction.FinslerOriginalKernelModulusPressure

/-!
# Leaf-block extraction and the blockwise kernel comparison

This module connects the kernel pressure stability theory of
FinslerOriginalKernelPressureStability and FinslerOriginalKernelCouplingConstruction
to the aggregate block comparison of FinslerOriginalKernelModulusPressure.

What is proved here:

* abs_kernelMarkedPressure_sub_le_of_blockPointLawCoupling: for one leaf block c,
  given a position-preserving coupling of the marked point law of the
  block-rescaled kernel blockLocalKernel Ks c with the reference marked point law
  of Ks (and likewise for the target side), the pressure of the block-rescaled
  pair differs from the reference pressure by at most the integral over the
  constructed coupling of the minimum count times the uniform edge-error
  constant markedEdgeErrorBound;

* blockKernelComparison_of_blockPointLawCouplings: assembling the per-block
  bounds with the same constant err yields the aggregate
  BlockKernelComparison q m Ks Kt kin g (m ^ q * err), via
  blockKernelComparison_of_blockwise_stability;

* pointLawCoupling: the position-preserving coupling of two marked point laws,
  constructed explicitly as the cube measure composed with the product of the
  two kernels, with pointLawCoupling_fst and pointLawCoupling_snd identifying
  its two marginals with the two marked point laws (this supplies the coupling
  input of the stability theorems);

* blockKernelComparison_of_pointLawEdgeBound: the unconditional form of the
  aggregate block comparison, with the per-block couplings instantiated by
  pointLawCoupling, leaving only per-block integrability and the per-block
  edge-error integral bound as hypotheses;

What remains, and why:

* The leaf-block law identification proper (the pushforward of the
  kernel-marked cloud law under the block extraction is the product of the
  block-rescaled kernel-marked cloud laws at intensity R / m ^ q) is not proved
  here.  The existing thinning theorem map_poisson_blockData (MarkedSplitting)
  does not apply to kernel marks: it assumes a single one-point law nu on the
  product of label and point space together with independence of the label and
  the point, whereas for kernel marks the mark law of a point depends on its
  label (the mark is sampled from K at the ambient position, which is determined
  by the label and the local position).  Closing it needs the label-dependent
  variant of map_poisson_blockData, with a kernel nu b in place of nu and
  without the independence hypothesis; the point-process combinatorics of the
  existing proof (Poisson colouring, multinomial fibre counts, iid blocks) are
  unchanged, but the one-point law step has to be redone in the kernel form.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open OTSelector OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## Per-block pressure stability -/

/-- **Per-block kernel pressure stability.**  For the leaf block c, a
position-preserving coupling of the block-rescaled marked point laws with the
reference marked point laws bounds the pressure difference of the
block-rescaled kernels by the edge-error integral over the coupling. -/
theorem abs_kernelMarkedPressure_sub_le_of_blockPointLawCoupling
    (q m : ℕ) (c : Fin q → Fin m) (R : ℝ≥0) {t C G : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    (γs : Measure ((Fin q → ℝ) × (A × A))) [IsProbabilityMeasure γs]
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γt]
    (hγs1 : γs.map (coupledMarkFst (q := q) (A := A)) =
      markedPointLaw q (blockLocalKernel Ks c))
    (hγs2 : γs.map (coupledMarkSnd (q := q) (A := A)) = markedPointLaw q Ks)
    (hγt1 : γt.map (coupledMarkFst (q := q) (A := B)) =
      markedPointLaw q (blockLocalKernel Kt c))
    (hγt2 : γt.map (coupledMarkSnd (q := q) (A := B)) = markedPointLaw q Kt)
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hI1 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := (R : ℝ)) kin g t z.1)
      (coupledCloudPairLaw (A := A) (B := B) q R γs γt))
    (hI2 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := (R : ℝ)) kin g t z.2)
      (coupledCloudPairLaw (A := A) (B := B) q R γs γt))
    (hIB : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
        markedEdgeErrorBound q (R : ℝ) t C G)
      (coupledCloudPairLaw (A := A) (B := B) q R γs γt)) :
    |kernelMarkedPressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
        R kin g t - kernelMarkedPressure q A B Ks Kt R kin g t| ≤
      ∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
        markedEdgeErrorBound q (R : ℝ) t C G
        ∂(coupledCloudPairLaw (A := A) (B := B) q R γs γt) :=
  abs_kernelMarkedPressure_sub_le_of_pointLawCoupling (q := q) (R := R) (t := t)
    (kin := kin) (g := g) (Ks := blockLocalKernel Ks c) (Ks' := Ks)
    (Kt := blockLocalKernel Kt c) (Kt' := Kt) γs γt hγs1 hγs2 hγt1 hγt2
    hkin hkin_bound hg hgb hC hG hI1 hI2 hIB

/-! ## The aggregate block comparison -/

/-- **Aggregate block comparison from per-block point-law couplings.**  Suppose
every leaf block c comes with position-preserving couplings of the marked point
laws of blockLocalKernel Ks c and blockLocalKernel Kt c to the reference marked
point laws of Ks and Kt, with the edge-error integral bounded by a common err.
Then the aggregate block comparison holds with error m ^ q * err. -/
theorem blockKernelComparison_of_blockPointLawCouplings
    (q m : ℕ) {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    (γs : ∀ _c : Fin q → Fin m, Measure ((Fin q → ℝ) × (A × A)))
    (γt : ∀ _c : Fin q → Fin m, Measure ((Fin q → ℝ) × (B × B)))
    (hγsprob : ∀ c, IsProbabilityMeasure (γs c))
    (hγtprob : ∀ c, IsProbabilityMeasure (γt c))
    (hγs1 : ∀ c, (γs c).map (coupledMarkFst (q := q) (A := A)) =
      markedPointLaw q (blockLocalKernel Ks c))
    (hγs2 : ∀ c, (γs c).map (coupledMarkSnd (q := q) (A := A)) = markedPointLaw q Ks)
    (hγt1 : ∀ c, (γt c).map (coupledMarkFst (q := q) (A := B)) =
      markedPointLaw q (blockLocalKernel Kt c))
    (hγt2 : ∀ c, (γt c).map (coupledMarkSnd (q := q) (A := B)) = markedPointLaw q Kt)
    {C G : ℝ} (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hI1 : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
        markedTilted (q := q) (r := (R : ℝ)) kin g t z.1)
        (coupledCloudPairLaw (A := A) (B := B) q R (γs c) (γt c)))
    (hI2 : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
        markedTilted (q := q) (r := (R : ℝ)) kin g t z.2)
        (coupledCloudPairLaw (A := A) (B := B) q R (γs c) (γt c)))
    (hIB : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
        ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
          markedEdgeErrorBound q (R : ℝ) t C G)
        (coupledCloudPairLaw (A := A) (B := B) q R (γs c) (γt c)))
    {err : ℝ}
    (hbound : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      ∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
          markedEdgeErrorBound q (R : ℝ) t C G
          ∂(coupledCloudPairLaw (A := A) (B := B) q R (γs c) (γt c)) ≤ err) :
    BlockKernelComparison q m Ks Kt kin g (((m ^ q : ℕ) : ℝ) * err) := by
  refine blockKernelComparison_of_blockwise_stability (q := q) (m := m) (t := 0)
    (kin := kin) (g := g) (err := err) ?_
  intro c R t
  haveI := hγsprob c
  haveI := hγtprob c
  exact le_trans
    (abs_kernelMarkedPressure_sub_le_of_blockPointLawCoupling (q := q) (m := m) c R
      (t := t) (kin := kin) (g := g) (Ks := Ks) (Kt := Kt)
      (γs c) (γt c) (hγs1 c) (hγs2 c) (hγt1 c) (hγt2 c)
      hkin hkin_bound hg hgb hC hG (hI1 c R t) (hI2 c R t) (hIB c R t))
    (hbound c R t)

/-! ## Position-preserving couplings of the marked point laws -/

/-- The position-preserving coupling of two marked point laws: the cube position
is shared and the two marks are sampled independently from the two kernels. -/
noncomputable def pointLawCoupling (q : ℕ) (K₁ : Kernel (Fin q → ℝ) A)
    (K₂ : Kernel (Fin q → ℝ) B) [IsMarkovKernel K₁] [IsMarkovKernel K₂] :
    Measure ((Fin q → ℝ) × (A × B)) :=
  (cubeMeasure (Fin q) 1) ⊗ₘ (K₁.prod K₂)

/-- The position-preserving coupling is a probability measure. -/
instance instIsProbabilityMeasurePointLawCoupling (q : ℕ) (K₁ : Kernel (Fin q → ℝ) A)
    (K₂ : Kernel (Fin q → ℝ) B) [IsMarkovKernel K₁] [IsMarkovKernel K₂] :
    IsProbabilityMeasure (pointLawCoupling (A := A) (B := B) q K₁ K₂) := by
  haveI hc : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  unfold pointLawCoupling
  infer_instance

/-- The first marginal of the position-preserving coupling is the first marked
point law. -/
theorem pointLawCoupling_fst (q : ℕ) (K₁ : Kernel (Fin q → ℝ) A)
    (K₂ : Kernel (Fin q → ℝ) B) [IsMarkovKernel K₁] [IsMarkovKernel K₂] :
    (pointLawCoupling (A := A) (B := B) q K₁ K₂).map
        (fun p : (Fin q → ℝ) × (A × B) => (p.1, p.2.1)) = markedPointLaw q K₁ := by
  have hm : (K₁.prod K₂).map Prod.fst = K₁ := by
    ext x
    rw [Kernel.map_apply _ measurable_fst, Kernel.prod_apply]
    simp
  unfold pointLawCoupling markedPointLaw
  rw [show (fun p : (Fin q → ℝ) × (A × B) => (p.1, p.2.1)) =
    Prod.map id Prod.fst from rfl]
  rw [← Measure.compProd_map (μ := cubeMeasure (Fin q) 1) (κ := K₁.prod K₂)
    (f := Prod.fst) measurable_fst, hm]

/-- The second marginal of the position-preserving coupling is the second marked
point law. -/
theorem pointLawCoupling_snd (q : ℕ) (K₁ : Kernel (Fin q → ℝ) A)
    (K₂ : Kernel (Fin q → ℝ) B) [IsMarkovKernel K₁] [IsMarkovKernel K₂] :
    (pointLawCoupling (A := A) (B := B) q K₁ K₂).map
        (fun p : (Fin q → ℝ) × (A × B) => (p.1, p.2.2)) = markedPointLaw q K₂ := by
  have hm : (K₁.prod K₂).map Prod.snd = K₂ := by
    ext x
    rw [Kernel.map_apply _ measurable_snd, Kernel.prod_apply]
    simp
  unfold pointLawCoupling markedPointLaw
  rw [show (fun p : (Fin q → ℝ) × (A × B) => (p.1, p.2.2)) =
    Prod.map id Prod.snd from rfl]
  rw [← Measure.compProd_map (μ := cubeMeasure (Fin q) 1) (κ := K₁.prod K₂)
    (f := Prod.snd) measurable_snd, hm]

/-- **Unconditional block comparison from the per-block edge-error bound.**  The
position-preserving couplings of the block-rescaled marked point laws with the
reference marked point laws are supplied explicitly by pointLawCoupling, so the
only remaining inputs are the per-block integrability and the per-block bound on
the edge-error integral. -/
theorem blockKernelComparison_of_pointLawEdgeBound
    (q m : ℕ) {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    {C G : ℝ} (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hI1 : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
        markedTilted (q := q) (r := (R : ℝ)) kin g t z.1)
        (coupledCloudPairLaw (A := A) (B := B) q R
          (pointLawCoupling (A := A) (B := A) q (blockLocalKernel Ks c) Ks)
          (pointLawCoupling (A := B) (B := B) q (blockLocalKernel Kt c) Kt)))
    (hI2 : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
        markedTilted (q := q) (r := (R : ℝ)) kin g t z.2)
        (coupledCloudPairLaw (A := A) (B := B) q R
          (pointLawCoupling (A := A) (B := A) q (blockLocalKernel Ks c) Ks)
          (pointLawCoupling (A := B) (B := B) q (blockLocalKernel Kt c) Kt)))
    (hIB : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
        ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
          markedEdgeErrorBound q (R : ℝ) t C G)
        (coupledCloudPairLaw (A := A) (B := B) q R
          (pointLawCoupling (A := A) (B := A) q (blockLocalKernel Ks c) Ks)
          (pointLawCoupling (A := B) (B := B) q (blockLocalKernel Kt c) Kt)))
    {err : ℝ}
    (hbound : ∀ (c : Fin q → Fin m) (R : ℝ≥0) (t : ℝ),
      ∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
          markedEdgeErrorBound q (R : ℝ) t C G
          ∂(coupledCloudPairLaw (A := A) (B := B) q R
            (pointLawCoupling (A := A) (B := A) q (blockLocalKernel Ks c) Ks)
            (pointLawCoupling (A := B) (B := B) q (blockLocalKernel Kt c) Kt)) ≤ err) :
    BlockKernelComparison q m Ks Kt kin g (((m ^ q : ℕ) : ℝ) * err) := by
  refine blockKernelComparison_of_blockPointLawCouplings (q := q) (m := m)
    (kin := kin) (g := g) (Ks := Ks) (Kt := Kt) (err := err)
    (γs := fun c => pointLawCoupling (A := A) (B := A) q (blockLocalKernel Ks c) Ks)
    (γt := fun c => pointLawCoupling (A := B) (B := B) q (blockLocalKernel Kt c) Kt)
    (fun c => instIsProbabilityMeasurePointLawCoupling (A := A) (B := A) q
      (blockLocalKernel Ks c) Ks)
    (fun c => instIsProbabilityMeasurePointLawCoupling (A := B) (B := B) q
      (blockLocalKernel Kt c) Kt)
    ?_ ?_ ?_ ?_ hkin hkin_bound hg hgb hC hG hI1 hI2 hIB hbound
  · intro c
    exact pointLawCoupling_fst (A := A) (B := A) q (blockLocalKernel Ks c) Ks
  · intro c
    exact pointLawCoupling_snd (A := A) (B := A) q (blockLocalKernel Ks c) Ks
  · intro c
    exact pointLawCoupling_fst (A := B) (B := B) q (blockLocalKernel Kt c) Kt
  · intro c
    exact pointLawCoupling_snd (A := B) (B := B) q (blockLocalKernel Kt c) Kt

end OTSelector.Reconstruction
