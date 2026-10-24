import OTSelector.Reconstruction.FinslerOriginalBlockPointLaw
import OTSelector.Probability.MarkedBlockValueIntegral

/-!
# The ambient leaf-block expectation identity for kernel-marked clouds

This module closes the last gap of FinslerOriginalBlockPointLaw.lean: it turns
the per-block law identification
kernelMarkedCloudLaw_blockLocalCloudEncoded_law_unconditional into the
expectation-level ambient leaf-block identity for the kernel-marked two-cloud
law, and assembles the identity over the m ^ q leaf blocks.

What is proved here:

* blockDataLaw_markedPointLaw_eq_map_blockDataMk: the block-data law built from
  the marked point law of a position-dependent kernel is the block encoding of
  the kernel-marked cloud law at the same intensity;
* integral_blockTiltedValue_blockLocalCloudEncoded: the ambient leaf-block
  expectation identity at the reduced intensity R / m ^ q.  Encoding the two
  ambient clouds at one leaf block and evaluating the block-local tilted value
  at the reduced intensity is, in expectation, the kernel-marked pressure of
  the block-rescaled kernels at the reduced intensity;
* integral_blockSum_blockLocalCloudEncoded: the Fubini assembly over the leaf
  partition.  Summing the block expectations over the m ^ q leaf blocks gives
  the aggregate block pressure blockKernelPressureSum at the reduced intensity
  R / m ^ q; this is the law-level leaf-block identity that
  FinslerOriginalKernelModulusPressure names as the producer of the aggregate
  block pressure in place of the single pressure of the reference kernel.

The step which is not formalized here is recorded at the end of the file.
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

/-! ## The block-data form of the kernel-marked cloud law -/

/-- The block-data law of the marked point law of a position-dependent kernel
is the block encoding of the kernel-marked cloud law at the same intensity. -/
theorem blockDataLaw_markedPointLaw_eq_map_blockDataMk (q : ℕ)
    {K : Kernel (Fin q → ℝ) A} [IsMarkovKernel K] (c : ℝ≥0) :
    blockDataLaw (markedPointLaw q K) (fun n => poissonMeasure c {n}) =
      (kernelMarkedCloudLaw q A K c).map
        (fun z : MarkedCloudSpace q A =>
          (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData ((Fin q → ℝ) × A))) := by
  rw [blockDataLaw_eq_map_cloud]
  unfold kernelMarkedCloudLaw kernelMarkedSeqLaw markedPointLaw
  rfl

/-! ## The ambient leaf-block expectation identity -/

/-- **Ambient leaf-block expectation identity at the reduced intensity.**  For
one leaf block b, the expected block-local tilted value of the ambient
kernel-marked two-cloud law at intensity R, evaluated at the reduced intensity
R / m ^ q, is the kernel-marked pressure of the block-rescaled kernels at that
reduced intensity. -/
theorem integral_blockTiltedValue_blockLocalCloudEncoded
    (q m : ℕ) [NeZero m] (hm : 0 < m) (R : ℝ≥0)
    {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (b : Fin q → Fin m) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
          (blockLocalCloudEncoded (A := A) q m b ω.1)
          (blockLocalCloudEncoded (A := B) q m b ω.2)
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) =
      kernelMarkedPressure q A B (blockLocalKernel Ks b) (blockLocalKernel Kt b)
        (R / (m ^ q : ℝ≥0)) kin g t := by
  classical
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure (Ks (fun _ : Fin q => 0))
  haveI : Nonempty B := nonempty_of_isProbabilityMeasure (Kt (fun _ : Fin q => 0))
  let c : ℝ≥0 := R / (m ^ q : ℝ≥0)
  let rloc : ℝ := (c : ℝ)
  let PosA := (Fin q → ℝ) × A
  let PosB := (Fin q → ℝ) × B
  let encA : MarkedCloudSpace q A → BlockData PosA := blockLocalCloudEncoded (A := A) q m b
  let encB : MarkedCloudSpace q B → BlockData PosB := blockLocalCloudEncoded (A := B) q m b
  let mkA : MarkedCloudSpace q A → BlockData PosA :=
    fun z => (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData PosA)
  let mkB : MarkedCloudSpace q B → BlockData PosB :=
    fun z => (⟨z.1, fun j : Fin z.1 => z.2 j⟩ : BlockData PosB)
  have hc0 : 0 ≤ rloc := c.coe_nonneg
  have hEncMeas : Measurable fun ω : TwoMarkedCloudSpace q A B =>
      (encA ω.1, encB ω.2) :=
    ((measurable_blockLocalCloudEncoded (A := A) q m b).comp measurable_fst).prodMk
      ((measurable_blockLocalCloudEncoded (A := B) q m b).comp measurable_snd)
  have hmkA : Measurable mkA := measurable_blockDataMk q A
  have hmkB : Measurable mkB := measurable_blockDataMk q B
  have hpairMeas : Measurable fun z : MarkedCloudSpace q A × MarkedCloudSpace q B =>
      (mkA z.1, mkB z.2) :=
    (hmkA.comp measurable_fst).prodMk (hmkB.comp measurable_snd)
  have hΦ : Measurable fun d : BlockData PosA × BlockData PosB =>
      blockTiltedValue q rloc kin g t d.1 d.2 :=
    measurable_blockTiltedValue q rloc hc0 hC0 hG0 hkin hkin_bound hg hgb t
  -- The law of each encoded block cloud is the block-data law of the block-rescaled kernel.
  have hlawA : (kernelMarkedCloudLaw q A Ks R).map encA =
      blockDataLaw (markedPointLaw q (blockLocalKernel Ks b))
        (fun n => poissonMeasure c {n}) := by
    simpa only [encA, c] using
      (kernelMarkedCloudLaw_blockLocalCloudEncoded_law_unconditional
        (q := q) (m := m) (A := A) hm R Ks b)
  have hlawB : (kernelMarkedCloudLaw q B Kt R).map encB =
      blockDataLaw (markedPointLaw q (blockLocalKernel Kt b))
        (fun n => poissonMeasure c {n}) := by
    simpa only [encB, c] using
      (kernelMarkedCloudLaw_blockLocalCloudEncoded_law_unconditional
        (q := q) (m := m) (A := B) hm R Kt b)
  have hBD_A : blockDataLaw (markedPointLaw q (blockLocalKernel Ks b))
      (fun n => poissonMeasure c {n}) =
      (kernelMarkedCloudLaw q A (blockLocalKernel Ks b) c).map mkA := by
    simpa only [mkA] using
      (blockDataLaw_markedPointLaw_eq_map_blockDataMk (q := q) (A := A)
        (K := blockLocalKernel Ks b) c)
  have hBD_B : blockDataLaw (markedPointLaw q (blockLocalKernel Kt b))
      (fun n => poissonMeasure c {n}) =
      (kernelMarkedCloudLaw q B (blockLocalKernel Kt b) c).map mkB := by
    simpa only [mkB] using
      (blockDataLaw_markedPointLaw_eq_map_blockDataMk (q := q) (A := B)
        (K := blockLocalKernel Kt b) c)
  change ∫ ω, blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2)
      ∂((kernelMarkedCloudLaw q A Ks R).prod (kernelMarkedCloudLaw q B Kt R)) =
      kernelMarkedPressure q A B (blockLocalKernel Ks b) (blockLocalKernel Kt b)
        c kin g t
  calc
    ∫ ω, blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2)
        ∂((kernelMarkedCloudLaw q A Ks R).prod (kernelMarkedCloudLaw q B Kt R))
        = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((kernelMarkedCloudLaw q A Ks R).prod
              (kernelMarkedCloudLaw q B Kt R)).map
                (fun ω : TwoMarkedCloudSpace q A B => (encA ω.1, encB ω.2))) := by
          exact (integral_map hEncMeas.aemeasurable hΦ.aestronglyMeasurable).symm
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((kernelMarkedCloudLaw q A Ks R).map encA).prod
              ((kernelMarkedCloudLaw q B Kt R).map encB)) := by
          rw [Measure.map_prod_map (kernelMarkedCloudLaw q A Ks R)
            (kernelMarkedCloudLaw q B Kt R)
            (measurable_blockLocalCloudEncoded (A := A) q m b)
            (measurable_blockLocalCloudEncoded (A := B) q m b)]
          rfl
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂((blockDataLaw (markedPointLaw q (blockLocalKernel Ks b))
                (fun n => poissonMeasure c {n})).prod
              (blockDataLaw (markedPointLaw q (blockLocalKernel Kt b))
                (fun n => poissonMeasure c {n}))) := by
          rw [hlawA, hlawB]
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((kernelMarkedCloudLaw q A (blockLocalKernel Ks b) c).map mkA).prod
              ((kernelMarkedCloudLaw q B (blockLocalKernel Kt b) c).map mkB)) := by
          rw [hBD_A, hBD_B]
      _ = ∫ d : BlockData PosA × BlockData PosB,
            blockTiltedValue q rloc kin g t d.1 d.2
            ∂(((kernelMarkedCloudLaw q A (blockLocalKernel Ks b) c).prod
              (kernelMarkedCloudLaw q B (blockLocalKernel Kt b) c)).map
                (fun z : MarkedCloudSpace q A × MarkedCloudSpace q B =>
                  (mkA z.1, mkB z.2))) := by
          rw [Measure.map_prod_map (kernelMarkedCloudLaw q A (blockLocalKernel Ks b) c)
            (kernelMarkedCloudLaw q B (blockLocalKernel Kt b) c) hmkA hmkB]
          rfl
      _ = ∫ z : MarkedCloudSpace q A × MarkedCloudSpace q B,
            blockTiltedValue q rloc kin g t (mkA z.1) (mkB z.2)
            ∂((kernelMarkedCloudLaw q A (blockLocalKernel Ks b) c).prod
              (kernelMarkedCloudLaw q B (blockLocalKernel Kt b) c)) := by
          exact integral_map hpairMeas.aemeasurable hΦ.aestronglyMeasurable
      _ = ∫ z : MarkedCloudSpace q A × MarkedCloudSpace q B,
            markedTilted q rloc kin g t (z.1, z.2)
            ∂((kernelMarkedCloudLaw q A (blockLocalKernel Ks b) c).prod
              (kernelMarkedCloudLaw q B (blockLocalKernel Kt b) c)) := by
          apply integral_congr_ae
          filter_upwards with z
          exact blockTiltedValue_blockDataMk q rloc (kin := kin) (g := g) t z.1 z.2
      _ = kernelMarkedPressure q A B (blockLocalKernel Ks b) (blockLocalKernel Kt b)
            c kin g t := rfl

end OTSelector.Reconstruction