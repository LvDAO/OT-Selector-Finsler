import OTSelector.Probability.MarkedMixtureThinning
import OTSelector.Probability.MarkedBlockLaw
import OTSelector.Reconstruction.FinslerOriginalKernelMarkedPoisson
import OTSelector.Reconstruction.FinslerOriginalKernelModulusPressure

/-!
# Label-dependent thinning for the leaf-block law of a kernel-marked cloud

The thinning engine map_poisson_blockDataOfPairsGen (MarkedMixtureThinning) is
the label-dependent form of map_poisson_blockData: the common one-point law of
the marks is replaced by a label-indexed family nu of probability measures, and
the independence of label and mark is dropped.  This module instantiates that
engine for the kernel-marked Poisson cloud kernelMarkedCloudLaw.

Proved here:

* instIsProbabilityMeasureMarkedPointLaw': the marked point law of a Markov
  kernel is a probability measure;
* blockOnePoint: the one-point block map of a marked point (encoded block label
  and local marked point);
* kernelMarkedCloudLaw_blockLocalCloudEncoded_law: **the leaf-block law
  identification**, conditional on the single-particle block law
  (markedPointLaw q K).map (blockOnePoint) = mixturePointLaw uniform
  (fun c => markedPointLaw q (blockLocalKernel K (decode c))): the pushforward of
  the kernel-marked cloud law under the block extraction is the block data law
  of the block-rescaled kernel at intensity R / m ^ q.

The only producer input left open is the single-particle block law above, which
is documented at the end of the file; everything else (the iid structure of the
kernel-marked sequence, the Poisson count independence, the label-dependent
thinning and the identification of the extracted block cloud with
blockLocalCloudEncoded) is proved here.
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

variable {A : Type*} [MeasurableSpace A]

/-- The marked point law of a Markov kernel is a probability measure. -/
instance instIsProbabilityMeasureMarkedPointLaw' (q : ℕ) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] : IsProbabilityMeasure (markedPointLaw q K) := by
  haveI hc : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  unfold markedPointLaw
  infer_instance

/-- The one-point block map: the encoded block label of the position together
with the local marked point. -/
def blockOnePoint (q m : ℕ) [NeZero m] (p : (Fin q → ℝ) × A) :
    Fin (m ^ q) × ((Fin q → ℝ) × A) :=
  (blockLabelCode q m p.1, blockLocalMark (A := A) q m p)

theorem measurable_blockOnePoint (q m : ℕ) [NeZero m] :
    Measurable (blockOnePoint (A := A) q m) :=
  measurable_markedBlockOnePointScaled q m

/-- **The leaf-block law identification for kernel marks.**  Assume the
single-particle block law: the one-point block map of the marked point law is
the label-dependent mixture of the block-rescaled marked point laws.  Then the
pushforward of the kernel-marked cloud law under the block extraction of b is
the block data law of the block-rescaled kernel at intensity R / m ^ q. -/
theorem kernelMarkedCloudLaw_blockLocalCloudEncoded_law
    (q m : ℕ) [NeZero m] (hm : 0 < m) (R : ℝ≥0) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K]
    (hpoint : (markedPointLaw q K).map (blockOnePoint (A := A) q m) =
      mixturePointLaw (fun _ : Fin (m ^ q) => (((m ^ q : ℕ) : ℝ≥0))⁻¹)
        (fun c : Fin (m ^ q) =>
          markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))))
    (b : Fin q → Fin m) :
    (kernelMarkedCloudLaw q A K R).map (blockLocalCloudEncoded (A := A) q m b) =
      blockDataLaw (markedPointLaw q (blockLocalKernel K b))
        (fun n => poissonMeasure (R / (m ^ q : ℝ≥0)) {n}) := by
  classical
  have hp : ∑ _d : Fin (m ^ q), (((m ^ q : ℕ) : ℝ≥0))⁻¹ = 1 := by
    have hmq : ((m ^ q : ℕ) : ℝ≥0) ≠ 0 := by
      exact_mod_cast pow_ne_zero q (NeZero.ne m)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hmq
  have hN : (kernelMarkedCloudLaw q A K R).map (fun z : MarkedCloudSpace q A => z.1) =
      poissonMeasure R := by
    unfold kernelMarkedCloudLaw kernelMarkedSeqLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hpairMap : Measurable (blockOnePoint (A := A) q m) := measurable_blockOnePoint q m
  have hpair : ∀ n, iIndepFun (fun i : Fin n => fun ξ : MarkedCloudSpace q A =>
      (markedLabelCode q m ξ i, blockLocalMark (A := A) q m (ξ.2 i)))
      (kernelMarkedCloudLaw q A K R) := by
    intro n
    have hpointSeq : iIndepFun (fun (i : ℕ) (s : ℕ → (Fin q → ℝ) × A) =>
        blockOnePoint (A := A) q m (s i))
        (Measure.infinitePi (fun _ : ℕ => markedPointLaw q K)) :=
      iIndepFun_infinitePi_apply_comp (markedPointLaw q K)
        (blockOnePoint (A := A) q m) hpairMap
    unfold kernelMarkedCloudLaw kernelMarkedSeqLaw
    exact (iIndepFun_snd_prod
      (ν₁ := poissonMeasure R)
      (ν₂ := Measure.infinitePi (fun _ : ℕ => markedPointLaw q K))
      (Y := fun i s => blockOnePoint (A := A) q m (s i))
      (fun i => hpairMap.comp (measurable_pi_apply i)) hpointSeq).precomp
      (g := fun i : Fin n => (i : ℕ)) (fun i j hij => Fin.ext hij)
  have hjointlaw : ∀ i, (kernelMarkedCloudLaw q A K R).map
      (fun ξ : MarkedCloudSpace q A =>
        (markedLabelCode q m ξ i, blockLocalMark (A := A) q m (ξ.2 i))) =
      mixturePointLaw (fun _ : Fin (m ^ q) => (((m ^ q : ℕ) : ℝ≥0))⁻¹)
        (fun c : Fin (m ^ q) =>
          markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))) := by
    intro i
    have hlaw_i : (Measure.infinitePi (fun _ : ℕ => markedPointLaw q K)).map
        (fun s : ℕ → (Fin q → ℝ) × A => s i) = markedPointLaw q K := by
      simpa only using
        (Measure.infinitePi_map_eval (μ := fun _ : ℕ => markedPointLaw q K) i)
    have hcomp : (fun ξ : MarkedCloudSpace q A =>
          (markedLabelCode q m ξ i, blockLocalMark (A := A) q m (ξ.2 i))) =
        (fun s : ℕ → (Fin q → ℝ) × A => blockOnePoint (A := A) q m (s i)) ∘ Prod.snd :=
      rfl
    have hgMeas : Measurable (fun s : ℕ → (Fin q → ℝ) × A => blockOnePoint (A := A) q m (s i)) :=
      hpairMap.comp (measurable_pi_apply i)
    unfold kernelMarkedCloudLaw kernelMarkedSeqLaw
    rw [show Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) 1 ⊗ₘ K) =
      Measure.infinitePi (fun _ : ℕ => markedPointLaw q K) from rfl]
    rw [hcomp, ← Measure.map_map (g := fun s : ℕ → (Fin q → ℝ) × A =>
      blockOnePoint (A := A) q m (s i)) (f := Prod.snd) hgMeas measurable_snd]
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    have hstep : (Measure.infinitePi (fun _ : ℕ => markedPointLaw q K)).map
        (fun s : ℕ → (Fin q → ℝ) × A => blockOnePoint (A := A) q m (s i)) =
        (Measure.infinitePi (fun _ : ℕ => markedPointLaw q K)).map
          ((blockOnePoint (A := A) q m) ∘
            (fun s : ℕ → (Fin q → ℝ) × A => s i)) := rfl
    rw [hstep, ← Measure.map_map hpairMap (measurable_pi_apply i), hlaw_i]
    exact hpoint
  have hwmeas : ∀ i, Measurable (fun ξ : MarkedCloudSpace q A => markedLabelCode q m ξ i) :=
    fun i => measurable_markedLabelCode q m i
  have hxmeas : ∀ i, Measurable (fun ξ : MarkedCloudSpace q A =>
      blockLocalMark (A := A) q m (ξ.2 i)) :=
    fun i => (measurable_blockLocalMark q m).comp ((measurable_pi_apply i).comp measurable_snd)
  have hindep : ∀ n, IndepFun (fun ξ : MarkedCloudSpace q A => ξ.1)
      (fun ξ => fun i : Fin n =>
        (markedLabelCode q m ξ i, blockLocalMark (A := A) q m (ξ.2 i)))
      (kernelMarkedCloudLaw q A K R) := by
    intro n
    unfold kernelMarkedCloudLaw kernelMarkedSeqLaw
    exact indepFun_prod (X := (id : ℕ → ℕ))
      (Y := fun s : ℕ → (Fin q → ℝ) × A => fun i : Fin n =>
        blockOnePoint (A := A) q m (s i)) measurable_id
      (measurable_pi_lambda _ fun i => hpairMap.comp (measurable_pi_apply (i : ℕ)))
  haveI hνprob : ∀ c : Fin (m ^ q), IsProbabilityMeasure
      (markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))) :=
    fun c => instIsProbabilityMeasureMarkedPointLaw' q _
  have hengine := map_poisson_blockDataOfPairsGen
    (P := kernelMarkedCloudLaw q A K R) (Ω := MarkedCloudSpace q A)
    (Pos := (Fin q → ℝ) × A) (γ := Fin (m ^ q))
    R (fun ξ : MarkedCloudSpace q A => ξ.1)
    (fun i ξ => markedLabelCode q m ξ i)
    (fun i ξ => blockLocalMark (A := A) q m (ξ.2 i))
    (fun _ : Fin (m ^ q) => (((m ^ q : ℕ) : ℝ≥0))⁻¹) hp
    (fun c : Fin (m ^ q) =>
      markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c)))
    hN hpair hwmeas hxmeas hjointlaw hindep (finFunctionFinEquiv b)
  have hleft : prefixBlockDataGen (Pos := (Fin q → ℝ) × A) (γ := Fin (m ^ q))
        (fun ξ : MarkedCloudSpace q A => ξ.1)
        (fun i ξ => markedLabelCode q m ξ i)
        (fun i ξ => blockLocalMark (A := A) q m (ξ.2 i))
        (finFunctionFinEquiv b) = blockLocalCloudEncoded (A := A) q m b := rfl
  rw [hleft] at hengine
  convert hengine using 1
  have hb : finFunctionFinEquiv.symm (finFunctionFinEquiv b) = b :=
    Equiv.symm_apply_apply (finFunctionFinEquiv (m := m) (n := q)) b
  simp only [hb]
  congr 1
  funext n
  rw [div_eq_mul_inv, Nat.cast_pow]

end OTSelector.Reconstruction

/-!
## The remaining single-particle block law

The only producer input that kernelMarkedCloudLaw_blockLocalCloudEncoded_law
leaves open is the single-particle block law

  (markedPointLaw q K).map (blockOnePoint q m)
    = mixturePointLaw (fun _ => (m ^ q)⁻¹)
        (fun c => markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))).

Its content is the in-block mark-law identification: a uniformly distributed
ambient position with a mark sampled from K at that position, after encoding the
block label and dilating the local coordinate, has the label-dependent law whose
block fibre is the marked point law of the block-rescaled kernel.  The natural
proof is by Fubini over the block partition: writing markedPointLaw as
cubeMeasure composed with K, restricting the position to the preimage of the
encoded label c and changing variables from the ambient position to the dilated
local position (the block identity x = blockRescaleMap c (blockScaledLocalPoint
q m x), available from blockLabelCode_eq_finFunctionFinEquiv_iff and
blockScaledLocalPoint_eq_sub), the cube measure on the block is carried to
(m ^ q)⁻¹ times the cube measure, which is exactly the fibre weight.

The ingredients already in the library for that proof are: the position-level
decomposition map_blockLabelCode_scaledLocal_cubeMeasure (label uniform and
independent of the dilated local position), the point of the compProd
representation Measure.compProd_apply, the block-label inversion
blockLabelCode_eq_finFunctionFinEquiv_iff, and the block-rescaling identity.
Once this single-particle law is available, applying
kernelMarkedCloudLaw_blockLocalCloudEncoded_law for every block c and feeding the
result into the ambient leaf-block expectation identity upgrades
BlockKernelComparison from the conditional form of
FinslerOriginalBlockExtractionLaw to the unconditional form.
-/