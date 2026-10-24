import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Independent Root Readout Kernel

Conditions: A measurable readout f of a sample and an independent root; s-finite sample/root laws for the joint identity, or a probability sample law for the Markov property.

Objects: The explicit kernel w ↦ P.map (ξ ↦ f(ξ,w)), retaining the original sample law.

Proof detail: Combine a constant sample kernel and the identity root kernel, then push through f. Evaluate each fiber using the product with a Dirac mass and compare product sections to obtain the joint reconstruction.

Relation to primary sources: This constructs the conditional readout explicitly from the product experiment. It does not infer independence after a sample-dependent root is selected. S-finite generality is provided by mathlib beyond the finite-family book formulation.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
-/
/-!
# Exact conditional readouts of the original independent-root product experiment

Retain the original root and push the unchanged sample law through its fixed-root readout.
The resulting joint pushforward is exactly the root/kernel composition product.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]

/-- Conditional readout of the unchanged original sample law at a fixed independent root. -/
def originalIndependentRootReadoutKernel (P : Measure Ω) (f : Ω × W → S) : Kernel W S :=
  (Kernel.const W P ×ₖ Kernel.id).map f

instance originalIndependentRootReadoutKernelIsSFinite (P : Measure Ω) [SFinite P]
    (f : Ω × W → S) :
    IsSFiniteKernel (originalIndependentRootReadoutKernel P f) := by
  unfold originalIndependentRootReadoutKernel
  infer_instance

/-- The conditional kernel is the literal fixed-root pushforward of the original law. -/
theorem originalIndependentRootReadoutKernel_apply (P : Measure Ω) [SFinite P]
    {f : Ω × W → S} (hf : Measurable f) (w : W) :
    originalIndependentRootReadoutKernel P f w = P.map (fun ξ ↦ f (ξ, w)) := by
  rw [originalIndependentRootReadoutKernel, Kernel.map_apply _ hf, Kernel.prod_apply,
    Kernel.const_apply, Kernel.id_apply, Measure.prod_dirac,
    Measure.map_map hf measurable_prodMk_right]
  rfl

/-- A measurable readout of a probability law gives an everywhere Markov kernel. -/
theorem isMarkovKernel_originalIndependentRootReadoutKernel
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω × W → S} (hf : Measurable f) :
    IsMarkovKernel (originalIndependentRootReadoutKernel P f) := by
  unfold originalIndependentRootReadoutKernel
  exact Kernel.IsMarkovKernel.map _ hf

/-- The original product experiment, observed together with its unchanged root, is exactly
root law composed with the literal conditional readout kernel. -/
theorem map_prod_root_readout_eq_compProd
    (P : Measure Ω) (ρ : Measure W) [SFinite P] [SFinite ρ]
    {f : Ω × W → S} (hf : Measurable f) :
    (P.prod ρ).map (fun v ↦ (v.2, f v)) =
      ρ ⊗ₘ originalIndependentRootReadoutKernel P f := by
  ext A hA
  rw [Measure.map_apply (measurable_snd.prodMk hf) hA,
    Measure.prod_apply_symm ((measurable_snd.prodMk hf) hA),
    Measure.compProd_apply hA]
  apply lintegral_congr
  intro w
  have hfw : Measurable (fun ξ : Ω ↦ f (ξ, w)) :=
    hf.comp (measurable_id.prodMk measurable_const)
  have hAw : MeasurableSet (Prod.mk w ⁻¹' A) := measurable_prodMk_left hA
  rw [originalIndependentRootReadoutKernel_apply P hf, Measure.map_apply hfw hAw]
  rfl

end OTSelector.Probability
