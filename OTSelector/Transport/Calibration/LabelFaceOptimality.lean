import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.LabelDisintegration
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCalibratedFaceOptimality.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCalibratedFaceOptimality`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalCalibratedFaceOptimality

**Conditions:** An existing original label-face equivalence, common original coupling and calibrated support on the full-marginal set.

**Objects:** Return of the unchanged limiting coupling to the original optimal face.

**Proof detail:** Disintegrate the original coupling over its common labels, transfer calibration to forward ordered conditional pairs, and apply the reverse implication of the supplied whole-face characterization.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110), Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (PDF pages 110–111).

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Calibration returns an original limiting coupling to the optimal face

The existing label-face characterization is consumed in the reverse direction.
Support and conditional couplings are constructed from the original marginals.
-/
open Set Function MeasureTheory ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]

/-- Exact original marginals and zero calibrated slack suffice for membership
in the original optimal face. No limiting disintegration is assumed. -/
theorem isOptimalCoupling_of_calibrated_of_original_label_face
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : M → ℝ) (hu : Continuous u) (a : M → Z) (ha : Measurable a)
    (N : Set M) (hN : MeasurableSet N)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hface : ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
      ∃ k : Kernel Z (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
        ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
          (condDistrib id a μ z) (condDistrib id a ν z) ∧
          ∀ᵐ p ∂k z, p.1 ∈ N ∧ p.2 ∈ N ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    (π : Measure (M × M)) (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2) :
    IsOptimalCoupling edist μ ν π := by
  let R : Set (M × M) := {p | p.1 ∈ N ∧ p.2 ∈ N ∧ u p.2 - u p.1 = dist p.1 p.2}
  have hR : MeasurableSet R := (measurable_fst hN).inter ((measurable_snd hN).inter
    (measurableSet_eq_fun ((hu.measurable.comp measurable_snd).sub
      (hu.measurable.comp measurable_fst)) (continuous_fst.dist continuous_snd).measurable))
  have hs : ∀ᵐ p ∂π, p ∈ R := by
    have hleft : ∀ᵐ p ∂π, p.1 ∈ N := ae_of_ae_map measurable_fst.aemeasurable
      (by rwa [hπ.1])
    have hright : ∀ᵐ p ∂π, p.2 ∈ N := ae_of_ae_map measurable_snd.aemeasurable
      (by rwa [hπ.2])
    filter_upwards [hleft, hright, hcal] with p hp hq hc using ⟨hp, hq, hc⟩
  obtain ⟨_, k, hk, hrec, hc⟩ :=
    (isCoupling_supported_iff_conditional_couplings ha ha hR
      (fun p hp ↦ ((horder p.1 hp.1 p.2 hp.2.1).mpr hp.2.2).1)).mp ⟨hπ, hs⟩
  apply (hface π).mpr
  refine ⟨k, hk, hrec, hc.mono fun z hz ↦ ⟨hz.1, ?_⟩⟩
  filter_upwards [hz.2] with p hp
  exact ⟨hp.1, hp.2.1, (horder p.1 hp.1 p.2 hp.2.1).mpr hp.2.2⟩

end OTSelector.Reconstruction

end
end
