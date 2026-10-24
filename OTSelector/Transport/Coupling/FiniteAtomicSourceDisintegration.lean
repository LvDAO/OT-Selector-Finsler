import OTSelector.Transport.Coupling.MixtureLabelQuadraticCost
import OTSelector.Transport.Coupling.MixtureLabelTransfer
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairSourceDisintegration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairSourceDisintegration`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepairSourceDisintegration

**Conditions:** A finite plan’s source is exactly the original finite Dirac array, including repeated observations, and squared transport cost is integrable.

**Objects:** One probability law for every unchanged original source atom, with exact total target and energy.

**Proof detail:** Split the source marginal into its individual Dirac labels by Radon–Nikodym component weights, project each component to the target and use source concentration to identify each deviation integral.

**Sources:** [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22), Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf), Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! A genuine counted-source population coupling gives one probability law
per unchanged original atom, with exactly its actual endpoint transport energy. -/
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {E I : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [MeasurableSingletonClass E] [Fintype I]

/-- The actual RN part carrying one original counted source label. -/
def originalAtomPopulationPart (x : I → E) (π : Measure (E × E)) (i : I) :
    Measure (E × E) :=
  smoothingEndpointCouplingPart (fun i ↦ Measure.dirac (x i))
    (fun _ : Unit ↦ π.snd) π i ()

/-- The true target law assigned to one unchanged original source atom. -/
def originalAtomPopulationLaw (x : I → E) (π : Measure (E × E)) (i : I) : Measure E :=
  (originalAtomPopulationPart x π i).snd

/-- RN source disintegration produces actual unit-mass atom laws whose sum is
the full population target and whose endpoint energies sum to the real plan cost.
Coincident original observations and empty original arrays are covered. -/
theorem originalAtomPopulationLaw_spec (x : I → E) (π : Measure (E × E))
    [IsFiniteMeasure π] (hsource : π.fst = ∑ i, Measure.dirac (x i))
    (hcost : Integrable (fun p ↦ dist p.1 p.2 ^ 2) π) :
    (∀ i, IsProbabilityMeasure (originalAtomPopulationLaw x π i)) ∧
      (∑ i, originalAtomPopulationLaw x π i) = π.snd ∧
      (∀ i, Integrable (fun v ↦ dist (x i) v ^ 2) (originalAtomPopulationLaw x π i)) ∧
      (∑ i, ∫ v, dist (x i) v ^ 2 ∂originalAtomPopulationLaw x π i) =
        ∫ p, dist p.1 p.2 ^ 2 ∂π := by
  classical
  let κ : I → Measure E := fun i ↦ Measure.dirac (x i)
  let τ : Unit → Measure E := fun _ ↦ π.snd
  have hπ : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, τ j) := ⟨hsource, by simp only [Fintype.sum_unique, τ]; rfl⟩
  have hsub (i : I) : originalAtomPopulationPart x π i ≤ π :=
    smoothingEndpointCouplingPart_le κ τ π hπ i ()
  have hfst (i : I) : (originalAtomPopulationPart x π i).fst = Measure.dirac (x i) := by
    simpa only [Fintype.sum_unique, κ, τ, originalAtomPopulationPart, Measure.fst] using
      smoothingEndpointCouplingPart_row κ τ π hπ i
  have hsum : (∑ i, originalAtomPopulationPart x π i) = π := by
    simpa only [Fintype.sum_unique, κ, τ, originalAtomPopulationPart] using
      smoothingEndpointCouplingPart_sum κ τ π hπ
  have hpoint (i : I) : ∀ᵐ p ∂originalAtomPopulationPart x π i, p.1 = x i := by
    apply ae_of_ae_map (μ := originalAtomPopulationPart x π i)
      (p := fun u : E ↦ u = x i) measurable_fst.aemeasurable
    change ∀ᵐ u ∂(originalAtomPopulationPart x π i).fst, u = x i
    rw [hfst]
    simp
  have hdev (i : I) : Measurable (fun v : E ↦ dist (x i) v ^ 2) :=
    (measurable_const.dist measurable_id).pow_const 2
  have hI (i : I) : Integrable (fun v ↦ dist (x i) v ^ 2)
      (originalAtomPopulationLaw x π i) := by
    apply (integrable_map_measure (hdev i).aestronglyMeasurable
      measurable_snd.aemeasurable).2
    exact (hcost.mono_measure (hsub i)).congr ((hpoint i).mono fun p hp ↦ by simp only [Function.comp_apply, hp])
  have hread (i : I) : (∫ v, dist (x i) v ^ 2 ∂originalAtomPopulationLaw x π i) =
      ∫ p, dist p.1 p.2 ^ 2 ∂originalAtomPopulationPart x π i := by
    rw [originalAtomPopulationLaw, Measure.snd,
      integral_map measurable_snd.aemeasurable (hdev i).aestronglyMeasurable]
    exact integral_congr_ae ((hpoint i).mono fun p hp ↦ by simp only [hp])
  refine ⟨?_, ?_, hI, ?_⟩
  · intro i
    have : IsProbabilityMeasure ((originalAtomPopulationPart x π i).map Prod.fst) := by
      change IsProbabilityMeasure (originalAtomPopulationPart x π i).fst
      rw [hfst]
      infer_instance
    have : IsProbabilityMeasure (originalAtomPopulationPart x π i) :=
      Measure.isProbabilityMeasure_of_map Prod.fst
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  · change (∑ i, (originalAtomPopulationPart x π i).map Prod.snd) = π.snd
    rw [← Measure.map_finset_sum' measurable_snd.aemeasurable, hsum]
    rfl
  · simp_rw [hread]
    simpa only [Fintype.sum_unique, κ, τ, originalAtomPopulationPart] using
      smoothingEndpointCouplingPart_integral_sum κ τ π hπ hcost

end OTSelector.Reconstruction

end
end
