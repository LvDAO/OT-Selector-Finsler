import Mathlib.Probability.Kernel.CondDistrib
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Transport.Coupling.CostEquivalence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneOriginalOptimalFaceCarrier.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneOriginalOptimalFaceCarrier`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.OptimalFaceCarrier

* **Conditions:** The supplied whole-optimal-face representation reconstructs every optimizer by a conditional kernel carried by regular same-label forward pairs.
* **Objects:** The original optimizer itself is carried by regular same-label forward pairs.
* **Proof detail:** Select the representing kernel of the given optimum and transfer its almost-everywhere carrier through the exact mixture identity.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition label prop:general-optimal-face, lines 422–483, equation eq:general-optimal-face.

Source relation (adapter): A carrier-transfer adapter of an explicitly assumed representation, rather than an independent proof of the whole-face theorem.
-/

/-!
# The actual regular same-ray carrier of every original optimal plan

The original whole-face representation supplies an actual conditional kernel carried by regular
same-label forward pairs. Its exact mixture identity transfers that support to the original plan.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {a : M → (ℚ → M)}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The unchanged original optimal face carries each original optimizer on regular endpoints
with one common original ray label and forward potential order. -/
theorem ae_original_regular_sameLabel_forward_of_optimal_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {π : Measure (M × M)}
    (hπ : let _inst : MetricSpace M := F.metricSpace; IsOptimalCoupling edist μ ν π) :
    ∀ᵐ p ∂π, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2 := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  dsimp only at hface hπ
  obtain ⟨k, hk, hcomp, hsupp⟩ := (hface π).mp hπ
  have hN := hF.measurableSet_potentialRegularDomain hcomplete u
  have hR : MeasurableSet {p : M × M | p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2} :=
    (measurable_fst hN).inter ((measurable_snd hN).inter
      ((measurableSet_eq_fun (ha.comp measurable_fst) (ha.comp measurable_snd)).inter
        (measurableSet_le (hu.continuous.measurable.comp measurable_fst)
          (hu.continuous.measurable.comp measurable_snd))))
  rw [← hcomp]
  apply Measure.ae_comp_of_ae_ae hR
  filter_upwards [hsupp] with z hz using hz.2

end OTSelector.Reconstruction

end
