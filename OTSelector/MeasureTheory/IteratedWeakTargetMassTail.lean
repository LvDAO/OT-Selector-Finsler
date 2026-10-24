import OTSelector.MeasureTheory.IteratedWeakMassTail
import OTSelector.MeasureTheory.LocalFiniteMeasure
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitTargetMassTail.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitTargetMassTail`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakTargetMassTail

## Lemma skeleton

* **Conditions:** Two successive weak scene limits and uniform finite first moments for open target-window masses covering every compact target set.
* **Objects:** Almost-everywhere local finiteness of the full nonproper target projection.
* **Proof detail:** Apply the iterated open-tail mass theorem to the swapped plan coordinates and take the countable target-window intersection.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=59): Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).

Source relation (composition): Target-coordinate counterpart of the iterated source mass argument; no properness is required.
-/

/-!
# Full target projections through successive actual weak limits

The original target-window moment bounds pass through the sample-size weak
limit for each fixed tilt and then through the tilt-index weak limit. Open
superlevel tail bounds give local finiteness of the full nonproper target
projection.
-/

open MeasureTheory Set Filter Topology TopologicalSpace OTSelector.Probability
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

section Marginal
variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

omit [T2Space X] [SecondCountableTopology X] in
/-- Uniform original window bounds produce local finiteness of the full
nonproper target marginal after both actual weak-limit stages. -/
theorem ae_locallyFinite_snd_of_iterated_weak_target_window_bounds
    (P : ℕ → ℕ → ProbabilityMeasure Ω) (Q : ℕ → ProbabilityMeasure Ω)
    (hinner : ∀ k, Tendsto (P k) atTop (𝓝 (Q k)))
    (R : ProbabilityMeasure Ω) (ψ : ℕ → ℕ)
    (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R))
    (π : Ω → LocalFiniteMeasure (X × Y)) (hπ : Continuous π)
    (U : ℕ → Set Y) (hU : ∀ k, IsOpen (U k))
    (hcover : ∀ K : Set Y, IsCompact K → ∃ k, K ⊆ U k)
    (C : ℕ → ℝ≥0∞) (hC : ∀ k, C k ≠ ⊤)
    (hbound : ∀ k n m, (∫⁻ ω, (π ω : Measure (X × Y)) (univ ×ˢ U m)
      ∂(P k n : Measure Ω)) ≤ C m) :
    ∀ᵐ ω ∂(R : Measure Ω), IsFiniteMeasureOnCompacts (π ω : Measure (X × Y)).snd := by
  have hall : ∀ᵐ ω ∂(R : Measure Ω), ∀ m,
      (π ω : Measure (X × Y)) (univ ×ˢ U m) < ⊤ := by
    apply ae_all_iff.mpr
    intro m
    exact ae_lt_top_of_iterated_weak_uniform_lintegral_bound P Q hinner R ψ houter _
      ((LocalFiniteMeasure.lowerSemicontinuous_measure_open (isOpen_univ.prod (hU m))).comp hπ)
      (C m) (hC m) (fun k n ↦ hbound k n m)
  filter_upwards [hall] with ω hω
  constructor
  intro K hK
  obtain ⟨m, hm⟩ := hcover K hK
  rw [Measure.snd, Measure.map_apply measurable_snd hK.measurableSet]
  exact (measure_mono (show Prod.snd ⁻¹' K ⊆ (univ : Set X) ×ˢ U m from
    fun e he ↦ ⟨mem_univ _, hm he⟩)).trans_lt (hω m)

end Marginal
end OTSelector.Reconstruction

end
end
