import OTSelector.MeasureTheory.ConditionalAbsoluteContinuity
import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.OptimalFaceDisintegration
import OTSelector.Transport.Coupling.OptimalPlanExistence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OptimalFaceDensities.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OptimalFaceDensities`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OptimalFaceDensities

**Conditions:** Compactly carried original probabilities are absolutely continuous with respect to one finite reference measure, and measurable labels are constant on calibrated pairs.

**Objects:** The derived common label marginal and jointly measurable normalized conditional densities for the entire original optimal face.

**Proof detail:** Construct an actual optimizer to force equality of label marginals, disintegrate the two populations against the common reference conditionals, and replace the conditional marginals in the whole-face kernel characterization by their RN densities.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110), Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (PDF pages 110–111).

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Actual conditional densities throughout the original optimal face

Compactly supported original probabilities determine a common calibrated optimal face.
For measurable labels constant on its calibrated pairs, existence of an original
optimizer forces equality of the label marginals. Absolute continuity against one
finite reference measure then supplies normalized jointly measurable conditional
densities for both populations over this derived common label measure.
The labels and the geometric conditional-reference estimates remain separate inputs.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]

/-- The original optimal face has normalized conditional densities over its derived
common label law, without a prescribed balancing condition or a positive density bound. -/
theorem exists_optimal_face_conditional_densities
    (μ ν m : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsFiniteMeasure m] (hμm : μ ≪ m) (hνm : ν ≪ m)
    {K : Set M} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (hν : ∀ᵐ x ∂ν, x ∈ K) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧
      ∀ (N : Set M), MeasurableSet N → (∀ᵐ x ∂μ, x ∈ N) → (∀ᵐ y ∂ν, y ∈ N) →
      ∀ label : M → Z, Measurable label →
      (∀ x ∈ N, ∀ y ∈ N, f y - f x = dist x y → label x = label y) →
      μ.map label = ν.map label ∧ ∃ wμ wν : Z → M → ℝ≥0∞,
        Measurable (Function.uncurry wμ) ∧ Measurable (Function.uncurry wν) ∧
        (∀ᵐ z ∂μ.map label,
          (condDistrib id label m z).withDensity (wμ z) = condDistrib id label μ z ∧
          (condDistrib id label m z).withDensity (wν z) = condDistrib id label ν z ∧
          (∫⁻ x, wμ z x ∂condDistrib id label m z) = 1 ∧
          (∫⁻ x, wν z x ∂condDistrib id label m z) = 1) ∧
        ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
          ∃ κ : Kernel Z (M × M), IsMarkovKernel κ ∧ κ ∘ₘ μ.map label = π ∧
            ∀ᵐ z ∂μ.map label,
              Vlasov.IsCoupling (κ z)
                ((condDistrib id label m z).withDensity (wμ z))
                ((condDistrib id label m z).withDensity (wν z)) ∧
              ∀ᵐ p ∂κ z, p.1 ∈ N ∧ p.2 ∈ N ∧ f p.2 - f p.1 = dist p.1 p.2 := by
  obtain ⟨x₀, hx₀⟩ := hμ.exists
  obtain ⟨f, hf, _, hface⟩ :=
    exists_optimal_face_disintegration_of_compact_carrier (Z := Z) μ ν hK hμ hν ⟨x₀, hx₀⟩
  obtain ⟨π₀, hπ₀⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν hK hμ hν
  refine ⟨f, hf, fun N hN hμN hνN label hlabel heq ↦ ?_⟩
  have hiff := hface N hN hμN hνN label label hlabel hlabel heq
  have hbalance := ((hiff π₀).mp hπ₀).1
  obtain ⟨wμ, hwμ, hdμ⟩ := exists_measurable_condDistrib_density hμm hlabel
  obtain ⟨wν, hwν, hdν⟩ := exists_measurable_condDistrib_density hνm hlabel
  rw [← hbalance] at hdν
  have hd : ∀ᵐ z ∂μ.map label,
      (condDistrib id label m z).withDensity (wμ z) = condDistrib id label μ z ∧
      (condDistrib id label m z).withDensity (wν z) = condDistrib id label ν z ∧
      (∫⁻ x, wμ z x ∂condDistrib id label m z) = 1 ∧
      (∫⁻ x, wν z x ∂condDistrib id label m z) = 1 := by
    filter_upwards [hdμ, hdν] with z hzμ hzν
    exact ⟨hzμ.1, hzν.1, hzμ.2, hzν.2⟩
  refine ⟨hbalance, wμ, wν, hwμ, hwν, hd, fun π ↦ ?_⟩
  rw [hiff π, and_iff_right hbalance]
  constructor
  · rintro ⟨κ, hκ, hrec, hc⟩
    refine ⟨κ, hκ, hrec, ?_⟩
    filter_upwards [hc, hd] with z hz hdz
    simpa only [hdz.1, hdz.2.1] using hz
  · rintro ⟨κ, hκ, hrec, hc⟩
    refine ⟨κ, hκ, hrec, ?_⟩
    filter_upwards [hc, hd] with z hz hdz
    simpa only [hdz.1, hdz.2.1] using hz

end OTSelector.Reconstruction

end
