import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
import OTSelector.MeasureTheory.RetainedLawVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalRetainedMarginalVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalRetainedMarginalVariation`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.RetainedMarginalVariation

## Lemma skeleton

* **Conditions:** Probability original laws converging in full variation, finite retained submeasures losing vanishing mass and optionally a measurable observation.
* **Objects:** Variation convergence of normalized retained laws and their observed marginals.
* **Proof detail:** Combine the full variation triangle inequality with the normalized-submeasure removal bound; pushforward contracts variation and squeeze both error terms to zero.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (composition): Variation/removal assembly for varying original laws, allowing arbitrary retained pairings.
-/

/-! Varying original conditional laws and arbitrary retained pairings have
convergent retained marginals when only the actual removed mass vanishes. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
set_option linter.style.haveILetI false

/-- The actual signed total variation obeys the ordinary three-law triangle. -/
theorem original_totalVariation_real_triangle
    {X : Type*} [MeasurableSpace X]
    (μ ν ξ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (μ.toSignedMeasure - ξ.toSignedMeasure).totalVariation.real univ ≤
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ +
      (ν.toSignedMeasure - ξ.toSignedMeasure).totalVariation.real univ := by
  have heq : μ.toSignedMeasure - ξ.toSignedMeasure =
      (μ.toSignedMeasure - ν.toSignedMeasure) +
        (ν.toSignedMeasure - ξ.toSignedMeasure) := by abel
  rw [heq]
  have hb : ((μ.toSignedMeasure - ν.toSignedMeasure) +
      (ν.toSignedMeasure - ξ.toSignedMeasure)).totalVariation univ ≤
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ +
      (ν.toSignedMeasure - ξ.toSignedMeasure).totalVariation univ := by
    simp only [SignedMeasure.totalVariation_eq_variation]
    exact VectorMeasure.variation_add_le univ
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨measure_ne_top _ _,measure_ne_top _ _⟩) hb
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
  exact hreal

/-- Original varying probability laws and their arbitrary actual sublaws
approach the same original limit whenever both the original variation and
the original removed masses vanish. -/
theorem tendsto_totalVariation_normalized_varying_submeasure
    {X J : Type*} [MeasurableSpace X]
    (μ : J → Measure X) [∀ j, IsProbabilityMeasure (μ j)]
    (ξ : Measure X) [IsProbabilityMeasure ξ]
    (ν : J → Measure X) [∀ j, IsFiniteMeasure (ν j)]
    (l : Filter J) (δ : J → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hvariation : Tendsto (fun j ↦
      ((μ j).toSignedMeasure - ξ.toSignedMeasure).totalVariation.real univ) l (𝓝 0))
    (hdata : ∀ᶠ j in l, ν j ≤ μ j ∧ 0 ≤ δ j ∧ δ j < 1 ∧ 1 - δ j ≤ (ν j).real univ) :
    Tendsto (fun j ↦ ((normalizedFiniteLaw (ν j)).toSignedMeasure -
      ξ.toSignedMeasure).totalVariation.real univ) l (𝓝 0) := by
  have hden : Tendsto (fun j ↦ 2 * δ j / (1 - δ j)) l (𝓝 0) := by
    have hh := (hδ.const_mul 2).div (tendsto_const_nhds.sub hδ) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    change Tendsto (fun j ↦ 2 * δ j / (1 - δ j)) l (𝓝 ((2 : ℝ) * 0 / (1 - 0))) at hh
    simpa only [mul_zero,sub_zero,zero_div] using hh
  have hbound : Tendsto (fun j ↦ 2 * δ j / (1 - δ j) +
      ((μ j).toSignedMeasure - ξ.toSignedMeasure).totalVariation.real univ) l (𝓝 0) := by
    simpa only [add_zero] using hden.add hvariation
  have hnonneg : ∀ᶠ j in l, 0 ≤ ((normalizedFiniteLaw (ν j)).toSignedMeasure -
      ξ.toSignedMeasure).totalVariation.real univ :=
    Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg
  have hupper : ∀ᶠ j in l, ((normalizedFiniteLaw (ν j)).toSignedMeasure -
      ξ.toSignedMeasure).totalVariation.real univ ≤ 2 * δ j / (1 - δ j) +
      ((μ j).toSignedMeasure - ξ.toSignedMeasure).totalVariation.real univ := by
    filter_upwards [hdata] with j hj
    have htriangle := original_totalVariation_real_triangle (normalizedFiniteLaw (ν j)) (μ j) ξ
    have hloss := totalVariation_normalized_submeasure_le_of_mass (μ j) (ν j)
      hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
    linarith only [htriangle,hloss]
  exact squeeze_zero' hnonneg hupper hbound

/-- An arbitrary observed marginal of actual retained original pair laws
converges using only variation of the original observed marginal. The
original pair law itself need not converge or be selected continuously. -/
theorem tendsto_totalVariation_normalized_retained_observation
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : J → Measure X) [∀ j, IsProbabilityMeasure (π j)]
    (χ : J → Measure X) [∀ j, IsFiniteMeasure (χ j)]
    (f : X → Y) (hf : Measurable f) (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (l : Filter J) (δ : J → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hvariation : Tendsto (fun j ↦
      (((π j).map f).toSignedMeasure - ξ.toSignedMeasure).totalVariation.real univ) l (𝓝 0))
    (hdata : ∀ᶠ j in l, χ j ≤ π j ∧ 0 ≤ δ j ∧ δ j < 1 ∧ 1 - δ j ≤ (χ j).real univ) :
    Tendsto (fun j ↦ (((normalizedFiniteLaw (χ j)).map f).toSignedMeasure -
      ξ.toSignedMeasure).totalVariation.real univ) l (𝓝 0) := by
  letI : ∀ j, IsProbabilityMeasure ((π j).map f) := fun j ↦ Measure.isProbabilityMeasure_map hf.aemeasurable
  have hm j : ((χ j).map f).real univ = (χ j).real univ := by
    simp only [measureReal_def,Measure.map_apply hf MeasurableSet.univ,preimage_univ]
  have hnormalize j : (normalizedFiniteLaw (χ j)).map f = normalizedFiniteLaw ((χ j).map f) := by
    simp only [normalizedFiniteLaw,hm j,Measure.map_smul]
  simp only [hnormalize]
  apply tendsto_totalVariation_normalized_varying_submeasure (fun j ↦ (π j).map f)
    ξ (fun j ↦ (χ j).map f) l δ hδ hvariation
  filter_upwards [hdata] with j hj
  exact ⟨Measure.map_mono hj.1 hf,hj.2.1,hj.2.2.1,by simpa only [hm] using hj.2.2.2⟩

end OTSelector.Reconstruction

end
end
