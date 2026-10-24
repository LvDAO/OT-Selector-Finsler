import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
import OTSelector.Probability.CommonSubmeasureSampling
import OTSelector.Transport.Coupling.CommonMarginalSubplan
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CommonSubplanSampling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CommonSubplanSampling`; the selected original proof blocks follow. -/
section

/-!
# Probability.CommonSubplanSampling

## Lemma skeleton

* **Conditions:** An original coupling and a fixed common subplan whose coordinate marginals are also dominated by the comparison probability laws.
* **Objects:** Two exact common-sampling couplings charged to the same subplan complement, a normalized-freezing version and iid marginal identities.
* **Proof detail:** Use each actual subplan marginal as the diagonal common part, identify both discarded marginal masses with the same original complement and take finite products. The freezing wrapper first constructs a shared retained subplan with its stated bound.

## Mathematical sources

- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14): Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.

Source relation (composition): Subplan-compatible sampling assembly; different color sample counts are permitted and no independent replacement of the original coupling is made.
-/

/-!
# Common sampling compatible with one fixed original subplan

The two colors retain the marginals of the same original subplan. Their iid
sample counts may differ; all changes are charged to its fixed complement.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableEq X] [MeasurableEq Y]

private theorem residual_marginal_mass
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (π χ : Measure A) [IsFiniteMeasure π] (hχ : χ ≤ π)
    {f : A → B} (hf : Measurable f) :
    (π.map f - χ.map f) univ = (π - χ) univ := by
  let _instChi : IsFiniteMeasure χ := isFiniteMeasure_of_le π hχ
  rw [Measure.sub_apply .univ (Measure.map_mono hχ hf),
    Measure.sub_apply .univ hχ, Measure.map_apply hf MeasurableSet.univ,
    Measure.map_apply hf MeasurableSet.univ, preimage_univ]

/-- The marginals of one retained original subplan produce two exact sampling
couplings. Both disagreement probabilities are bounded by its original complement. -/
theorem exists_common_sampling_of_original_subplan
    (π χ : Measure (X × Y)) [IsFiniteMeasure π]
    (μ μ' : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (ν ν' : Measure Y) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hπ : Vlasov.IsCoupling π μ ν) (hχ : χ ≤ π)
    (hχ₀ : χ.map Prod.fst ≤ μ') (hχ₁ : χ.map Prod.snd ≤ ν') :
    ∃ γ₀ : Measure (X × X), ∃ γ₁ : Measure (Y × Y),
      IsProbabilityMeasure γ₀ ∧ IsProbabilityMeasure γ₁ ∧
      γ₀.map Prod.fst = μ ∧ γ₀.map Prod.snd = μ' ∧
      γ₁.map Prod.fst = ν ∧ γ₁.map Prod.snd = ν' ∧
      γ₀ {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
      γ₁ {p | p.1 ≠ p.2} ≤ (π - χ) univ := by
  have h₀ : χ.map Prod.fst ≤ μ := by
    simpa only [hπ.1] using Measure.map_mono hχ measurable_fst
  have h₁ : χ.map Prod.snd ≤ ν := by
    simpa only [hπ.2] using Measure.map_mono hχ measurable_snd
  obtain ⟨γ₀, hp₀, hf₀, hs₀, hb₀⟩ :=
    exists_common_sampling_of_submeasure μ μ' (χ.map Prod.fst) h₀ hχ₀
  obtain ⟨γ₁, hp₁, hf₁, hs₁, hb₁⟩ :=
    exists_common_sampling_of_submeasure ν ν' (χ.map Prod.snd) h₁ hχ₁
  have he₀ := residual_marginal_mass π χ hχ measurable_fst
  have he₁ := residual_marginal_mass π χ hχ measurable_snd
  rw [hπ.1] at he₀
  rw [hπ.2] at he₁
  exact ⟨γ₀, γ₁, hp₀, hp₁, hf₀, hs₀, hf₁, hs₁, hb₀.trans_eq he₀, hb₁.trans_eq he₁⟩

/-- Actual freezing data on both colors produce one fixed original residual
subplan and compatible common sampling, without a sample balance condition. -/
theorem exists_normalized_freezing_subplan_sampling
    (μ₀ μ₁ : Measure X) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    (ν₀ ν₁ : Measure Y) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (D₀ : FiniteLawFreezingBound μ₀ μ₁ ε) (D₁ : FiniteLawFreezingBound ν₀ ν₁ ε)
    (hμ₁ : 0 < μ₁.real univ) (hν₁ : 0 < ν₁.real univ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π (normalizedFiniteLaw μ₀) (normalizedFiniteLaw ν₀)) :
    ∃ χ : Measure (X × Y), χ ≤ π ∧
      χ.map Prod.fst ≤ normalizedFiniteLaw μ₁ ∧
      χ.map Prod.snd ≤ normalizedFiniteLaw ν₁ ∧
      (π - χ) univ ≤ ENNReal.ofReal (6 * ε / (1 - ε)) ∧
      ∃ γ₀ : Measure (X × X), ∃ γ₁ : Measure (Y × Y),
        IsProbabilityMeasure γ₀ ∧ IsProbabilityMeasure γ₁ ∧
        γ₀.map Prod.fst = normalizedFiniteLaw μ₀ ∧
        γ₀.map Prod.snd = normalizedFiniteLaw μ₁ ∧
        γ₁.map Prod.fst = normalizedFiniteLaw ν₀ ∧
        γ₁.map Prod.snd = normalizedFiniteLaw ν₁ ∧
        γ₀ {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
        γ₁ {p | p.1 ≠ p.2} ≤ (π - χ) univ := by
  let _instMu0 := normalizedFiniteLaw_probability μ₀ (D₀.normalized_variation hε hε1 hμ₁).1
  let _instMu1 := normalizedFiniteLaw_probability μ₁ hμ₁
  let _instNu0 := normalizedFiniteLaw_probability ν₀ (D₁.normalized_variation hε hε1 hν₁).1
  let _instNu1 := normalizedFiniteLaw_probability ν₁ hν₁
  obtain ⟨θ₀, hθ₀, hθ₀', _, hb₀⟩ := D₀.normalized_common_part hε hε1 hμ₁
  obtain ⟨θ₁, hθ₁, hθ₁', _, hb₁⟩ := D₁.normalized_common_part hε hε1 hν₁
  let χ := commonMarginalSubplan π (normalizedFiniteLaw μ₀) (normalizedFiniteLaw ν₀) θ₀ θ₁
  obtain ⟨hχ, hχ₀, hχ₁, _, hmass⟩ := commonMarginalSubplan_spec π
    (normalizedFiniteLaw μ₀) (normalizedFiniteLaw ν₀) hπ θ₀ θ₁ hθ₀ hθ₁
  have hb : (π - χ) univ ≤ ENNReal.ofReal (6 * ε / (1 - ε)) := by
    refine hmass.trans ((add_le_add hb₀ hb₁).trans_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine ⟨χ, hχ, hχ₀.trans hθ₀', hχ₁.trans hθ₁', hb, ?_⟩
  exact exists_common_sampling_of_original_subplan π χ
    (normalizedFiniteLaw μ₀) (normalizedFiniteLaw μ₁)
    (normalizedFiniteLaw ν₀) (normalizedFiniteLaw ν₁)
    hπ hχ (hχ₀.trans hθ₀') (hχ₁.trans hθ₁')

/-- The common sampling construction preserves both full iid array laws exactly. -/
theorem iid_common_sampling_marginals {I A : Type*} [Fintype I] [MeasurableSpace A]
    (γ : Measure (A × A)) [IsProbabilityMeasure γ]
    (μ ν : Measure A) (hμ : γ.map Prod.fst = μ) (hν : γ.map Prod.snd = ν) :
    (Measure.pi (fun _ : I ↦ γ)).map (fun p i ↦ (p i).1) =
        Measure.pi (fun _ : I ↦ μ) ∧
    (Measure.pi (fun _ : I ↦ γ)).map (fun p i ↦ (p i).2) =
        Measure.pi (fun _ : I ↦ ν) := by
  constructor
  · rw [Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
    simp only [hμ]
  · rw [Measure.pi_map_pi (fun _ ↦ measurable_snd.aemeasurable)]
    simp only [hν]

end OTSelector.Reconstruction

end
