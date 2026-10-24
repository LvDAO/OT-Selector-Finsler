import Mathlib.MeasureTheory.Function.L2Space
import OTSelector.MeasureTheory.LocalFiniteMeasureProbability

/-!
Conditions: Measurable original observations on the same row experiments and tight marginal-law families; the subsequence result additionally uses probability rows and the stated separable metrizable Hausdorff carrier hypotheses.

Objects: Tight joint pair/triple laws and an increasing weakly convergent subsequence of the actual triple pushforward laws.

Proof detail: Choose compact marginal sets with small escaped masses; their product is compact and the joint escape is bounded by the sum of marginal escapes. Apply the actual probability-law compactness theorem to the resulting joint family.

References: D. H. Fremlin: Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability; Rick Durrett: Section 2.3, Theorem 2.3.1 and preceding union-tail estimate, pp. 67–68.
Relation: A joint-tightness/Prokhorov consequence on unchanged original sample spaces. No independence of the observations and no replacement coupling are required.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.OriginalJointLawTightness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.OriginalJointLawTightness`; the selected original proof blocks follow. -/
section

/-!
# Joint tightness on original sample spaces

Tight marginal laws give tight joint laws of observations on the same original
probability space. No independence or replacement coupling is used.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace

noncomputable section
namespace OTSelector.Probability

/-- Two observations retain their actual joint law when obtaining tightness from
the two marginal families. -/
theorem isTightMeasureSet_original_joint_of_marginals
    {I X Y : Type*} {Ω : I → Type*}
    [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) (f : ∀ i, Ω i → X) (g : ∀ i, Ω i → Y)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hft : IsTightMeasureSet (range (fun i ↦ (P i).map (f i))))
    (hgt : IsTightMeasureSet (range (fun i ↦ (P i).map (g i)))) :
    IsTightMeasureSet (range (fun i ↦ (P i).map (fun ω ↦ (f i ω, g i ω)))) := by
  refine IsTightMeasureSet.prodMk (hft.subset ?_) (hgt.subset ?_)
  · rintro _ ⟨ν, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (Measure.fst_map_prodMk (hg i)).symm⟩
  · rintro _ ⟨ν, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (Measure.snd_map_prodMk (hf i)).symm⟩

/-- The original common scene of two plans and a target cloud is tight whenever
its actual three marginal families are tight. -/
theorem isTightMeasureSet_original_triple_of_marginals
    {I X Y Z : Type*} {Ω : I → Type*}
    [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i))
    (f : ∀ i, Ω i → X) (g : ∀ i, Ω i → Y) (h : ∀ i, Ω i → Z)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hh : ∀ i, Measurable (h i))
    (hft : IsTightMeasureSet (range (fun i ↦ (P i).map (f i))))
    (hgt : IsTightMeasureSet (range (fun i ↦ (P i).map (g i))))
    (hht : IsTightMeasureSet (range (fun i ↦ (P i).map (h i)))) :
    IsTightMeasureSet (range (fun i ↦ (P i).map (fun ω ↦ (f i ω, g i ω, h i ω)))) := by
  apply isTightMeasureSet_original_joint_of_marginals P f (fun i ω ↦ (g i ω, h i ω)) hf
    (fun i ↦ (hg i).prodMk (hh i)) hft
  exact isTightMeasureSet_original_joint_of_marginals P g h hg hh hgt hht

/-- Prokhorov extracts one common subsequence of the actual original joint laws,
preserving the correlations between all three observations. -/
theorem exists_tendsto_subseq_original_triple_of_marginals
    {X Y Z : Type*} {Ω : ℕ → Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [T2Space Y] [PseudoMetrizableSpace Y] [SecondCountableTopology Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [T2Space Z] [PseudoMetrizableSpace Z] [SecondCountableTopology Z]
    [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (f : ∀ i, Ω i → X) (g : ∀ i, Ω i → Y) (h : ∀ i, Ω i → Z)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hh : ∀ i, Measurable (h i))
    (hft : IsTightMeasureSet (range (fun i ↦ (P i).map (f i))))
    (hgt : IsTightMeasureSet (range (fun i ↦ (P i).map (g i))))
    (hht : IsTightMeasureSet (range (fun i ↦ (P i).map (h i)))) :
    let laws : ℕ → ProbabilityMeasure (X × Y × Z) := fun i ↦
      ProbabilityMeasure.map (⟨P i, inferInstance⟩ : ProbabilityMeasure (Ω i))
        (f := fun ω ↦ (f i ω, g i ω, h i ω))
        ((hf i).prodMk ((hg i).prodMk (hh i))).aemeasurable
    ∃ Q : ProbabilityMeasure (X × Y × Z), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (laws ∘ φ) atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_probabilityMeasure_of_isTight
  exact isTightMeasureSet_original_triple_of_marginals P f g h hf hg hh hft hgt hht

end OTSelector.Probability

end
end
