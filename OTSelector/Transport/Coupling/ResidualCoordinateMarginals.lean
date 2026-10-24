import OTSelector.Probability.SubcouplingTypeMarking
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawResidualCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawResidualCoordinates`; the selected original proof blocks follow. -/
section

/-!
# Transport.Coupling.ResidualCoordinateMarginals

## Lemma skeleton

* **Conditions:** A paired law carried by equality of two measurable coordinates and a common subplan; frozen-law residual statements supply coordinate balance and component domination.
* **Objects:** Equal transverse coordinate marginals for the common subplan and both residual laws.
* **Proof detail:** Transfer the equality event to dominated measures, commute coordinate maps with projections, and subtract the same finite common coordinate law from the two balanced marginals.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (composition): Residual coordinate balance from actual submeasure algebra; the original-residual form uses the positive difference even without separate input domination.
-/

/-!
Balanced transverse marginals of both residual laws after common-subplan freezing.
The selected common subplan may be chosen arbitrarily below the original pairing.
-/

open Set MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Every subplan of an original equal-coordinate pairing preserves that equality. -/
theorem common_subplan_coordinate_marginals
    (π χ : Measure (X × Y)) (hχ : χ ≤ π)
    (cs : X → Z) (ct : Y → Z) (hcs : Measurable cs) (hct : Measurable ct)
    (hpaired : ∀ᵐ p ∂π, cs p.1 = ct p.2) :
    (χ.map Prod.fst).map cs = (χ.map Prod.snd).map ct := by
  rw [Measure.map_map hcs measurable_fst, Measure.map_map hct measurable_snd]
  exact Measure.map_congr (ae_mono hχ hpaired)

/-- Frozen residual colors have exactly the same coordinate law. This retains
spatial population cancellation which scalar total variation would discard. -/
theorem frozen_residual_coordinate_marginals
    (π χ : Measure (X × Y)) [IsFiniteMeasure π] (hχ : χ ≤ π)
    (νs : Measure X) (νt : Measure Y)
    (hχs : χ.map Prod.fst ≤ νs) (hχt : χ.map Prod.snd ≤ νt)
    (cs : X → Z) (ct : Y → Z) (hcs : Measurable cs) (hct : Measurable ct)
    (hpaired : ∀ᵐ p ∂π, cs p.1 = ct p.2)
    (hfrozen : νs.map cs = νt.map ct) :
    (νs - χ.map Prod.fst).map cs = (νt - χ.map Prod.snd).map ct := by
  have : IsFiniteMeasure χ := isFiniteMeasure_of_le π hχ
  rw [PopulationSubcouplingTypes.map_sub_of_le _ _ hχs cs hcs,
    PopulationSubcouplingTypes.map_sub_of_le _ _ hχt ct hct, hfrozen,
    common_subplan_coordinate_marginals π χ hχ cs ct hcs hct hpaired]

/-- The actual residual remains a subplan of the original equal-coordinate
pairing, including its original support and clock legality. -/
theorem original_residual_coordinate_marginals
    (π χ : Measure (X × Y)) (cs : X → Z) (ct : Y → Z)
    (hcs : Measurable cs) (hct : Measurable ct)
    (hpaired : ∀ᵐ p ∂π, cs p.1 = ct p.2) :
    ((π - χ).map Prod.fst).map cs = ((π - χ).map Prod.snd).map ct :=
  common_subplan_coordinate_marginals π (π - χ) Measure.sub_le cs ct hcs hct hpaired

end OTSelector.Reconstruction

end
end
