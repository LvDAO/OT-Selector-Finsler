import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import OTSelector.Transport.Coupling.LabelClockCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ChartLabelClockEmbedding.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ChartLabelClockEmbedding`; the selected original proof blocks follow. -/
section

/-!
Conditions: The legal inverse chart is measurable on its domain, the label/clock map is injective and the spaces have the stated standard-Borel structure.

Objects: A measurable embedding and almost-everywhere measurable observable readouts.

Proof detail: Restrict to the legal domain, use standard-Borel measurable-injection inverse results and compose the resulting measurable maps.

Sources: D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30); D. H. Fremlin, Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22).
Relation: Library encoding of a legal label-clock embedding, using standard-Borel closure results rather than a named Finsler theorem.
-/

/-!
# Measurable label-clock embeddings on genuine coordinate cores

A legal measurable coordinate core maps through the actual inverse chart into the
original Borel domain. Composing its measurable embedding with the original injective
label-clock map gives an embedding of the coordinate core. Observables pulled back
through the inverse chart are almost everywhere measurable for every restricted law.
Only the inverse chart on its legal domain is used.
-/

open Set MeasureTheory Manifold

noncomputable section
namespace OTSelector.Geometry

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z]

/-- A measurable original observable has an almost everywhere measurable actual
inverse-chart pullback under any coordinate law restricted to a legal measurable core. -/
theorem aemeasurable_chart_observable (old : M) (ν : Measure E)
    {f : M → Z} (hf : Measurable f) {K : Set E} (hK : MeasurableSet K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) :
    AEMeasurable (f ∘ (extChartAt 𝓘(ℝ, E) old).symm) (ν.restrict K) := by
  exact hf.comp_aemeasurable
    (((continuousOn_extChartAt_symm old).mono hKtarget).aemeasurable hK)

/-- The genuine inverse-chart label-clock map embeds each legal measurable coordinate
core whose image lies in the original Borel injectivity domain. -/
theorem measurableEmbedding_chart_labelClock [StandardBorelSpace E]
    [StandardBorelSpace M] [MeasurableSpace.CountablySeparated Z] (old : M)
    {K : Set E} (hK : MeasurableSet K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {N : Set M} (hN : MeasurableSet N)
    (hKN : MapsTo (extChartAt 𝓘(ℝ, E) old).symm K N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val))) :
    MeasurableEmbedding (fun z : K ↦
      (a ((extChartAt 𝓘(ℝ, E) old).symm z.val),
        u ((extChartAt 𝓘(ℝ, E) old).symm z.val))) := by
  let _instChartLabelClockCoreBorel : StandardBorelSpace K := hK.standardBorel
  let _instChartLabelClockDomainBorel : StandardBorelSpace N := hN.standardBorel
  let χ := extChartAt 𝓘(ℝ, E) old
  let g : K → N := fun z ↦ ⟨χ.symm z.val, hKN z.property⟩
  have hi : Continuous (fun z : K ↦ χ.symm z.val) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((continuousOn_extChartAt_symm old).mono hKtarget)
  have hg : Measurable g := hi.measurable.subtype_mk
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact χ.symm.injOn (hKtarget x.property) (hKtarget y.property)
      (congrArg Subtype.val hxy)
  exact (Reconstruction.measurableEmbedding_labelClock hN ha hu hinj).comp
    (hg.measurableEmbedding hginj)

end OTSelector.Geometry

end
end
