import OTSelector.MeasureTheory.GeometricWindowDensities
import OTSelector.MeasureTheory.NormalizedLabelClockDensity
import OTSelector.MeasureTheory.WindowJointAbsoluteContinuity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.GeometricWindowNormalization.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.GeometricWindowNormalization`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.GeometricWindowNormalization

Conditions: A finite measure, measurable label/clock maps and a countable measurable almost-everywhere cover with actual product-reference density identities.
Objects: The label marginal, a countably assembled joint density, and its conditional clock probability kernels.
Proof detail: Derive joint absolute continuity from the window laws, combine reference Radon–Nikodym densities, and apply conditional-density normalization on the label marginal.

## Mathematical sources

- D. H. Fremlin, *Measure Theory, Volume 2*: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure. https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf
- D. H. Fremlin, *Measure Theory, Volume 4*: Section 452A–452F (integration of families and disintegrations), 452M (product disintegration). https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Equation eq:compact-conditional-whole-densities and preceding geometric conditional-density window assembly. ../main.tex#L1849

Source relation: Countable-window and Radon–Nikodym bookkeeping for the manuscript construction. The normalization is almost everywhere for the actual marginal; no positive density lower bound or extra joint-density oracle is assumed.
-/

/-!
# Deriving conditional normalization from actual window laws

Each actual window joint density determines its own marginal and conditional
density. Countable assembly therefore derives joint absolute continuity and the
whole conditional density without a separate joint absolute-continuity premise.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- Actual product-reference window formulas already suffice for the complete
original conditional density and its normalization. -/
theorem labelClock_geometric_window_densities_of_pieces
    {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
    (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (O : ℕ → Set M) (hO : ∀ j, MeasurableSet (O j))
    (hcover : ∀ᵐ x ∂η, x ∈ ⋃ j, O j)
    (β : ℕ → Measure Z) (hβ : ∀ j, SigmaFinite (β j))
    (G : ℕ → Z × ℝ → ℝ≥0∞) (hG : ∀ j, Measurable (G j))
    (hpiece : ∀ j, (η.restrict (disjointed O j)).map (fun x ↦ (a x, u x)) =
      ((β j).prod (volume : Measure ℝ)).withDensity (G j)) :
    let lambda := η.map a
    let R := lambda.prod (volume : Measure ℝ)
    let H := fun y : Z × ℝ ↦ ∑' j, (β j).rnDeriv lambda y.1 * G j y
    η.map (fun x ↦ (a x, u x)) ≪ R ∧
      Measurable H ∧ R.withDensity H = η.map (fun x ↦ (a x, u x)) ∧
      (∀ᵐ z ∂lambda, ∫⁻ s, H (z, s) ∂volume = 1) ∧
      (∀ᵐ z ∂lambda,
        (volume : Measure ℝ).withDensity (fun s ↦ H (z, s)) = condDistrib u a η z) := by
  have hjoint := labelClock_joint_absolutelyContinuous_of_window_pieces η ha hu O hO
    hcover (fun j ↦ by
      let _instWindowReference : SigmaFinite (β j) := hβ j
      exact map_labelClock_absolutelyContinuous_of_density
        (η.restrict (disjointed O j)) hu (β j) (hG j) (hpiece j))
  exact ⟨hjoint,
    (labelClock_geometric_window_densities η ha hu O hO hcover hjoint β hβ G hG hpiece).2⟩

end OTSelector.Reconstruction

end
