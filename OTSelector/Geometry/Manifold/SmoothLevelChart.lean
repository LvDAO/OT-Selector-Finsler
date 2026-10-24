import OTSelector.Geometry.Manifold.RegularLevelChart
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SmoothLevelChart.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SmoothLevelChart`; the selected original proof blocks follow. -/
section

/-!
Conditions: A smooth scalar map has a nonzero differential at the center in the stated finite-dimensional real normed space.

Objects: A smooth chart of the level set modeled on the actual kernel, with derivative inclusion and exact local level image.

Proof detail: Invert the scalar-plus-kernel projection map and identify its level-zero slice; compute the differential and kernel dimension.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Jiří Lebl, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57 (https://www.jirka.org/ra/realanal2.pdf#page=51); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Explicit regular-level/implicit-function corollary.
-/

/-!
# A smooth chart for an actual regular level set

A nonzero differential of a smooth real function gives a local parameterization by
its actual kernel. The center differential of the parameterization is the kernel
inclusion. The image is exactly the original level set in a constructed open ambient
neighborhood. Smoothness holds on one open parameter domain, using regularity of the
same implicit inverse throughout a smaller domain of invertible actual derivatives.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A regular level of an actual smooth scalar function has a smooth kernel chart,
with its true center derivative, local image identity and codimension derived. -/
theorem exists_smooth_levelChart {f : E → ℝ} {Ω : Set E} {a : E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (ha : a ∈ Ω)
    (hp : fderiv ℝ f a ≠ 0) :
    let p := fderiv ℝ f a
    ∃ (B : Set p.ker) (σ : p.ker → E) (U : Set E),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧ ContDiffOn ℝ ∞ σ B ∧ σ 0 = a ∧
      MapsTo σ B Ω ∧ (∀ w ∈ B, f (σ w) = f a) ∧
      HasFDerivAt σ p.ker.subtypeL 0 ∧ Function.Injective (fderiv ℝ σ 0) ∧
      InjOn σ B ∧ IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧
      σ '' B = U ∩ {x | f x = f a} ∧
      Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E := by
  exact exists_contDiff_levelChart (by simp : (1 : ℕ∞ω) ≤ ∞) hΩ hf ha hp

end OTSelector.Geometry

end
end
