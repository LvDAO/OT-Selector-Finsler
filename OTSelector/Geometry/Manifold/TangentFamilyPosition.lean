import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Geometry.Manifold.TangentFamilyPosition

## Lemma skeleton

* **Conditions:** A jointly C2 tangent lift on the stated parameter×time domain; open parameter domain only in the slice conclusions.

* **Objects:** C2 manifold position, C1 parameter slices and continuous C2 time curves.

* **Proof detail:** Compose the tangent family with the smooth tangent-bundle projection. Compose with fixed-time/fixed-parameter insertions and lower regularity as stated.

## Mathematical sources

- [John M. Lee, Introduction to Smooth Manifolds, second edition (2013)](https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10): Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.

Source relation (adapter): Bundle-projection and slicing calculus. No Finsler equation of motion or additional geometric hypothesis is used.
-/

/-!
# Position regularity of actual tangent families

Joint C2 regularity of the actual total tangent family implies joint C2 regularity
of its manifold position by the bundle projection. On an open parameter set, every
fixed-time parameter slice is C1 and every fixed-parameter time curve is globally C2
and continuous. No Euler--Lagrange equation or additional Finsler hypothesis is needed.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Projection of the actual tangent family gives joint C2 position regularity. -/
theorem contMDiffOn_positionFamily_of_tangentFamily
    {Γ : W → ℝ → M} {D : Set (W × ℝ)}
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D) :
    ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) 2 (fun q ↦ Γ q.1 q.2) D := by
  intro q hq
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hG q hq)).1

/-- Each parameter slice of the actual family is C1 at every interior parameter. -/
theorem contMDiffAt_positionParameter_of_tangentFamily
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (t : ℝ) :
    ContMDiffAt 𝓘(ℝ, W) 𝓘(ℝ, E) 1 (fun b ↦ Γ b t) w := by
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds (show (w, t) ∈ B ×ˢ univ from ⟨hw, mem_univ _⟩))
  exact (hp.comp w ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)).of_le
    (show (1 : ℕ∞ω) ≤ 2 by decide)

/-- Every fixed-parameter time curve is C2 on the entire real line. -/
theorem contMDiff_positionCurve_of_tangentFamily
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 (Γ w) := by
  intro t
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds (show (w, t) ∈ B ×ˢ univ from ⟨hw, mem_univ _⟩))
  exact hp.comp t ((contDiffAt_const.prodMk contDiffAt_id).contMDiffAt)

/-- The same actual time curve is continuous, for compact-time localization. -/
theorem continuous_positionCurve_of_tangentFamily
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) : Continuous (Γ w) :=
  (contMDiff_positionCurve_of_tangentFamily hB hG hw).continuous

end OTSelector.Geometry
