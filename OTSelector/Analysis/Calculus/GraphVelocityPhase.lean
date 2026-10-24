import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.GraphVelocityPhase.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.GraphVelocityPhase`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C2 position family is defined on the stated open parameter/time domain.

Objects: Its actual time-velocity phase family is C1, with explicit open source neighborhoods.

Proof detail: Differentiate evaluation in the time direction, pair position and velocity, and take the open preimage of the requested phase domain.

Sources: Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60).
Relation: Elementary actual-velocity regularity and domain-control corollary.
-/

/-!
# The actual velocity phase of a graph family

A jointly C2 position family has a jointly C1 velocity phase formed with its actual
ordinary time derivative. The derivative is identified with evaluation of the joint
Fréchet differential. Continuity then gives an explicit open neighborhood whose entire
velocity phase stays in any prescribed open domain containing the central phase.
-/

open Set
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The base position and actual time velocity of a parameterized graph family. -/
def graphVelocityPhase (y : W × ℝ → V) (q : W × ℝ) : (ℝ × V) × V :=
  ((q.2, y q), deriv (fun s ↦ y (q.1, s)) q.2)

/-- The velocity component is evaluation of the actual joint differential. -/
theorem graphVelocityPhase_eq_fderiv {y : W × ℝ → V} {q : W × ℝ}
    (hy : DifferentiableAt ℝ y q) :
    graphVelocityPhase y q = ((q.2, y q), fderiv ℝ y q (0, 1)) := by
  have hd := (hy.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))).deriv
  exact congrArg (fun v ↦ ((q.2, y q), v)) hd

/-- A C2 graph family has a C1 actual velocity phase on its open domain. -/
theorem contDiffOn_graphVelocityPhase {y : W × ℝ → V} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hy : ContDiffOn ℝ 2 y D) :
    ContDiffOn ℝ 1 (graphVelocityPhase y) D := by
  have hd := (hy.fderiv_of_isOpen hD (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
    (contDiffOn_const (c := ((0 : W), (1 : ℝ))))
  have h := (contDiffOn_snd.prodMk (hy.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))).prodMk hd
  apply h.congr
  intro q hq
  exact graphVelocityPhase_eq_fderiv
    ((hy.contDiffAt (hD.mem_nhds hq)).differentiableAt (by norm_num))

/-- Intersecting with the inverse image of an open velocity domain gives an actual
open neighborhood of the central parameter on which every velocity phase stays in it. -/
theorem graphVelocityPhase_source_neighborhood {y : W × ℝ → V} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hy : ContDiffOn ℝ 2 y D) {U : Set ((ℝ × V) × V)}
    (hU : IsOpen U) {q₀ : W × ℝ} (hq : q₀ ∈ D) (hp : graphVelocityPhase y q₀ ∈ U) :
    let D' := D ∩ graphVelocityPhase y ⁻¹' U
    IsOpen D' ∧ q₀ ∈ D' ∧ D' ⊆ D ∧ MapsTo (graphVelocityPhase y) D' U := by
  exact ⟨(contDiffOn_graphVelocityPhase hD hy).continuousOn.isOpen_inter_preimage hD hU,
    ⟨hq, hp⟩, inter_subset_left, fun _ hz ↦ hz.2⟩

end OTSelector.Geometry

end
end
