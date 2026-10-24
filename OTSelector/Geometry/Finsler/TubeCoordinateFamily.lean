import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.TubeCoordinateEnergy

/-!
# Geometry.Finsler.TubeCoordinateFamily

* **Conditions:** A genuine smooth tube/inverse and the actual C2 original tangent family lying in its target on the stated domain.
* **Objects:** Actual inverse-tube position–velocity and original pulled-back momentum families with proved joint C2 regularity and slit membership.
* **Proof detail:** Apply the genuine inverse tangent map, read its true derivative and compose with the tube energy Legendre map.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateFamily`; the selected original proof blocks follow. -/
section

/-!
# Actual position-velocity and momentum families in a genuine tube

The actual inverse tube tangent map reads the same original family's coordinate
velocity. Smoothness of this tangent map transfers joint regularity to the real
position-velocity family, and the original pulled-back Legendre map supplies its
actual coordinate momentum. No velocity identity or momentum regularity is assumed.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E V W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Position and actual time derivative of the given family in the true inverse tube. -/
def tubeCoordinateTangentFamily (Y : OpenPartialHomeomorph V M)
    (Γ : W → ℝ → M) (q : W × ℝ) : V × V :=
  ((Y.symm ∘ Γ q.1) q.2, deriv (Y.symm ∘ Γ q.1) q.2)

/-- The actual energy momentum of the same coordinate family. -/
def tubeCoordinateMomentumFamily (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (Γ : W → ℝ → M) (q : W × ℝ) : V × (V →L[ℝ] ℝ) :=
  parametricLegendre (F.tubeCoordinateEnergy Y) (tubeCoordinateTangentFamily Y Γ q)

/-- The true coordinate velocity is read by the actual inverse tangent map. -/
theorem tubeCoordinateTangentFamily_eq {Y : OpenPartialHomeomorph V M}
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {D : Set (W × ℝ)} (hD : IsOpen D)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D)
    {q : W × ℝ} (hq : q ∈ D) (hx : Γ q.1 q.2 ∈ Y.target) :
    tubeCoordinateTangentFamily Y Γ q =
      (Y.symm (Γ q.1 q.2), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, V) Y.symm (Γ q.1 q.2)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) q.2 1)) := by
  have hp : ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) 2 (fun r ↦ Γ r.1 r.2) D :=
    fun r hr ↦ (Bundle.contMDiffWithinAt_totalSpace.mp (hG r hr)).1
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) q.2 :=
    ((hp.contMDiffAt (hD.mem_nhds hq)).comp q.2
      ((contDiffAt_const.prodMk contDiffAt_id).contMDiffAt)).mdifferentiableAt (by norm_num)
  have hy := (hi.contMDiffAt (Y.open_target.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp q.2 hy hc
  unfold tubeCoordinateTangentFamily
  refine Prod.ext ?_ ?_
  · rfl
  · change deriv (Y.symm ∘ Γ q.1) q.2 = _
    rw [deriv, ← mfderiv_eq_fderiv, hd]
    rfl

/-- Joint C2 actual tangents give joint C2 position and actual velocity after the
same genuine inverse tube map; the derivative identity is derived internally. -/
theorem contDiffOn_tubeCoordinateTangentFamily {Y : OpenPartialHomeomorph V M}
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {D : Set (W × ℝ)} (hD : IsOpen D)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D)
    (hmap : ∀ q ∈ D, Γ q.1 q.2 ∈ Y.target) :
    ContDiffOn ℝ 2 (tubeCoordinateTangentFamily Y Γ) D := by
  have ht := hi.contMDiffOn_tangentMapWithin (m := 2) (by simp)
    Y.open_target.uniqueMDiffOn
  have hcomp := ht.comp hG (fun q hq ↦ hmap q hq)
  have hout := (contMDiff_tangentBundleModelSpaceHomeomorph
    (I := 𝓘(ℝ, V)) (n := 2)).comp_contMDiffOn hcomp
  have hread : ContDiffOn ℝ 2 (fun q : W × ℝ ↦
      (Y.symm (Γ q.1 q.2), mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, V) Y.symm Y.target
        (Γ q.1 q.2) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) q.2 1))) D := by
    have hh : ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, V × V) 2
        (fun q : W × ℝ ↦
          (Y.symm (Γ q.1 q.2), mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, V) Y.symm Y.target
            (Γ q.1 q.2) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) q.2 1))) D := by
      simpa only [← modelWithCornersSelf_prod, Function.comp_def] using! hout
    exact hh.contDiffOn
  apply hread.congr
  intro q hq
  rw [tubeCoordinateTangentFamily_eq hi hD hG hq (hmap q hq),
    mfderivWithin_of_mem_nhds (Y.open_target.mem_nhds (hmap q hq))]

variable {F : ContinuousFinslerNorm E M}

/-- Nonzero original Euler--Lagrange velocity remains nonzero in genuine tube coordinates. -/
theorem tubeCoordinateTangentFamily_mem_domain
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {D : Set (W × ℝ)} (hD : IsOpen D)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D)
    {q : W × ℝ} (hq : q ∈ D) (hx : Γ q.1 q.2 ∈ Y.target)
    (hEL : F.IsEulerLagrangeAt (Γ q.1) q.2) :
    tubeCoordinateTangentFamily Y Γ q ∈ Y.source ×ˢ {v : V | v ≠ 0} := by
  rw [tubeCoordinateTangentFamily_eq hi hD hG hq hx]
  refine ⟨Y.map_target hx, ?_⟩
  have hd : Y.MDifferentiable 𝓘(ℝ, V) 𝓘(ℝ, E) :=
    ⟨hY.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩
  have hvel : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) q.2 1 ≠ 0 := by
    intro he
    have hp := F.speed_pos_of_isEulerLagrangeAt hEL
    change 0 < F.toFun ⟨Γ q.1 q.2, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) q.2 1⟩ at hp
    rw [he, F.map_zero] at hp
    exact lt_irrefl _ hp
  intro he
  exact hvel ((hd.symm.mfderiv_injective hx) (he.trans (_root_.map_zero _).symm))

namespace IsSmoothStronglyConvex

/-- The same actual family's energy momentum is jointly C2 in genuine tube coordinates.
The original energy, its true Legendre derivative, and inverse tangent identity supply it. -/
theorem contDiffOn_tubeCoordinateMomentumFamily (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {D : Set (W × ℝ)} (hD : IsOpen D)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D)
    (hmap : ∀ q ∈ D, Γ q.1 q.2 ∈ Y.target)
    (hEL : ∀ q ∈ D, F.IsEulerLagrangeAt (Γ q.1) q.2) :
    ContDiffOn ℝ 2 (F.tubeCoordinateMomentumFamily Y Γ) D := by
  have hP := contDiffOn_tubeCoordinateTangentFamily hi hD hG hmap
  have hL : ContDiffOn ℝ 2 (parametricLegendre (F.tubeCoordinateEnergy Y))
      (Y.source ×ˢ {v : V | v ≠ 0}) := by
    intro z hz
    exact ((contDiffAt_parametricLegendre
      ((hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
        ((Y.open_source.prod isOpen_ne).mem_nhds hz))).of_le (by simp)).contDiffWithinAt
  exact hL.comp hP (fun q hq ↦
    tubeCoordinateTangentFamily_mem_domain hY hi hD hG hq (hmap q hq) (hEL q hq))

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
