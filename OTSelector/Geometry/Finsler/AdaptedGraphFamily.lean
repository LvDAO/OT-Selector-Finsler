import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.AdaptedGraphLagrangian
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphTime

/-!
# Geometry.Finsler.AdaptedGraphFamily

* **Conditions:** An original C2 energy solution family and its genuine adapted graph inverse and Legendre branch.
* **Objects:** Actual adapted graph Euler–Lagrange and Hamiltonian phase equations, plus their germ-local congruence helper.
* **Proof detail:** Use the positive inverse clock to reparameterize original length equations, project the spatial component and identify momentum through the same branch.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedGraphFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedGraphFamily`; the selected original proof blocks follow. -/
section

/-!
# Original Finsler energy families in the same adapted graph coordinates

The inverse of the actual adapted family clock supplies a positive time change.
Original energy Euler--Lagrange therefore implies the true adapted graph equation,
and the same graph Legendre branch gives the corresponding phase equation.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

/-- Locally equal spatial curves have the same actual graph Euler--Lagrange equation. -/
theorem hasDerivAt_graphEulerLagrange_congr
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : (ℝ × V) × V → ℝ} {x y : ℝ → V} {t : ℝ} (hxy : x =ᶠ[𝓝 t] y)
    (hEL : HasDerivAt (fun s ↦ fiberLegendre L ((s, x s), deriv x s))
      (GraphHamiltonian.positionDifferential L ((t, x t), deriv x t)) t) :
    HasDerivAt (fun s ↦ fiberLegendre L ((s, y s), deriv y s))
      (GraphHamiltonian.positionDifferential L ((t, y t), deriv y t)) t := by
  rw [← hxy.eq_of_nhds, ← hxy.deriv_eq]
  apply hEL.congr_of_eventuallyEq
  filter_upwards [hxy, hxy.deriv] with s hs hds
  rw [hs, hds]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The same adapted graph inverse converts an original energy family to actual graph EL. -/
theorem adaptedGraph_eulerLagrange_of_energy_family (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {γ : W × ℝ → E} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hγ : ContDiffOn ℝ 2 γ (B ×ˢ I))
    (hphase : ∀ w ∈ B, ∀ t ∈ I,
      (γ (w, t), deriv (fun u ↦ γ (w, u)) t) ∈ chartEnergyDomain old)
    (hEL : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy old)
        (γ (w, s), deriv (fun u ↦ γ (w, u)) s))
      (baseEnergyDifferential (F.chartEnergy old)
        (γ (w, t), deriv (fun u ↦ γ (w, u)) t)) t)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ A (γ z)))
    (hsub : e.source ⊆ B ×ˢ I) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hpos : ∀ p ∈ e.source, 0 < (fderiv ℝ (fun z ↦ A (γ z)) p (0, 1)).1) :
    ∀ q ∈ e.target,
      let y := fun s ↦ (curveGraphPosition (fun z ↦ A (γ z)) e (q.1, s)).2
      DifferentiableAt ℝ y q.2 ∧ HasDerivAt
        (fun s ↦ fiberLegendre (F.adaptedGraphLagrangian old A) ((s, y s), deriv y s))
        (GraphHamiltonian.positionDifferential (F.adaptedGraphLagrangian old A)
          ((q.2, y q.2), deriv y q.2)) q.2 := by
  intro q hq
  let γA := fun z ↦ A (γ z)
  let w := q.1
  let J : Set ℝ := {s | (w, s) ∈ e.target}
  let τ : ℝ → ℝ := fun s ↦ (e.symm (w, s)).2
  let x : ℝ → E := fun t ↦ γ (w, t)
  let y : ℝ → V := fun s ↦ (curveGraphPosition γA e (w, s)).2
  have hJ : IsOpen J := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hqJ : q.2 ∈ J := hq
  have hw : w ∈ B := by
    have h := (hsub (e.map_target hq)).1
    rwa [(curveGraph_inverse_components he hq).1] at h
  have hτI : MapsTo τ J I := fun _ hs ↦ (hsub (e.map_target hs)).2
  have hx : ContDiffOn ℝ 2 x I :=
    hγ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht ↦ ⟨hw, ht⟩)
  have hγA : ContDiffOn ℝ 2 γA (B ×ˢ I) := A.contDiff.comp_contDiffOn hγ
  have hΓ : ContDiffOn ℝ 2 (curveGraphPosition γA e) e.target :=
    hγA.comp hi (fun _ ht ↦ hsub (e.map_target ht))
  have hy : DifferentiableAt ℝ y q.2 := by
    have hg := (hΓ.contDiffAt (e.open_target.mem_nhds hq)).differentiableAt (by norm_num)
    have hj : DifferentiableAt ℝ (fun u : ℝ ↦ (w, u)) q.2 :=
      (differentiableAt_const w).prodMk differentiableAt_id
    exact (hg.comp q.2 hj).snd
  have hτ : ContDiffOn ℝ 2 τ J :=
    hi.snd.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hs ↦ hs)
  have hτpos (s : ℝ) (hs : s ∈ J) : 0 < deriv τ s := by
    have hi' := (hi.contDiffAt (e.open_target.mem_nhds hs)).differentiableAt (by norm_num)
    have hg := (hγA.contDiffAt ((hB.prod hI).mem_nhds
      (hsub (e.map_target hs)))).differentiableAt (by norm_num)
    have hp := hpos _ (e.map_target hs)
    have hd := curveGraphTime_hasDerivAt he hs hg hi' hp.ne'
    exact hd.deriv.symm ▸ inv_pos.mpr hp
  have hsame (s : ℝ) (hs : s ∈ J) : A (x (τ s)) = curveGraphPosition γA e (w, s) :=
    (curveGraphPosition_eq_slice he hs).symm
  have hclock (s : ℝ) (hs : s ∈ J) : (A (x (τ s))).1 = s :=
    (congrArg Prod.fst (hsame s hs)).trans (curveGraph_inverse_components he hs).2
  have heq : (fun s ↦ (A (x (τ s))).2) =ᶠ[𝓝 q.2] y := by
    filter_upwards [hJ.mem_nhds hqJ] with s hs
    exact congrArg Prod.snd (hsame s hs)
  refine ⟨hy, hasDerivAt_graphEulerLagrange_congr heq ?_⟩
  exact hF.adaptedGraph_eulerLagrange_reparam old A hI hconn hx (hphase w hw)
    (hEL w hw) hJ hτ hτI hτpos hclock q.2 hqJ

/-- The derived actual graph phase solves the field of the same graph Legendre branch. -/
theorem adaptedGraph_phase_of_energy_family (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {γ : W × ℝ → E} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hγ : ContDiffOn ℝ 2 γ (B ×ˢ I))
    (hphase : ∀ w ∈ B, ∀ t ∈ I,
      (γ (w, t), deriv (fun u ↦ γ (w, u)) t) ∈ chartEnergyDomain old)
    (hEL : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy old)
        (γ (w, s), deriv (fun u ↦ γ (w, u)) s))
      (baseEnergyDifferential (F.chartEnergy old)
        (γ (w, t), deriv (fun u ↦ γ (w, u)) t)) t)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ A (γ z)))
    (hsub : e.source ⊆ B ×ˢ I) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hpos : ∀ p ∈ e.source, 0 < (fderiv ℝ (fun z ↦ A (γ z)) p (0, 1)).1)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old A))
    {q : W × ℝ} (hq : q ∈ e.target)
    (hstate : ((q.2, (curveGraphPosition (fun z ↦ A (γ z)) e q).2),
      deriv (fun s ↦ (curveGraphPosition (fun z ↦ A (γ z)) e (q.1, s)).2) q.2) ∈
        g.source) :
    let y := fun s ↦ (curveGraphPosition (fun z ↦ A (γ z)) e (q.1, s)).2
    let p := fun s ↦
      (y s, fiberLegendre (F.adaptedGraphLagrangian old A) ((s, y s), deriv y s))
    HasDerivAt p
      (GraphHamiltonian.field (F.adaptedGraphLagrangian old A) g q.2 (p q.2)) q.2 := by
  obtain ⟨hy, hgraph⟩ := hF.adaptedGraph_eulerLagrange_of_energy_family
    old A hB hI hconn hγ hphase hEL he hsub hi hpos q hq
  exact GraphHamiltonian.hasDerivAt_phase_of_graphEulerLagrange hg hy hgraph hstate

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
