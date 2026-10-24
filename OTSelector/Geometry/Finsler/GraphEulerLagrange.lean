import OTSelector.Analysis.Calculus.Variational.EulerLagrangeReparam
import OTSelector.Analysis.Calculus.Variational.GraphEulerLagrange
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthReparam
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphTime
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerGraphEulerLagrange.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerGraphEulerLagrange`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.GraphEulerLagrange

* **Conditions:** A jointly C2 actual energy Euler–Lagrange family, its genuine graph inverse and positive longitudinal velocity.
* **Objects:** The graph Euler–Lagrange equation and its phase lift solving any genuine graph Legendre branch containing that phase.
* **Proof detail:** Derive the positive inverse-time derivative, reparameterize the length equation and project its actual spatial component, retaining the same graph inverse and branch.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual Finsler energy curves in the same graph coordinates

An actual C2 energy Euler--Lagrange family is reparameterized by its own local graph
inverse. Positive longitudinal velocity gives a positive actual recovered-time derivative.
Original energy equations therefore imply length equations, whose actual spatial projection
is the graph Euler--Lagrange equation. Its momentum lift solves the field of any genuine
partial Legendre branch containing the same graph phase.

The graph inverse and the Legendre branch are retained throughout. Neither a length
nor a graph Euler--Lagrange equation is supplied as a premise. This is a local family
adapter, with ordinary curve equations and genuine inverse identities as inputs.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The same actual graph inverse converts an original energy solution family to graph EL. -/
theorem chartGraph_eulerLagrange_of_energy_family (x₀ : M)
    {γ : W × ℝ → ℝ × V} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hγ : ContDiffOn ℝ 2 γ (B ×ˢ I))
    (hphase : ∀ w ∈ B, ∀ t ∈ I,
      (γ (w, t), deriv (fun u ↦ γ (w, u)) t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀)
        (γ (w, s), deriv (fun u ↦ γ (w, u)) s))
      (baseEnergyDifferential (F.chartEnergy x₀)
        (γ (w, t), deriv (fun u ↦ γ (w, u)) t)) t)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    (hsub : e.source ⊆ B ×ˢ I) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hpos : ∀ p ∈ e.source, 0 < (fderiv ℝ γ p (0, 1)).1) :
    ∀ q ∈ e.target,
      let y := fun s ↦ (curveGraphPosition γ e (q.1, s)).2
      DifferentiableAt ℝ y q.2 ∧
      HasDerivAt (fun s ↦ fiberLegendre (F.chartGraphLagrangian x₀) ((s, y s), deriv y s))
        (GraphHamiltonian.positionDifferential (F.chartGraphLagrangian x₀)
          ((q.2, y q.2), deriv y q.2)) q.2 := by
  intro q hq
  let w := q.1
  let J : Set ℝ := {s | (w, s) ∈ e.target}
  let τ : ℝ → ℝ := fun s ↦ (e.symm (w, s)).2
  let x : ℝ → ℝ × V := fun t ↦ γ (w, t)
  let y : ℝ → V := fun s ↦ (curveGraphPosition γ e (w, s)).2
  have hJ : IsOpen J := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hqJ : q.2 ∈ J := hq
  have hw : w ∈ B := by
    have h := (hsub (e.map_target hq)).1
    rwa [(curveGraph_inverse_components he hq).1] at h
  have hτI (s : ℝ) (hs : s ∈ J) : τ s ∈ I := (hsub (e.map_target hs)).2
  have hx : ContDiffOn ℝ 2 x I :=
    hγ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht ↦ ⟨hw, ht⟩)
  have hΓ : ContDiffOn ℝ 2 (curveGraphPosition γ e) e.target :=
    hγ.comp hi (fun _ ht ↦ hsub (e.map_target ht))
  have hy (s : ℝ) (hs : s ∈ J) : DifferentiableAt ℝ y s := by
    have hg := (hΓ.contDiffAt (e.open_target.mem_nhds hs)).differentiableAt (by norm_num)
    have hj : DifferentiableAt ℝ (fun u : ℝ ↦ (w, u)) s :=
      (differentiableAt_const w).prodMk differentiableAt_id
    exact (hg.comp s hj).snd
  have hτreg (s : ℝ) (hs : s ∈ J) : DifferentiableAt ℝ τ s ∧ 0 < deriv τ s := by
    have hi' := (hi.contDiffAt (e.open_target.mem_nhds hs)).differentiableAt (by norm_num)
    have hg := (hγ.contDiffAt ((hB.prod hI).mem_nhds
      (hsub (e.map_target hs)))).differentiableAt (by norm_num)
    have hp := hpos _ (e.map_target hs)
    have hd := curveGraphTime_hasDerivAt he hs hg hi' hp.ne'
    exact ⟨hd.differentiableAt, hd.deriv.symm ▸ inv_pos.mpr hp⟩
  have heq (s : ℝ) (hs : s ∈ J) : (x ∘ τ) s = (s, y s) := by
    calc
      (x ∘ τ) s = curveGraphPosition γ e (w, s) :=
        (curveGraphPosition_eq_slice he hs).symm
      _ = (s, y s) := Prod.ext (curveGraph_inverse_components he hs).2 rfl
  have hL (s : ℝ) (hs : s ∈ J) :
      DifferentiableAt ℝ (fun z ↦ (F.chartLength x₀ z : ℝ))
        ((s, y s), (1, deriv y s)) := by
    have hb := (hphase w hw (τ s) (hτI s hs)).1
    have hb' : (s, y s) ∈ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target := by
      rwa [← heq s hs]
    have hp : ((s, y s), (1, deriv y s)) ∈ chartEnergyDomain x₀ := by
      refine ⟨hb', ?_⟩
      intro hzero
      have h := congrArg Prod.fst hzero
      norm_num at h
    exact ((hF.contDiffOn_chartLength x₀).contDiffAt
      ((isOpen_chartEnergyDomain x₀).mem_nhds hp)).differentiableAt (by simp)
  have hlength (s : ℝ) (hs : s ∈ J) : HasDerivAt
      (fun u ↦ fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
        ((u, y u), deriv (fun r ↦ (r, y r)) u))
      (baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ))
        ((s, y s), deriv (fun r ↦ (r, y r)) s)) s := by
    have hr := hF.chartLength_eulerLagrange_reparam x₀ hI hconn hx
      (hphase w hw) (hEL w hw) (τ := τ) (t := s) (by
        filter_upwards [hJ.mem_nhds hs] with u hu
        exact ⟨(hτreg u hu).1, (hτreg u hu).2, hτI u hu⟩)
    apply hasDerivAt_eulerLagrange_congr _ hr
    filter_upwards [hJ.mem_nhds hs] with u hu
    exact heq u hu
  exact ⟨hy q.2 hqJ, eulerLagrange_graphRestriction hJ hy hL hlength q.2 hqJ⟩

/-- The derived graph momentum lift solves the field of the same genuine Legendre branch. -/
theorem chartGraph_phase_of_energy_family (x₀ : M)
    {γ : W × ℝ → ℝ × V} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hγ : ContDiffOn ℝ 2 γ (B ×ˢ I))
    (hphase : ∀ w ∈ B, ∀ t ∈ I,
      (γ (w, t), deriv (fun u ↦ γ (w, u)) t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀)
        (γ (w, s), deriv (fun u ↦ γ (w, u)) s))
      (baseEnergyDifferential (F.chartEnergy x₀)
        (γ (w, t), deriv (fun u ↦ γ (w, u)) t)) t)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    (hsub : e.source ⊆ B ×ˢ I) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hpos : ∀ p ∈ e.source, 0 < (fderiv ℝ γ p (0, 1)).1)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.chartGraphLagrangian x₀))
    {q : W × ℝ} (hq : q ∈ e.target)
    (hstate : ((q.2, (curveGraphPosition γ e q).2),
      deriv (fun s ↦ (curveGraphPosition γ e (q.1, s)).2) q.2) ∈ g.source) :
    let y := fun s ↦ (curveGraphPosition γ e (q.1, s)).2
    let p := fun s ↦ (y s, fiberLegendre (F.chartGraphLagrangian x₀) ((s, y s), deriv y s))
    HasDerivAt p (GraphHamiltonian.field (F.chartGraphLagrangian x₀) g q.2 (p q.2)) q.2 := by
  obtain ⟨hy, hgraph⟩ := hF.chartGraph_eulerLagrange_of_energy_family
    x₀ hB hI hconn hγ hphase hEL he hsub hi hpos q hq
  exact GraphHamiltonian.hasDerivAt_phase_of_graphEulerLagrange hg hy hgraph hstate

/-- A positive central longitudinal velocity constructs the same graph inverse and its true EL. -/
theorem exists_chartGraph_eulerLagrange_of_energy_family [FiniteDimensional ℝ W] (x₀ : M)
    {γ : W × ℝ → ℝ × V} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hγ : ContDiffOn ℝ 2 γ (B ×ˢ I))
    (hphase : ∀ w ∈ B, ∀ t ∈ I,
      (γ (w, t), deriv (fun u ↦ γ (w, u)) t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀)
        (γ (w, s), deriv (fun u ↦ γ (w, u)) s))
      (baseEnergyDifferential (F.chartEnergy x₀)
        (γ (w, t), deriv (fun u ↦ γ (w, u)) t)) t)
    {z : W × ℝ} (hz : z ∈ B ×ˢ I) (hv : 0 < (fderiv ℝ γ z (0, 1)).1) :
    ∃ e : OpenPartialHomeomorph (W × ℝ) (W × ℝ),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      z ∈ e.source ∧ curveGraphCoordinateMap γ z ∈ e.target ∧
      e.source ⊆ B ×ˢ I ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      ContDiffOn ℝ 2 (curveGraphPosition γ e) e.target ∧
      (∀ p ∈ e.source, 0 < (fderiv ℝ γ p (0, 1)).1) ∧
      ∀ q ∈ e.target,
        let y := fun s ↦ (curveGraphPosition γ e (q.1, s)).2
        DifferentiableAt ℝ y q.2 ∧
        HasDerivAt (fun s ↦ fiberLegendre (F.chartGraphLagrangian x₀)
          ((s, y s), deriv y s))
          (GraphHamiltonian.positionDifferential (F.chartGraphLagrangian x₀)
            ((q.2, y q.2), deriv y q.2)) q.2 := by
  obtain ⟨e, he, hzs, hzt, hsub, _, _, hi, hΓ, hsign, _⟩ :=
    exists_curveGraphCoordinates (hγ.contDiffAt ((hB.prod hI).mem_nhds hz))
      hv.ne' (hB.prod hI) hz
  have hpos (p : W × ℝ) (hp : p ∈ e.source) : 0 < (fderiv ℝ γ p (0, 1)).1 :=
    pos_of_mul_pos_left (hsign p hp).2 hv.le
  exact ⟨e, he, hzs, hzt, hsub, hi, hΓ, hpos,
    hF.chartGraph_eulerLagrange_of_energy_family x₀ hB hI hconn hγ hphase hEL he hsub hi hpos⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
