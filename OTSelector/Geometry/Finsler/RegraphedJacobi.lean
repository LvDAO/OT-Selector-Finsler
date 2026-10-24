import OTSelector.Analysis.Calculus.GraphVelocityPhase
import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.GraphLength
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.GraphDynamics
import OTSelector.Geometry.Finsler.GraphEulerLagrange
import OTSelector.Geometry.Finsler.GraphHamiltonianVariation
import OTSelector.Geometry.Finsler.GraphMomentum
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.HamiltonianFamily
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerRegraphedJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerRegraphedJacobi`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.RegraphedJacobi

* **Conditions:** A jointly C2 original Hamiltonian solution family with positive central longitudinal velocity.
* **Objects:** One constructed graph inverse, one genuine graph Legendre branch and actual reduced Jacobi equations on a common open neighborhood.
* **Proof detail:** Construct inverse graph coordinates, retain every varied phase in one graph branch by continuity, use the momentum formula for C2 regularity and differentiate the actual graph equation.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual reduced Jacobi equations after graph reparameterization

One original C2 Hamiltonian solution family constructs a graph inverse and one genuine
graph Legendre branch. A common open neighborhood keeps every actual varied graph
velocity inside that branch. The true graph phase is C2 by the original energy-momentum
formula, so differentiating its actual graph equation yields the reduced Jacobi system.
No reparameterized equation, variational equation or branch-confinement premise is added.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- One original Hamiltonian family constructs local graph coordinates and its actual
reduced Jacobi equations, with the positive coefficient from the true graph Hessian. -/
theorem exists_chartRegraphedJacobi (x₀ : M)
    {ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
      ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))}
    (hℓ : (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀) (hℓi : ContDiffOn ℝ ∞ ℓ.symm ℓ.target)
    {Ψ : W × ℝ → (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hΨ : ContDiffOn ℝ 2 Ψ (B ×ˢ I)) (hmap : MapsTo Ψ (B ×ˢ I) ℓ.target)
    (hODE : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt (fun s ↦ Ψ (w, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ (w, t))) t)
    {z₀ : W × ℝ} (hz₀ : z₀ ∈ B ×ˢ I)
    (hv : 0 < (fderiv ℝ (fun z ↦ (Ψ z).1) z₀ (0, 1)).1) :
    let γ := fun z ↦ (Ψ z).1
    let q₀ := curveGraphCoordinateMap γ z₀
    let L := F.chartGraphLagrangian x₀
    ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
      (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
      (D : Set (W × ℝ)),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      z₀ ∈ e.source ∧ e.source ⊆ B ×ˢ I ∧
      (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ ∧
      ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
      ContDiffOn ℝ 2 (F.chartGraphPhase x₀ γ e) D ∧
      ∀ q ∈ D,
        let P := F.chartGraphPhase x₀ γ e
        let A := GraphHamiltonian.blockA L g q.2 (P q)
        let B' := GraphHamiltonian.blockB L g q.2 (P q)
        let C := GraphHamiltonian.blockC L g q.2 (P q)
        graphVelocityPhase (fun p ↦ (curveGraphPosition γ e p).2) q ∈ g.source ∧
        HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2 ∧
        (∀ ξ : W,
          let Z := fun s ↦ fderiv ℝ (fun w ↦ P (w, s)) q.1 ξ
          HasDerivAt (fun s ↦ (Z s).1) (B' (Z q.2).1 + C (Z q.2).2) q.2 ∧
          HasDerivAt (fun s ↦ (Z s).2) (-A (Z q.2).1 - (Z q.2).2.comp B') q.2) ∧
        (∀ u v, A u v = A v u) ∧
        (∀ p r : V →L[ℝ] ℝ, r (C p) = p (C r)) ∧
        C = ContinuousLinearMap.inverse
          (GraphLegendre.verticalHessian L (g.symm ((q.2, (P q).1), (P q).2))) ∧
        ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (C p) := by
  let γ := fun z ↦ (Ψ z).1
  let q₀ := curveGraphCoordinateMap γ z₀
  let L := F.chartGraphLagrangian x₀
  obtain ⟨hγ, hphase, hEL⟩ :=
    F.chartHamiltonianFamily_positionProperties x₀ hℓ hsub hI hΨ hmap hODE
  obtain ⟨e, he, hzs, hqt, hesub, _, _, hi, hΓ, hsign, _⟩ :=
    exists_curveGraphCoordinates (hγ.contDiffAt ((hB.prod hI).mem_nhds hz₀))
      hv.ne' (hB.prod hI) hz₀
  have hpos (p : W × ℝ) (hp : p ∈ e.source) :
      0 < (fderiv ℝ γ p (0, 1)).1 := pos_of_mul_pos_left (hsign p hp).2 hv.le
  let y := fun q ↦ (curveGraphPosition γ e q).2
  let P := F.chartGraphPhase x₀ γ e
  have hPC2 : ContDiffOn ℝ 2 P e.target :=
    hF.contDiffOn_chartGraphPhase x₀ hℓ hsub hℓi (hB.prod hI) hΨ hmap
      (fun p hp ↦ hODE p.1 hp.1 p.2 hp.2) he hesub hi hpos
  have hbase : (graphVelocityPhase y q₀).1 ∈
      (extChartAt 𝓘(ℝ, ℝ × V) x₀).target := by
    have hp := hesub (e.map_target hqt)
    have hb := (hphase _ hp.1 _ hp.2).1
    have heq : (graphVelocityPhase y q₀).1 = γ (e.symm q₀) :=
      Prod.ext (curveGraph_inverse_components he hqt).2.symm rfl
    rwa [heq]
  obtain ⟨g, hg, hgs, _, hgsub, _, hgi, _, _⟩ :=
    hF.exists_smooth_chartGraphLegendre_local_inverse x₀ hbase
  let D := e.target ∩ (graphVelocityPhase y) ⁻¹' g.source
  obtain ⟨hD, hqD, hDsub, hsource⟩ :=
    graphVelocityPhase_source_neighborhood e.open_target hΓ.snd g.open_source hqt hgs
  have hgraphODE (q : W × ℝ) (hq : q ∈ D) :
      HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2 := by
    exact hF.chartGraph_phase_of_energy_family x₀ hB hI hconn hγ hphase hEL
      he hesub hi hpos hg (hDsub hq) (hsource hq)
  have hpt (q : W × ℝ) (hq : q ∈ D) : ((q.2, (P q).1), (P q).2) ∈ g.target := by
    have h := g.map_source (hsource hq)
    rw [hg] at h
    exact h
  refine ⟨e, g, D, he, hzs, hesub, hg, hgsub, hgi, hD, hqD, hDsub,
    hPC2.mono hDsub, ?_⟩
  intro q hq
  have hcoeff := hF.chartGraphDynamics_blocks x₀ hg hgsub hgi (hpt q hq)
  refine ⟨hsource hq, hgraphODE q hq, ?_, hcoeff.2.1, hcoeff.2.2.1,
    hcoeff.2.2.2.1, hcoeff.2.2.2.2.1⟩
  intro ξ
  exact hasDerivAt_graphHamiltonian_parameterVariation hg
    ((hF.contDiffOn_chartGraphLength x₀).mono hgsub) hgi hD
    (hPC2.mono hDsub) hgraphODE hq (hpt q hq) ξ

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
