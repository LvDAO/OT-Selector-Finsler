import OTSelector.Analysis.Calculus.GraphVelocityPhase
import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Analysis.ODE.Hamiltonian.GraphJacobiMatrix
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.GraphMomentum
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.PotentialGraphStructure
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.SmoothLevelModel
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialLevelGraph.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialLevelGraph`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PotentialLevelGraph

* **Conditions:** A smooth potential with actual central momentum matching and positive longitudinal velocity in an R×V chart.
* **Objects:** An automatically constructed V-dimensional level chart, square graph Jacobi matrices, positive inverse block, zero Wronskian and trivial joint position/momentum kernel.
* **Proof detail:** Use nonzero differential to construct the level chart, apply the normalized graph family, and express its rank/pairing and true variational blocks in a finite basis.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): Parameter dimension and level immersion are conclusions; no auxiliary q-by-q reduced system is assumed.
-/

/-!
# Actual regular potential levels produce dimension-matched Finsler graph families

A smooth potential with the prescribed actual initial momentum determines its own
local level chart. Its parameter space is the spatial model V, so the true graph
parameter derivative has d-1 input and position dimensions. The original normalized
family, branches, Jacobi equations and local central rank/pairing are retained.
The canonical finite basis gives actual square Jacobi matrices, positive inverse
block, zero Wronskian and trivial joint position/momentum kernel.
Only smooth potential and central momentum matching remain auxiliary inputs; no
level-set immersion, parameter dimension or level chart is assumed.
-/

open Set Filter Metric Manifold Matrix
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- A regular smooth potential constructs the genuine d-1-dimensional level chart
and the same true Finsler graph family, including its actual square Jacobi matrices. -/
theorem exists_potentialLevel_graphStructure (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {f : (ℝ × V) → ℝ} {Ω : Set (ℝ × V)} {y₀ v₀ : ℝ × V}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hy₀ : y₀ ∈ Ω)
    (hz : (y₀, v₀) ∈ chartEnergyDomain x₀)
    (hmatch : fderiv ℝ f y₀ = fiberLegendre (F.chartEnergy x₀) (y₀, v₀))
    (hpositive : 0 < v₀.1) (t₀ : ℝ) :
    ∃ (σ : V → ℝ × V) (B₀ : Set V) (U : Set (ℝ × V)),
      IsOpen B₀ ∧ (0 : V) ∈ B₀ ∧ IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ σ B₀ ∧ σ 0 = y₀ ∧ MapsTo σ B₀ Ω ∧
      (∀ w ∈ B₀, f (σ w) = f y₀) ∧ Function.Injective (fderiv ℝ σ 0) ∧
      InjOn σ B₀ ∧ σ '' B₀ = U ∩ {x | f x = f y₀} ∧
      let L₀ := F.chartEnergy x₀
      let z₀ := (σ (0 : V), v₀)
      let p₀ := parametricLegendre L₀ z₀
      ∃ (ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
          ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)))
        (B : Set V) (v : V → ℝ × V) (a : V → ℝ) (r : ℝ≥0) (T : ℝ)
        (Φ : ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) × ℝ →
          (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)),
        let seed := potentialConormalState f σ a
        let Ψ := fun q : V × ℝ ↦ Φ (seed q.1, q.2)
        let γ := fun q ↦ (Ψ q).1
        let Z₀ := fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) (0 : V)
        let q₀ := curveGraphCoordinateMap γ ((0 : V), t₀)
        let L := F.chartGraphLagrangian x₀
        (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
          parametricLegendre L₀ ∧
        z₀ ∈ ℓ.source ∧ ℓ.source ⊆ chartEnergyDomain x₀ ∧
        ContDiffOn ℝ ∞ ℓ.symm ℓ.target ∧ IsOpen B ∧ (0 : V) ∈ B ∧ B ⊆ B₀ ∧
        ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧ v (0 : V) = v₀ ∧ a (0 : V) = 1 ∧
        ContDiffOn ℝ ∞ seed B ∧ seed (0 : V) = p₀ ∧
        (∀ w ∈ B, (σ w, v w) ∈ ℓ.source ∧ 0 < a w ∧
          L₀ (σ w, v w) = L₀ z₀ ∧
          fiberLegendre L₀ (σ w, v w) = a w • fderiv ℝ f (σ w) ∧
          ℓ.symm (seed w) = (σ w, v w) ∧ seed w ∈ closedBall p₀ r) ∧
        0 < r ∧ 0 < T ∧
        LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L₀ ℓ)
          t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
        MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) ℓ.target ∧
        ContDiffOn ℝ 2 Ψ (B ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
        Z₀ t₀ = fderiv ℝ seed (0 : V) ∧
        (∀ t ∈ Icc (t₀ - T) (t₀ + T),
          DifferentiableAt ℝ (fun w ↦ Ψ (w, t)) (0 : V) ∧ Function.Injective (Z₀ t) ∧
          (∀ u w : V, canonicalPhasePairing (Z₀ t u) (Z₀ t w) = 0) ∧
          (∀ u : V, HasDerivWithinAt (fun s ↦ Z₀ s u)
            (fderiv ℝ (localHamiltonianVectorField L₀ ℓ) (Φ (p₀, t)) (Z₀ t u))
            (Icc (t₀ - T) (t₀ + T)) t) ∧
          ∀ u : V, (Z₀ t u).1 ∈ (fiberLegendre L₀ (ℓ.symm (Φ (p₀, t)))).ker) ∧
        ∃ (e : OpenPartialHomeomorph (V × ℝ) (V × ℝ))
          (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
          (D : Set (V × ℝ)),
          (e : V × ℝ → V × ℝ) = curveGraphCoordinateMap γ ∧
          ((0 : V), t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ Ioo (t₀ - T) (t₀ + T) ∧
          (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
          g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ ∧
          ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
          ContDiffOn ℝ 2 (F.chartGraphPhase x₀ γ e) D ∧
          (∀ q ∈ D,
            let P := F.chartGraphPhase x₀ γ e
            let A := GraphHamiltonian.blockA L g q.2 (P q)
            let B' := GraphHamiltonian.blockB L g q.2 (P q)
            let C := GraphHamiltonian.blockC L g q.2 (P q)
            graphVelocityPhase (fun p ↦ (curveGraphPosition γ e p).2) q ∈ g.source ∧
            HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2 ∧
            (∀ ξ : V,
              let Z := fun s ↦ fderiv ℝ (fun w ↦ P (w, s)) q.1 ξ
              HasDerivAt (fun s ↦ (Z s).1) (B' (Z q.2).1 + C (Z q.2).2) q.2 ∧
              HasDerivAt (fun s ↦ (Z s).2) (-A (Z q.2).1 - (Z q.2).2.comp B') q.2) ∧
            (∀ u v, A u v = A v u) ∧
            (∀ p r : V →L[ℝ] ℝ, r (C p) = p (C r)) ∧
            C = ContinuousLinearMap.inverse
              (GraphLegendre.verticalHessian L (g.symm ((q.2, (P q).1), (P q).2))) ∧
            ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (C p) ) ∧
          ∃ Q : Set (V × ℝ), IsOpen Q ∧ q₀ ∈ Q ∧ Q ⊆ D ∧
            ∀ q ∈ Q, q.1 = (0 : V) →
              let P := F.chartGraphPhase x₀ γ e
              let R := fderiv ℝ (fun w ↦ P (w, q.2)) q.1
              Function.Injective R ∧ (∀ u w : V, canonicalPhasePairing (R u) (R w) = 0) ∧
              let b := Module.finBasis ℝ V
              let Z := fun s ↦ fderiv ℝ (fun w ↦ P (w, s)) q.1
              let J := fun s ↦ vectorFamilyMatrix b (fun j ↦ (Z s (b j)).1)
              let K := fun s ↦ covectorFamilyMatrix b (fun j ↦ (Z s (b j)).2)
              let A := hamiltonianMatrixA b (GraphHamiltonian.blockA L g q.2 (P q))
              let B' := hamiltonianMatrixB b (GraphHamiltonian.blockB L g q.2 (P q))
              let C := hamiltonianMatrixC b (GraphHamiltonian.blockC L g q.2 (P q))
              HasDerivAt J (B' * J q.2 + C * K q.2) q.2 ∧
                HasDerivAt K (-A * J q.2 - B'ᵀ * K q.2) q.2 ∧
                Aᵀ = A ∧ Cᵀ = C ∧ C.PosDef ∧ (J q.2)ᵀ * K q.2 = (K q.2)ᵀ * J q.2 ∧
                (∀ u : Fin (Module.finrank ℝ V) → ℝ,
                  J q.2 *ᵥ u = 0 → K q.2 *ᵥ u = 0 → u = 0) ∧
                C = hamiltonianMatrixC b (ContinuousLinearMap.inverse
                  (GraphLegendre.verticalHessian L
                    (g.symm ((q.2, (P q).1), (P q).2)))) := by
  have hp : fderiv ℝ f y₀ ≠ 0 := by
    rw [hmatch]
    intro hzero
    have hv := congrArg (fun p : (ℝ × V) →L[ℝ] ℝ ↦ p v₀) hzero
    have hpos : 0 < fiberLegendre (F.chartEnergy x₀) (y₀, v₀) v₀ := by
      rw [hF.chartEnergy_euler x₀ hz]
      exact mul_pos (by norm_num) (F.chartEnergy_pos x₀ hz)
    exact (ne_of_gt hpos) hv
  obtain ⟨B₀, σ, U, hB₀, h0, hU, hyU, hUΩ, hσ, hσ0, hσΩ, hlevel,
    himm, hinj, himage⟩ := exists_smooth_graphLevelChart hΩ hf hy₀ hp
  refine ⟨σ, B₀, U, hB₀, h0, hU, hyU, hUΩ, hσ, hσ0, hσΩ, hlevel,
    himm, hinj, himage, ?_⟩
  have hlev : (fun w ↦ f (σ w)) =ᶠ[𝓝 (0 : V)] fun _ ↦ f y₀ := by
    filter_upwards [hB₀.mem_nhds h0] with w hw
    exact hlevel w hw
  have hz' : (σ 0, v₀) ∈ chartEnergyDomain x₀ := by simpa only [hσ0] using hz
  have hm' : fderiv ℝ f (σ 0) = fiberLegendre (F.chartEnergy x₀) (σ 0, v₀) := by
    simpa only [hσ0] using hmatch
  obtain ⟨ℓ, B, v, a, r, T, Φ, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    hΨ, hinit, hvar, e, g, D, he, hzes, hesub, hg, hgsub, hgi,
    hD, hqD, hDsub, hPC2, hgraph, Q, hQ, hqQ, hQD, hstructure⟩ :=
    hF.exists_potentialNormal_graphStructure x₀ hΩ hf hB₀ h0 hσ hσΩ hlev
      himm hz' hm' hpositive t₀
  refine ⟨ℓ, B, v, a, r, T, Φ, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    hΨ, hinit, hvar, e, g, D, he, hzes, hesub, hg, hgsub, hgi,
    hD, hqD, hDsub, hPC2, hgraph, Q, hQ, hqQ, hQD, ?_⟩
  intro q hq hlabel
  have hs := hstructure q hq hlabel
  refine ⟨hs.1, hs.2, ?_⟩
  have hpt := g.map_source (hgraph q (hQD hq)).1
  rw [hg] at hpt
  exact hF.chartGraph_parameter_matrices x₀ (Module.finBasis ℝ V) (Module.finBasis ℝ V)
    hg hgsub hgi hD hPC2 (fun z hz ↦ (hgraph z hz).2.1)
    (hQD hq) hpt hs.1 hs.2

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
