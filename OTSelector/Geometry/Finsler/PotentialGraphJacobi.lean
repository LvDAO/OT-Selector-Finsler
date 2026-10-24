import OTSelector.Analysis.Calculus.GraphVelocityPhase
import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.GraphMomentum
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.HamiltonianFamily
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.PotentialNormalC2
import OTSelector.Geometry.Finsler.RegraphedJacobi
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialGraphJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialGraphJacobi`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PotentialGraphJacobi

* **Conditions:** Smooth immersed potential-level data matching the actual central Finsler momentum and positive central longitudinal velocity.
* **Objects:** A normalized potential normal family and its same-family actual reduced graph Jacobi system.
* **Proof detail:** Build the constant-energy conormal seed and C2 flow, verify longitudinal positivity from the original field equation, then apply actual regraphing and parameter differentiation.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.

Source relation (derived): The ambient rank/isotropy/normality remains attached to this family; regraphed rank and rough-potential matching are separate later results.
-/

/-!
# Actual reduced Jacobi equations of a normalized potential normal family

A genuine smooth immersed level set and its actual potential differential construct one
positive constant-energy seed, ambient Legendre branch and Hamiltonian flow. The same
jointly C2 family constructs graph coordinates and a graph Legendre branch, and its actual
graph parameter derivative solves the reduced Jacobi equations. Central longitudinal
positivity is checked from the given velocity through the actual original flow equation.
The original phase rank, isotropy and normality remain attached to the same family;
no corresponding regraphed rank assertion or rough-potential identification is made.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- A smooth potential level-set family constructs its same-flow genuine reduced Jacobi
system without assuming graph equations, phase regularity or variational equations. -/
theorem exists_potentialNormal_graphJacobi (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {f : (ℝ × V) → ℝ} {σ : W → ℝ × V} {Ω : Set (ℝ × V)}
    {B₀ : Set W} {w₀ : W} {c : ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hB₀ : IsOpen B₀) (hw₀ : w₀ ∈ B₀)
    (hσ : ContDiffOn ℝ ∞ σ B₀) (hσΩ : MapsTo σ B₀ Ω)
    (hlevel : (fun w ↦ f (σ w)) =ᶠ[𝓝 w₀] fun _ ↦ c)
    (himm : Function.Injective (fderiv ℝ σ w₀))
    {v₀ : ℝ × V} (hz : (σ w₀, v₀) ∈ chartEnergyDomain x₀)
    (hmatch : fderiv ℝ f (σ w₀) = fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀))
    (hpositive : 0 < v₀.1) (t₀ : ℝ) :
    let L₀ := F.chartEnergy x₀
    let z₀ := (σ w₀, v₀)
    let p₀ := parametricLegendre L₀ z₀
    ∃ (ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
        ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)))
      (B : Set W) (v : W → ℝ × V) (a : W → ℝ) (r : ℝ≥0) (T : ℝ)
      (Φ : ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) × ℝ →
        (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)),
      let seed := potentialConormalState f σ a
      let Ψ := fun q : W × ℝ ↦ Φ (seed q.1, q.2)
      let γ := fun q ↦ (Ψ q).1
      let Z₀ := fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀
      let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
      let L := F.chartGraphLagrangian x₀
      (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
        parametricLegendre L₀ ∧
      z₀ ∈ ℓ.source ∧ ℓ.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ ℓ.symm ℓ.target ∧ IsOpen B ∧ w₀ ∈ B ∧ B ⊆ B₀ ∧
      ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧ v w₀ = v₀ ∧ a w₀ = 1 ∧
      ContDiffOn ℝ ∞ seed B ∧ seed w₀ = p₀ ∧
      (∀ w ∈ B, (σ w, v w) ∈ ℓ.source ∧ 0 < a w ∧
        L₀ (σ w, v w) = L₀ z₀ ∧
        fiberLegendre L₀ (σ w, v w) = a w • fderiv ℝ f (σ w) ∧
        ℓ.symm (seed w) = (σ w, v w) ∧ seed w ∈ closedBall p₀ r) ∧
      0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L₀ ℓ)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) ℓ.target ∧
      ContDiffOn ℝ 2 Ψ (B ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
      Z₀ t₀ = fderiv ℝ seed w₀ ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun w ↦ Ψ (w, t)) w₀ ∧ Function.Injective (Z₀ t) ∧
        (∀ u w : W, canonicalPhasePairing (Z₀ t u) (Z₀ t w) = 0) ∧
        (∀ u : W, HasDerivWithinAt (fun s ↦ Z₀ s u)
          (fderiv ℝ (localHamiltonianVectorField L₀ ℓ) (Φ (p₀, t)) (Z₀ t u))
          (Icc (t₀ - T) (t₀ + T)) t) ∧
        ∀ u : W, (Z₀ t u).1 ∈ (fiberLegendre L₀ (ℓ.symm (Φ (p₀, t)))).ker) ∧
      ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
        (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
        (D : Set (W × ℝ)),
        (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
        (w₀, t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ Ioo (t₀ - T) (t₀ + T) ∧
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
  let L₀ := F.chartEnergy x₀
  let z₀ := (σ w₀, v₀)
  let p₀ := parametricLegendre L₀ z₀
  obtain ⟨ℓ, B, v, a, r, T, Φ, D₀, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    _, hbox, hΦ, hΨ, hinit, hvar⟩ :=
    hF.exists_chartHamiltonian_potentialNormalC2Flow
      x₀ hΩ hf hB₀ hw₀ hσ hσΩ hlevel himm hz hmatch t₀
  let seed := potentialConormalState f σ a
  let Ψ := fun q : W × ℝ ↦ Φ (seed q.1, q.2)
  let γ := fun q : W × ℝ ↦ (Ψ q).1
  change seed w₀ = p₀ at hseed₀
  have hmem : MapsTo seed B (closedBall p₀ r) := fun w hw ↦ (hdata w hw).2.2.2.2.2
  obtain ⟨_, hΨmap, hODE⟩ := hamiltonianFlow_seededFamily hflow
    (hΦ.mono hbox) hmap (hseed.of_le (by simp : 2 ≤ ∞)) hmem
  have ht₀ : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  have hcenter : Ψ (w₀, t₀) = p₀ := by
    change Φ (seed w₀, t₀) = p₀
    rw [hseed₀]
    exact hflow.apply_initial p₀ (mem_closedBall_self r.coe_nonneg)
  have hinv : ℓ.symm p₀ = z₀ := by
    rw [show p₀ = ℓ z₀ by rw [hℓ]]
    exact ℓ.left_inv hzs
  have hvelocity : fderiv ℝ γ (w₀, t₀) (0, 1) = v₀ := by
    have hγ₂ : ContDiffAt ℝ 2 γ (w₀, t₀) :=
      hΨ.fst.contDiffAt ((hB.prod isOpen_Ioo).mem_nhds
        (show (w₀, t₀) ∈ B ×ˢ Ioo (t₀ - T) (t₀ + T) from ⟨hwB, ht₀⟩))
    have hγa := hγ₂.differentiableAt (by norm_num)
    have hd := hγa.hasFDerivAt.comp_hasDerivAt t₀
      ((hasDerivAt_const t₀ w₀).prodMk (hasDerivAt_id t₀))
    have heq := hd.unique (hasDerivAt_hamiltonian_position (hODE w₀ hwB t₀ ht₀))
    simpa only [hcenter, hinv] using heq
  have hpositive' : 0 < (fderiv ℝ γ (w₀, t₀) (0, 1)).1 := by
    rw [hvelocity]
    exact hpositive
  have hgraph := hF.exists_chartRegraphedJacobi x₀ hℓ hsub hℓi hB isOpen_Ioo
    isPreconnected_Ioo hΨ hΨmap hODE ⟨hwB, ht₀⟩ hpositive'
  exact ⟨ℓ, B, v, a, r, T, Φ, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    hΨ, hinit, hvar, hgraph⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
