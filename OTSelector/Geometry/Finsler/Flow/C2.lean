import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.LocalC2
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow

/-!
## Lemma skeleton

* **Conditions:** Smooth strongly convex Finsler energy and a nonzero chart phase.
* **Objects:** A local joint-C2 Hamiltonian flow with its variational derivative.
* **Proof detail:** Build the chart Legendre inverse and smooth Hamiltonian field; invoke the finite-dimensional C2 flow constructor and keep the flow inside its domain.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 2, pp. 304–305 (Minkowski norms and Finsler metrics), p. 308 (Legendre duality, equation (2–12)).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2

**Relationship to the sources:** This packages already proved regular-Lagrangian and ODE facts for the Finsler chart; no global flow or complete-geodesic hypothesis is inserted.
-/

/-!
# Jointly C2 actual Finsler Hamiltonian flow

Apply the open-domain joint C2 flow construction to the actual local Hamiltonian of a
smooth strongly convex Finsler chart energy. The same solution family stays in the
Legendre target, is jointly C2 in initial state and time on a positive closed box, and
retains the actual initial-state derivatives and their genuine Hamiltonian block equations.
The momentum block is the positive inverse of the actual vertical energy Hessian, with
symmetry expressed by the canonical dual pairing and no inner product identification.

All neighborhood sizes and derivative bounds are derived from the original Finsler data.
This theorem concerns a local fixed-chart flow and its actual variations; it does not
assert joint C-infinity regularity or local length minimality.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- The actual Finsler Hamiltonian flow is jointly C2 on a positive closed flow box,
with its true initial-state derivatives satisfying the Hamiltonian block variation equations.
The positive momentum block is the inverse of the actual vertical energy Hessian. -/
theorem exists_chartHamiltonian_c2Flow (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let p₀ := parametricLegendre L z
    ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (r : ℝ≥0) (T : ℝ) (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)),
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ 0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      ContDiffOn ℝ 2 Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun q ↦ Φ (q, t)) p₀) ∧
      fderiv ℝ (fun q ↦ Φ (q, t₀)) p₀ = ContinuousLinearMap.id ℝ _ ∧
      (∀ δ : E × (E →L[ℝ] ℝ), flowPositionVariation Φ p₀ δ t₀ = δ.1 ∧
        flowMomentumVariation Φ p₀ δ t₀ = δ.2) ∧
      (∀ (δ : E × (E →L[ℝ] ℝ)) (t : ℝ), t ∈ Icc (t₀ - T) (t₀ + T) →
        HasDerivWithinAt (flowPositionVariation Φ p₀ δ)
          (localHamiltonianBlockB L e (Φ (p₀, t)) (flowPositionVariation Φ p₀ δ t) +
            localHamiltonianBlockC L e (Φ (p₀, t)) (flowMomentumVariation Φ p₀ δ t))
          (Icc (t₀ - T) (t₀ + T)) t ∧
        HasDerivWithinAt (flowMomentumVariation Φ p₀ δ)
          (-localHamiltonianBlockA L e (Φ (p₀, t)) (flowPositionVariation Φ p₀ δ t) -
            (flowMomentumVariation Φ p₀ δ t).comp
              (localHamiltonianBlockB L e (Φ (p₀, t))))
          (Icc (t₀ - T) (t₀ + T)) t) ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T),
        localHamiltonianBlockC L e (Φ (p₀, t)) =
          ContinuousLinearMap.inverse (verticalEnergyHessian L (e.symm (Φ (p₀, t)))) ∧
        (∀ b w : E, localHamiltonianBlockA L e (Φ (p₀, t)) b w =
          localHamiltonianBlockA L e (Φ (p₀, t)) w b) ∧
        (∀ q s : E →L[ℝ] ℝ, s (localHamiltonianBlockC L e (Φ (p₀, t)) q) =
          q (localHamiltonianBlockC L e (Φ (p₀, t)) s)) ∧
        (∀ q : E →L[ℝ] ℝ, q ≠ 0 → 0 < q (localHamiltonianBlockC L e (Φ (p₀, t)) q)) := by
  let L := F.chartEnergy x₀
  let p₀ := parametricLegendre L z
  obtain ⟨e, he, hsource, htarget, hsub, hG, _, hX, _⟩ :=
    hF.exists_smooth_chartHamiltonian x₀ hz
  obtain ⟨r, T, hr, hT, Φ, hflow, hmap, hC2, hdiff, hinit, hvar⟩ :=
    LocalFlow.exists_c2Flow_in_open e.open_target hX htarget t₀
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have hcenter : p₀ ∈ closedBall p₀ (r : ℝ) := mem_closedBall_self r.coe_nonneg
  have htargetOrbit : ∀ t ∈ Icc (t₀ - T) (t₀ + T), Φ (p₀, t) ∈ e.target :=
    fun t ht ↦ hmap ⟨hcenter, ht⟩
  refine ⟨e, r, T, Φ, he, hsource, hsub, hG, hr, hT, hflow, hmap,
    hC2, hdiff, hinit, fun δ ↦ flowVariation_initial hinit δ, ?_, ?_⟩
  · intro δ t ht
    exact hasDerivWithinAt_hamiltonianFlowVariation_blocks he hL hG
      (htargetOrbit t ht) (hvar δ t ht)
  · intro t ht
    have hp := htargetOrbit t ht
    have hpositive : ∀ w : E, w ≠ 0 →
        0 < verticalEnergyHessian L (e.symm (Φ (p₀, t))) w w :=
      fun _ hw ↦ hF.chartEnergy_hessian_pos x₀ (hsub (e.map_target hp)) hw
    exact ⟨localHamiltonianBlockC_eq_inverse he hL hG hp hpositive,
      localHamiltonianBlockA_symm he hL hG hp,
      localHamiltonianBlockC_symm he hL hG hp,
      fun _ hq ↦ localHamiltonianBlockC_pos he hL hG hp hpositive hq⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex

end OTSelector.Geometry
