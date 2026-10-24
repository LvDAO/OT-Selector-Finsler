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
import OTSelector.Analysis.ODE.Flow.LocalVariational
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian

/-!
## Lemma skeleton

* **Conditions:** For generic block splitting: a differentiable actual initial-state flow variation and smooth Hamiltonian data. The Finsler existence result assumes finite-dimensional smooth strongly convex data, a nonzero chart state and initial time.
* **Objects:** The position J and momentum P components of the actual initial-state Fréchet derivative of a constructed Hamiltonian flow; blocks A,B,C from the true scalar Hamiltonian.
* **Proof detail:** Construct an open-set local differentiable flow, then project its genuine variational equation through the actual canonical field derivative. This yields J′=BJ+CP, P′=-AJ-P∘B, initial identity, and positive inverse-Hessian C on a closed time interval.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250
* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 11, p. 327, equation (11–3), Jacobi equation for a geodesic variation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=25

**Relationship to the sources:** This specializes the ODE first variational equation to the Hamiltonian coordinate field. It supplies phase-space variations related to Finsler Jacobi theory; it does not establish the curvature equation (11–3) or identify a Chern covariant derivative.
-/

/-!
# Actual initial-state variations of the local Finsler Hamiltonian flow

The general open-set flow theorem constructs a local solution family and its actual
Fréchet derivative in the initial state. Applied to the Hamiltonian of the genuine smooth
strongly convex Finsler chart energy, this yields position and momentum variations `J` and `P`.
The actual linearized canonical field gives `J' = B J + C P` and `P' = -A J - P ∘ B`.
Here `A`, `B`, and `C` are extracted from the true derivative of that Hamiltonian field;
`A` and `C` are symmetric under the canonical pairing and `C` is the positive inverse
of the actual vertical energy Hessian. No inner product identification is selected.

The construction assumes only the original smooth strongly convex Finsler structure,
a nonzero state in a tangent chart, and an initial time. The time and initial-state
neighborhoods and all derivative bounds are derived by the general flow theorem.
Initial differentiability is proved at the prescribed central state, for every time in
a closed interval. Directional variation equations hold as within derivatives there,
hence as ordinary derivatives in its interior. The variations are actual `fderiv` values,
not separately supplied solutions of the linearized equation.

This is a local fixed-chart result. It does not establish minimizing length, construct
conormal transport-ray variations, or prove the complete selector theorem.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Position component of the actual initial-state Fréchet derivative of a phase flow. -/
noncomputable def flowPositionVariation
    (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ))
    (p δ : E × (E →L[ℝ] ℝ)) (t : ℝ) : E :=
  (fderiv ℝ (fun q ↦ Φ (q, t)) p δ).1

/-- Momentum component of the actual initial-state Fréchet derivative of a phase flow. -/
noncomputable def flowMomentumVariation
    (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ))
    (p δ : E × (E →L[ℝ] ℝ)) (t : ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ (fun q ↦ Φ (q, t)) p δ).2

/-- The actual phase variation equations split into the genuine Hamiltonian Hessian blocks.
This is the component calculation used after constructing the flow derivative below. -/
theorem hasDerivWithinAt_hamiltonianFlowVariation_blocks
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {p δ : E × (E →L[ℝ] ℝ)} {I : Set ℝ} {t : ℝ} (ht : Φ (p, t) ∈ e.target)
    (hvar : HasDerivWithinAt (fun s ↦ fderiv ℝ (fun q ↦ Φ (q, s)) p δ)
      (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p, t))
        (fderiv ℝ (fun q ↦ Φ (q, t)) p δ)) I t) :
    HasDerivWithinAt (flowPositionVariation Φ p δ)
      (localHamiltonianBlockB L e (Φ (p, t)) (flowPositionVariation Φ p δ t) +
        localHamiltonianBlockC L e (Φ (p, t)) (flowMomentumVariation Φ p δ t)) I t ∧
    HasDerivWithinAt (flowMomentumVariation Φ p δ)
      (-localHamiltonianBlockA L e (Φ (p, t)) (flowPositionVariation Φ p δ t) -
        (flowMomentumVariation Φ p δ t).comp (localHamiltonianBlockB L e (Φ (p, t)))) I t := by
  have hblocks :
      fderiv ℝ (localHamiltonianVectorField L e) (Φ (p, t))
        (fderiv ℝ (fun q ↦ Φ (q, t)) p δ) =
      (localHamiltonianBlockB L e (Φ (p, t)) (flowPositionVariation Φ p δ t) +
        localHamiltonianBlockC L e (Φ (p, t)) (flowMomentumVariation Φ p δ t),
        -localHamiltonianBlockA L e (Φ (p, t)) (flowPositionVariation Φ p δ t) -
          (flowMomentumVariation Φ p δ t).comp
            (localHamiltonianBlockB L e (Φ (p, t)))) :=
    localHamiltonianVectorField_linearized_blocks he hL hG ht _ _
  rw [hblocks] at hvar
  exact ⟨hvar.fst, hvar.snd⟩

/-- At the initial time the actual position and momentum variations recover the prescribed
initial direction whenever the constructed flow has initial derivative equal to the identity. -/
theorem flowVariation_initial
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {p : E × (E →L[ℝ] ℝ)} {t₀ : ℝ}
    (hinit : fderiv ℝ (fun q ↦ Φ (q, t₀)) p = ContinuousLinearMap.id ℝ _) (δ : E × (E →L[ℝ] ℝ)) :
    flowPositionVariation Φ p δ t₀ = δ.1 ∧ flowMomentumVariation Φ p δ t₀ = δ.2 := by
  simp only [flowPositionVariation, flowMomentumVariation, hinit, ContinuousLinearMap.id_apply,
    and_self]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- The genuine Finsler Hamiltonian flow has actual initial-state derivatives satisfying
the Hamiltonian block variation equations, with positive inverse-Hessian momentum block.
The flow, its derivative, and the variational equation are all constructed from the Finsler data. -/
theorem exists_chartHamiltonian_variationalFlow (hF : F.IsSmoothStronglyConvex)
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
  obtain ⟨r, T, hr, hT, Φ, hflow, hmap, hdiff, hinit, hvar⟩ :=
    LocalFlow.exists_differentiableFlow_in_open e.open_target hX htarget t₀
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have hcenter : p₀ ∈ closedBall p₀ (r : ℝ) := mem_closedBall_self r.coe_nonneg
  have htargetOrbit : ∀ t ∈ Icc (t₀ - T) (t₀ + T), Φ (p₀, t) ∈ e.target :=
    fun t ht ↦ hmap ⟨hcenter, ht⟩
  refine ⟨e, r, T, Φ, he, hsource, hsub, hG, hr, hT, hflow, hmap,
    hdiff, hinit, fun δ ↦ flowVariation_initial hinit δ, ?_, ?_⟩
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
