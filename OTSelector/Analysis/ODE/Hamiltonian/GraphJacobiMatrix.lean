import Mathlib.LinearAlgebra.Matrix.PosDef
import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.GraphLength
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.GraphDynamics
import OTSelector.Geometry.Finsler.GraphHamiltonianVariation
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.Jacobi.Pairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.GraphJacobiMatrix.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.GraphJacobiMatrix`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual graph Hamiltonian parameter variations with matched vector/covector bases; Hessian symmetry, positivity and isotropy where required.

Objects: Matrix Jacobi equations, symmetric/positive blocks, zero Wronskian and full-phase injectivity.

Proof detail: Differentiate the true Hamiltonian flow, express each block in the chosen bases and translate canonical pairings and rank to matrices.

Sources: Gerald Teschl, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56); Gerald Teschl, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250); Ana Cannas da Silva, Homework 1, Symplectic Linear Algebra, p. 8; Section 2.2, pp. 9–10 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=16); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Derived coordinate form of the actual linearized Hamilton equation; Jacobi curvature is background rather than a substituted equation.
-/

/-!
# Square coordinates of the actual graph Jacobi family

Two bases with the same finite index read the actual parameter derivative into square
position and momentum matrices. The genuine graph Hamiltonian block equations become
matrix equations; original phase injectivity and canonical isotropy give full matrix
phase rank and zero Wronskian. Positivity is inherited from the actual Finsler graph
Hessian, with no position-block invertibility assumption.
-/

open Set Matrix Module Manifold
open scoped ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι]

omit [FiniteDimensional ℝ V] in
/-- Injectivity of the phase map gives trivial joint kernel for its two square matrices. -/
theorem phase_matrices_joint_kernel (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {Z : W →L[ℝ] (V × (V →L[ℝ] ℝ))} (hinj : Function.Injective Z)
    (u : ι → ℝ)
    (hJ : vectorFamilyMatrix bV (fun j ↦ (Z (bW j)).1) *ᵥ u = 0)
    (hP : covectorFamilyMatrix bV (fun j ↦ (Z (bW j)).2) *ᵥ u = 0) : u = 0 := by
  classical
  let w : W := ∑ j, u j • bW j
  have hposition : (Z w).1 = 0 := by
    apply bV.repr.injective
    ext i
    have h := congrFun hJ i
    simpa only [w, map_sum, map_smul, Prod.fst_sum, Prod.smul_fst,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, vectorFamilyMatrix, Pi.zero_apply, map_zero, Finsupp.zero_apply,
      mul_comm] using h
  have hmomentum : (Z w).2 = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    change (Z w).2 v = 0
    rw [← bV.sum_repr v, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    have h : (Z w).2 (bV i) = 0 := by
      have hh := congrFun hP i
      simpa only [w, map_sum, map_smul, Prod.snd_sum, Prod.smul_snd,
        _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Matrix.mulVec,
        dotProduct, covectorFamilyMatrix, Pi.zero_apply, mul_comm] using hh
    rw [map_smul, h, smul_zero]
  have hw : w = 0 := hinj (by simpa using (Prod.ext hposition hmomentum : Z w = 0))
  have hu := congrArg bW.equivFun hw
  simpa only [w, ← bW.equivFun_symm_apply, bW.equivFun.apply_symm_apply, map_zero] using hu

/-- A canonically symmetric positive dual-to-vector map has a positive definite basis matrix. -/
theorem hamiltonianMatrixC_posDef (b : Basis ι ℝ V)
    {C : (V →L[ℝ] ℝ) →L[ℝ] V}
    (hsym : ∀ p q : V →L[ℝ] ℝ, q (C p) = p (C q))
    (hpos : ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (C p)) :
    (hamiltonianMatrixC b C).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hamiltonianMatrixC_transpose b hsym
  intro x hx
  let q : V →L[ℝ] ℝ := ∑ i, x i • basisCovector b i
  have hqeval (i : ι) : q (b i) = x i := by
    simp [q, basisCovector_apply, b.repr_self, Finsupp.single_apply]
  have hq : q ≠ 0 := by
    intro heq
    apply hx
    funext i
    simpa only [hqeval, _root_.zero_apply, Pi.zero_apply] using
      congrArg (fun p : V →L[ℝ] ℝ ↦ p (b i)) heq
  have hmul (i : ι) : (hamiltonianMatrixC b C *ᵥ x) i = b.repr (C q) i := by
    simp only [q, Matrix.mulVec, dotProduct, hamiltonianMatrixC,
      map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have heq : star x ⬝ᵥ (hamiltonianMatrixC b C *ᵥ x) = q (C q) := by
    simp only [dotProduct, Pi.star_apply, star_trivial, hmul]
    simp only [q, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, basisCovector_apply]
  rw [heq]
  exact hpos q hq

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- The actual graph phase parameter derivative has square Jacobi matrices in matching
parameter and spatial bases. Their joint kernel is trivial and their Wronskian vanishes;
the positive matrix C is the basis representation of the genuine inverse graph Hessian. -/
theorem chartGraph_parameter_matrices (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.chartGraphLagrangian x₀))
    (hsub : g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.chartGraphLagrangian x₀) g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target)
    (hinj : Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    let L := F.chartGraphLagrangian x₀
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    let P := fun s ↦ covectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).2)
    let A := hamiltonianMatrixA bV (GraphHamiltonian.blockA L g t (Ψ (w₀, t)))
    let B := hamiltonianMatrixB bV (GraphHamiltonian.blockB L g t (Ψ (w₀, t)))
    let C := hamiltonianMatrixC bV (GraphHamiltonian.blockC L g t (Ψ (w₀, t)))
    HasDerivAt J (B * J t + C * P t) t ∧
      HasDerivAt P (-A * J t - Bᵀ * P t) t ∧ Aᵀ = A ∧ Cᵀ = C ∧ C.PosDef ∧
      (J t)ᵀ * P t = (P t)ᵀ * J t ∧
      (∀ u : ι → ℝ, J t *ᵥ u = 0 → P t *ᵥ u = 0 → u = 0) ∧
      C = hamiltonianMatrixC bV (ContinuousLinearMap.inverse
        (GraphLegendre.verticalHessian L (g.symm ((t, (Ψ (w₀, t)).1),
          (Ψ (w₀, t)).2)))) := by
  let L := F.chartGraphLagrangian x₀
  have hL : ContDiffOn ℝ ∞ L g.source := (hF.contDiffOn_chartGraphLength x₀).mono hsub
  have hv (ξ : W) :=
    hasDerivAt_graphHamiltonian_parameterVariation hg hL hG hD hΨ hODE hz hp ξ
  have hm := hasDerivWithinAt_hamiltonian_family_matrices (I := univ) (t := t) bV
    (J := fun j s ↦ (fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ (bW j)).1)
    (P := fun j s ↦ (fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ (bW j)).2)
    (A := GraphHamiltonian.blockA L g t (Ψ (w₀, t)))
    (B := GraphHamiltonian.blockB L g t (Ψ (w₀, t)))
    (C := GraphHamiltonian.blockC L g t (Ψ (w₀, t)))
    (fun j ↦ (hv (bW j)).1.hasDerivWithinAt)
    (fun j ↦ (hv (bW j)).2.hasDerivWithinAt)
  have hc := hF.chartGraphDynamics_blocks x₀ hg hsub hG hp
  refine ⟨hm.1.hasDerivAt (by simp), hm.2.hasDerivAt (by simp),
    hamiltonianMatrixA_transpose bV hc.2.1,
    hamiltonianMatrixC_transpose bV hc.2.2.1,
    hamiltonianMatrixC_posDef bV hc.2.2.1 hc.2.2.2.2.1, ?_,
    fun u hJ hP ↦ phase_matrices_joint_kernel bW bV hinj u hJ hP, ?_⟩
  · apply sub_eq_zero.mp
    ext i j
    rw [matrix_wronskian_apply]
    exact hpair (bW i) (bW j)
  · exact congrArg (hamiltonianMatrixC bV) hc.2.2.2.1

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
