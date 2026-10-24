import OTSelector.Analysis.ODE.GraphHamiltonianCoefficientContinuity
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.GraphJacobiCoefficientSmoothness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.GraphJacobiCoefficientSmoothness`; the selected original proof blocks follow. -/
section

/-!
Conditions: The actual graph Lagrangian and inverse chart are smooth and the actual phase path is smooth in their domain.

Objects: Smoothness of the unchanged Hamiltonian blocks and fixed-basis matrix coefficients.

Proof detail: Compose actual smooth phase derivatives with the path and bounded linear coordinate readouts.

Sources: Gerald Teschl, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Smooth coefficient-readout consequence, without an additional focal endpoint hypothesis.
-/

/-!
# Smoothness of unchanged actual graph-Jacobi coefficients

The actual graph-field phase derivative is smooth. Along any smooth actual phase path,
its same Hamiltonian blocks and fixed-basis matrix coefficients are smooth. Matrix readouts
are continuous linear maps, so this holds in the operator norm used by the focal geometry.
-/

open Set Matrix Module
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual smooth phase paths give smooth actual graph Hamiltonian blocks. -/
theorem contDiffOn_graphHamiltonian_blocks
    {L : (ℝ×V)×V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ×V)×V) ((ℝ×V)×(V→L[ℝ]ℝ))}
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {p : ℝ → V×(V→L[ℝ]ℝ)} {I : Set ℝ} (hp : ContDiffOn ℝ ∞ p I)
    (htarget : ∀ t∈I, ((t,(p t).1),(p t).2)∈g.target) :
    ContDiffOn ℝ ∞ (fun t ↦ GraphHamiltonian.blockA L g t (p t)) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ GraphHamiltonian.blockB L g t (p t)) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ GraphHamiltonian.blockC L g t (p t)) I := by
  have hD : ContDiffOn ℝ ∞ (fun t ↦ fderiv ℝ (GraphHamiltonian.field L g t) (p t)) I := by
    intro t ht
    exact (contDiffAt_graphField_phaseDerivative hL hG (htarget t ht)).comp_contDiffWithinAt t
      (contDiffWithinAt_id.prodMk (hp t ht))
  exact ⟨((contDiffOn_const.clm_comp hD).clm_comp contDiffOn_const).neg,
    (contDiffOn_const.clm_comp hD).clm_comp contDiffOn_const,
    (contDiffOn_const.clm_comp hD).clm_comp contDiffOn_const⟩

variable [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]

/-- The fixed original-basis matrix coefficients are smooth for those same actual blocks. -/
theorem contDiffOn_graphHamiltonian_matrix_coefficients
    (bV : Basis ι ℝ V)
    {L : (ℝ×V)×V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ×V)×V) ((ℝ×V)×(V→L[ℝ]ℝ))}
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {p : ℝ → V×(V→L[ℝ]ℝ)} {I : Set ℝ} (hp : ContDiffOn ℝ ∞ p I)
    (htarget : ∀ t∈I, ((t,(p t).1),(p t).2)∈g.target) :
    ContDiffOn ℝ ∞ (fun t ↦ hamiltonianMatrixA bV (GraphHamiltonian.blockA L g t (p t))) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ hamiltonianMatrixB bV (GraphHamiltonian.blockB L g t (p t))) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ hamiltonianMatrixC bV (GraphHamiltonian.blockC L g t (p t))) I := by
  obtain ⟨hA,hB,hC⟩ := contDiffOn_graphHamiltonian_blocks hL hG hp htarget
  let LA : (V→L[ℝ]V→L[ℝ]ℝ) →ₗ[ℝ] Matrix ι ι ℝ := {
    toFun := hamiltonianMatrixA bV
    map_add' := by intro X Y; ext i j; simp [hamiltonianMatrixA]
    map_smul' := by intro r X; ext i j; simp [hamiltonianMatrixA] }
  let LB : (V→L[ℝ]V) →ₗ[ℝ] Matrix ι ι ℝ := {
    toFun := hamiltonianMatrixB bV
    map_add' := by intro X Y; ext i j; simp [hamiltonianMatrixB]
    map_smul' := by intro r X; ext i j; simp [hamiltonianMatrixB] }
  let LC : ((V→L[ℝ]ℝ)→L[ℝ]V) →ₗ[ℝ] Matrix ι ι ℝ := {
    toFun := hamiltonianMatrixC bV
    map_add' := by intro X Y; ext i j; simp [hamiltonianMatrixC]
    map_smul' := by intro r X; ext i j; simp [hamiltonianMatrixC] }
  constructor
  · simpa only [Function.comp_def,LA,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,
      AddHom.coe_mk] using LA.toContinuousLinearMap.contDiff.comp_contDiffOn hA
  constructor
  · simpa only [Function.comp_def,LB,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,
      AddHom.coe_mk] using LB.toContinuousLinearMap.contDiff.comp_contDiffOn hB
  · simpa only [Function.comp_def,LC,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,
      AddHom.coe_mk] using LC.toContinuousLinearMap.contDiff.comp_contDiffOn hC

end OTSelector.Reconstruction

end
end
