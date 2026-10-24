import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Measure.Hausdorff
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.GraphJacobiCoefficientContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.GraphJacobiCoefficientContinuity`; the selected original proof blocks follow. -/
section

/-!
Conditions: The actual graph Lagrangian and inverse Legendre chart are smooth on their actual domains; the phase path is continuous and stays in that target.

Objects: Continuity of the actual phase derivative, Hamiltonian Hessian blocks and fixed-basis coefficient matrices.

Proof detail: Differentiate the smooth field, take its continuous linear block readouts and compose them with the actual path.

Sources: Gerald Teschl, Section 8.3, pp. 239–241, equations (8.39)–(8.43), (8.47), and Problem 8.9 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=250); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Regularity/readout adapter for true graph-Hamiltonian derivatives; it proves no focal asymptotic.
-/

/-!
# Continuity of the actual graph-Jacobi coefficients

Joint smoothness of the actual graph Hamiltonian field gives continuity of its
position and momentum partial derivatives. Reading these same derivatives in the
fixed bases supplies the coefficient continuity needed at finite focal endpoints.
-/

open Set Matrix Module
open scoped Topology ContDiff Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The partial phase derivative of the actual nonautonomous graph field is jointly smooth. -/
theorem contDiffAt_graphField_phaseDerivative
    {L : (ℝ × V) × V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ g.target) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (V × (V →L[ℝ] ℝ)) ↦
      fderiv ℝ (GraphHamiltonian.field L g q.1) q.2) (t, p) := by
  have hfield : ContDiffAt ℝ ∞
      (fun q : ℝ × (V × (V →L[ℝ] ℝ)) ↦ GraphHamiltonian.field L g q.1 q.2)
      (t, p) :=
    ((GraphHamiltonian.contDiffOn_field hL hG).contDiffAt (g.open_target.mem_nhds hp)).comp
      (t, p) ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  apply ContDiffAt.fderiv (n := ∞) (m := ∞)
    (g := fun q : ℝ × (V × (V →L[ℝ] ℝ)) ↦ q.2)
    (f := fun q z ↦ GraphHamiltonian.field L g q.1 z) _ contDiffAt_snd (by simp)
  exact hfield.comp ((t, p), p) (contDiffAt_fst.fst.prodMk contDiffAt_snd)

/-- Actual graph Hamiltonian blocks remain continuous along every continuous
phase path inside their original Legendre domain. -/
theorem continuousOn_graphHamiltonian_blocks
    {L : (ℝ × V) × V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {p : ℝ → V × (V →L[ℝ] ℝ)} {I : Set ℝ} (hp : ContinuousOn p I)
    (htarget : ∀ t ∈ I, ((t, (p t).1), (p t).2) ∈ g.target) :
    ContinuousOn (fun t ↦ GraphHamiltonian.blockA L g t (p t)) I ∧
      ContinuousOn (fun t ↦ GraphHamiltonian.blockB L g t (p t)) I ∧
      ContinuousOn (fun t ↦ GraphHamiltonian.blockC L g t (p t)) I := by
  have hD : ContinuousOn (fun t ↦ fderiv ℝ (GraphHamiltonian.field L g t) (p t)) I := by
    intro t ht
    have hpartial : ContinuousAt
        (fun q : ℝ × (V × (V →L[ℝ] ℝ)) ↦
          fderiv ℝ (GraphHamiltonian.field L g q.1) q.2) (t, p t) :=
      (contDiffAt_graphField_phaseDerivative hL hG (htarget t ht)).continuousAt
    have hpath : ContinuousWithinAt (fun r : ℝ ↦ (r, p r)) I t :=
      continuousWithinAt_id.prodMk (hp t ht)
    exact ContinuousAt.comp_continuousWithinAt (f := fun r : ℝ ↦ (r, p r))
      hpartial hpath
  refine ⟨?_, ?_, ?_⟩
  · exact ((continuousOn_const.clm_comp hD).clm_comp continuousOn_const).neg
  · exact (continuousOn_const.clm_comp hD).clm_comp continuousOn_const
  · exact (continuousOn_const.clm_comp hD).clm_comp continuousOn_const

variable [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The same fixed-basis matrix coefficients are continuous, including at either
finite endpoint inside the actual graph-phase domain. -/
theorem continuousOn_graphHamiltonian_matrix_coefficients
    (bV : Basis ι ℝ V)
    {L : (ℝ × V) × V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {p : ℝ → V × (V →L[ℝ] ℝ)} {I : Set ℝ} (hp : ContinuousOn p I)
    (htarget : ∀ t ∈ I, ((t, (p t).1), (p t).2) ∈ g.target) :
    ContinuousOn (fun t ↦ hamiltonianMatrixA bV (GraphHamiltonian.blockA L g t (p t))) I ∧
      ContinuousOn (fun t ↦ hamiltonianMatrixB bV (GraphHamiltonian.blockB L g t (p t))) I ∧
      ContinuousOn (fun t ↦ hamiltonianMatrixC bV (GraphHamiltonian.blockC L g t (p t))) I := by
  obtain ⟨hA, hB, hC⟩ := continuousOn_graphHamiltonian_blocks hL hG hp htarget
  refine ⟨?_, ?_, ?_⟩
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (hA.clm_apply continuousOn_const).clm_apply continuousOn_const
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (basisCovector bV i).continuous.comp_continuousOn
      (hB.clm_apply continuousOn_const)
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (basisCovector bV i).continuous.comp_continuousOn
      (hC.clm_apply continuousOn_const)

end OTSelector.Reconstruction

end
end
