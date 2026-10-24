import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OTSelector.LinearAlgebra.Matrix.PhaseCell
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedPhaseSourceCellVolume.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedPhaseSourceCellVolume`; the selected original proof blocks follow. -/
section

/-!
Conditions: An invertible matrix, positive-semidefinite mobility, nonnegative radius and vectors in the given norm balls.

Objects: An explicit marked linear-phase cell and containment of the actual transformed position.

Proof detail: Apply the previously proved (1+U) inverse norm bound to z−Up and insert the actual affine cell definition.

Sources: Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Explicit phase-cell definition and membership algebra. No volume/intensity conclusion from the original file is included.
-/

/-!
# Original marked source-cell volume from the actual leg determinant

The marked envelope is defined by a Borel inverse-compliance inequality. Its
physical product-intensity is exactly the integrated original determinant, even
when its spatial extent is unbounded near an original clock endpoint.
-/
open Set Function Matrix MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original source envelope for a deterministic phase cell and a marked center. -/
def markedPhaseSourceCell (L : Matrix ι ι ℝ) (U : ℝ → Matrix ι ι ℝ)
    (c : ℝ → (ι → ℝ)) (B : Set ℝ) (R : ℝ) : Set ((ι → ℝ) × ℝ) :=
  {v | v.2 ∈ B ∧ ‖(1 + U v.2)⁻¹ *ᵥ (L⁻¹ *ᵥ (v.1 - c v.2))‖ ≤
    phaseSourceCellRadius ι R}







/-- Every bounded phase pair lies in the fixed original marked source envelope. -/
theorem mk_add_mulVec_sub_mem_markedPhaseSourceCell
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hU : ∀ a, (U a).PosSemidef) (c : ℝ → (ι → ℝ))
    {B : Set ℝ} {a R : ℝ} (ha : a ∈ B) (hR : 0 ≤ R)
    {z p : ι → ℝ} (hz : ‖z‖ ≤ R) (hp : ‖p‖ ≤ R) :
    (c a + L *ᵥ (z - U a *ᵥ p), a) ∈ markedPhaseSourceCell L U c B R := by
  refine ⟨ha, ?_⟩
  change ‖(1 + U a)⁻¹ *ᵥ (L⁻¹ *ᵥ ((c a + L *ᵥ (z - U a *ᵥ p)) - c a))‖ ≤ _
  rw [add_sub_cancel_left, Matrix.mulVec_mulVec (z - U a *ᵥ p) L⁻¹ L,
    Matrix.nonsing_inv_mul _ hL, Matrix.one_mulVec]
  exact (mem_phaseSourceCell_iff (hU a) R _).mp (sub_mulVec_mem_phaseSourceCell (hU a) hR hz hp)







end OTSelector.Reconstruction

end
end
