import OTSelector.LinearAlgebra.Matrix.CoarseComplianceCoordinates
import OTSelector.LinearAlgebra.Matrix.MeasurablePhaseCongruence
import OTSelector.MeasureTheory.LinearPhaseCell
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CoarsePhaseSourceCells.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CoarsePhaseSourceCells`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.CoarsePhaseSourceCells

**Conditions:** An invertible spatial frame, nonzero scale and positive-semidefinite original compliance fields; coarse phase position and momentum errors are bounded by R≥0.

**Objects:** Fixed original-input source/target cells centered by the true compliance congruence.

**Proof detail:** Rewrite the original point by the exact paired frame identity; control the transformed offset using the determinant-based phase-cell bound and the same position/momentum radius, with a sign change for targets.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=660), Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (spectral decomposition, determinant, definiteness, symmetric square root); [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662), Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T); [OTSelector project, Common-cut approximate momentum field and phase-cell envelopes](main.tex#degenerate-central-phase-envelope), main.tex label degenerate-central-phase-envelope, line 9561.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Deterministic original source cells in genuine coarse anisotropic coordinates

The marked center and physical spatial frame use the same compliance congruence.
Every bounded coarse phase pair therefore lands in its fixed original-input
source set; its count is still a count of the unchanged original input.
-/
open Set Function Matrix MeasureTheory
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pullback of a deterministic coarse phase center to the original source coordinate. -/
def coarsePhaseSourceCenter (T : Matrix ι ι ℝ) (ℓ : ℝ) (U : ℝ → Matrix ι ι ℝ)
    (k l : ι → ℝ) (a : ℝ) : ι → ℝ :=
  (ℓ • T⁻¹) *ᵥ (k - (T * U a * Tᵀ) *ᵥ l)

/-- Its marked center is Borel under exactly the original Borel compliance field. -/
theorem measurable_coarsePhaseSourceCenter (T : Matrix ι ι ℝ) (ℓ : ℝ)
    {U : ℝ → Matrix ι ι ℝ} (hU : Measurable U) (k l : ι → ℝ) :
    Measurable (coarsePhaseSourceCenter T ℓ U k l) := by
  have hV := measurable_phaseLegCongruence T hU
  have hm : Measurable (fun a ↦ (T * U a * Tᵀ) *ᵥ l) := by
    apply measurable_pi_lambda
    intro i
    exact Finset.measurable_sum _ (fun j _ ↦ (hV.eval.eval).mul measurable_const)
  exact (Matrix.toLin' (ℓ • T⁻¹)).continuous_of_finiteDimensional.measurable.comp
    (measurable_const.sub hm)

/-- A bounded coarse phase pair has its literal original source in the corresponding fixed
marked envelope. No alternative matching, metric, or endpoint is introduced. -/
theorem mk_coarse_source_mem_markedPhaseCell
    (T : Matrix ι ι ℝ) [Invertible T] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {U : ℝ → Matrix ι ι ℝ} (hU : ∀ a, (U a).PosSemidef)
    (k l : ι → ℝ) {B : Set ℝ} {a R : ℝ} (ha : a ∈ B) (hR : 0 ≤ R)
    {z p : ι → ℝ} (hz : ‖z - k‖ ≤ R) (hp : ‖p - l‖ ≤ R) :
    ((ℓ • T⁻¹) *ᵥ (z - (T * U a * Tᵀ) *ᵥ p), a) ∈
      markedPhaseSourceCell (ℓ • T⁻¹) (fun a ↦ T * U a * Tᵀ)
        (coarsePhaseSourceCenter T ℓ U k l) B R := by
  have h := mk_add_mulVec_sub_mem_markedPhaseSourceCell
    (isUnit_det_coarsePhaseFrame T hℓ) (fun a ↦ phaseLegCongruence_posSemidef T (hU a))
    (coarsePhaseSourceCenter T ℓ U k l) ha hR hz hp
  have heq : coarsePhaseSourceCenter T ℓ U k l a + (ℓ • T⁻¹) *ᵥ
      ((z - k) - (T * U a * Tᵀ) *ᵥ (p - l)) =
      (ℓ • T⁻¹) *ᵥ (z - (T * U a * Tᵀ) *ᵥ p) := by
    dsimp only [coarsePhaseSourceCenter]
    rw [← Matrix.mulVec_add]
    congr 1
    rw [Matrix.mulVec_sub]
    abel_nf
  rwa [heq] at h

/-- The paired normalized position/momentum reconstruct the unchanged physical source. -/
theorem original_source_mem_coarsePhaseCell
    (T : Matrix ι ι ℝ) [Invertible T] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {U : ℝ → Matrix ι ι ℝ} (hU : ∀ a, (U a).PosSemidef)
    (k l : ι → ℝ) {B : Set ℝ} {a R : ℝ} (ha : a ∈ B) (hR : 0 ≤ R)
    {z p : ι → ℝ} (hz : ‖ℓ⁻¹ • (T *ᵥ z) - k‖ ≤ R)
    (hp : ‖ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ p) - l‖ ≤ R) :
    (z - U a *ᵥ p, a) ∈
      markedPhaseSourceCell (ℓ • T⁻¹) (fun a ↦ T * U a * Tᵀ)
        (coarsePhaseSourceCenter T ℓ U k l) B R := by
  have h := mk_coarse_source_mem_markedPhaseCell T hℓ hU k l ha hR hz hp
  rwa [coarsePhaseFrame_source_identity T (U a) hℓ z p] at h

/-- The same normalized phase point reconstructs its unchanged physical target. -/
theorem original_target_mem_coarsePhaseCell
    (T : Matrix ι ι ℝ) [Invertible T] {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {V : ℝ → Matrix ι ι ℝ} (hV : ∀ a, (V a).PosSemidef)
    (k l : ι → ℝ) {B : Set ℝ} {b R : ℝ} (hb : b ∈ B) (hR : 0 ≤ R)
    {z p : ι → ℝ} (hz : ‖ℓ⁻¹ • (T *ᵥ z) - k‖ ≤ R)
    (hp : ‖ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ p) - l‖ ≤ R) :
    (z + V b *ᵥ p, b) ∈
      markedPhaseSourceCell (ℓ • T⁻¹) (fun b ↦ T * V b * Tᵀ)
        (coarsePhaseSourceCenter T ℓ V k (-l)) B R := by
  have hpneg : ‖ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ (-p)) - (-l)‖ ≤ R := by
    have heq : ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ (-p)) - (-l) =
        -(ℓ⁻¹ • ((Tᵀ)⁻¹ *ᵥ p) - l) := by
      rw [Matrix.mulVec_neg, smul_neg]
      abel_nf
    rw [heq, norm_neg]
    exact hp
  have h := original_source_mem_coarsePhaseCell T hℓ hV k (-l) hb hR hz hpneg
  simpa only [Matrix.mulVec_neg, sub_neg_eq_add] using h

end OTSelector.Reconstruction

end
end
