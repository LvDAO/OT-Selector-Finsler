import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.LinearAlgebra.Matrix.PositiveLegInverseQuadratic
import OTSelector.LinearAlgebra.Matrix.QuadraticMomentumBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PhaseSourceCellPullback.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PhaseSourceCellPullback`; the selected original proof blocks follow. -/
section

/-!
Conditions: A positive-semidefinite matrix and two norm-bounded vectors in the given finite coordinate norm.

Objects: The explicit phase-cell radius, inverse-(1+U) norm estimate and containment/equivalence formulas.

Proof detail: Use positivity to lower-bound identity plus U in Euclidean norm, compare with the finite-coordinate norm and rewrite the cell through its actual inverse matrix.

Sources: Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Elementary matrix/norm-comparison construction with its explicit dimension factor; no spectral pole hypothesis is used.
-/

/-!
# Deterministic original source envelopes for bounded phase cells

A bounded position-momentum cell pulls back through a positive compliance leg into
an explicit compact linear image. Its Haar volume has exactly one determinant
factor, including arbitrarily ill-conditioned or singular compliance legs.
-/
open Set Function Matrix MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A dimension-dependent radius containing the inverse image of a phase cell. -/
def phaseSourceCellRadius (ι : Type*) [Fintype ι] (R : ℝ) : ℝ :=
  (2 * (Fintype.card ι : ℝ) + 3) * R

/-- The deterministic source envelope is the image of one fixed coordinate ball. -/
def phaseSourceCell (U : Matrix ι ι ℝ) (R : ℝ) : Set (ι → ℝ) :=
  (Matrix.toLin' (1 + U)) '' Metric.closedBall 0 (phaseSourceCellRadius ι R)

private theorem norm_inverse_mulVec_le_of_identity_lower_bound
    {U : Matrix ι ι ℝ} (hU : U.PosSemidef) {R : ℝ} (hR : 0 ≤ R)
    {v : ι → ℝ} (hv : ‖v‖ ≤ 2 * R) :
    ‖(1 + U)⁻¹ *ᵥ v‖ ≤ 2 * ((Fintype.card ι : ℝ) + 1) * R := by
  have hlo : ((1 + U) - (1 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef := by
    simpa using hU
  have hp := posDef_of_scalar_identity_lower_bound (by norm_num : (0 : ℝ) < 1) hlo
  have hquad (w : ι → ℝ) :
      |matrixQuadratic (1 + U)⁻¹ w| ≤ (1 / 2 : ℝ) * ∑ i, w i ^ 2 := by
    have hn : 0 ≤ matrixQuadratic (1 + U)⁻¹ w := by
      apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      simpa only [star_trivial] using hp.inv.posSemidef.dotProduct_mulVec_nonneg w
    rw [abs_of_nonneg hn]
    simpa using matrixQuadratic_inverse_le_of_scalar_identity_lower_bound
      (by norm_num : (0 : ℝ) < 1) hlo w
  have hnorm := norm_mulVec_sq_le_quadratic_of_sum_bound hp.inv.posSemidef
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hquad v
  have henergy := (le_abs_self (matrixQuadratic (1 + U)⁻¹ v)).trans (hquad v)
  have hsum : (∑ i, v i ^ 2) ≤ (Fintype.card ι : ℝ) * (2 * R) ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, (2 * R) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |v i| ≤ 2 * R := (norm_le_pi_norm v i).trans hv
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2
      _ = _ := by simp
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have htarget : 0 ≤ 2 * ((Fintype.card ι : ℝ) + 1) * R := by positivity
  nlinarith [sq_nonneg (Fintype.card ι : ℝ), sq_nonneg R,
    mul_nonneg (sq_nonneg R) (sq_nonneg ((Fintype.card ι : ℝ) + 1)),
    norm_nonneg ((1 + U)⁻¹ *ᵥ v)]

/-- Every source of a bounded phase cell belongs to a fixed compact original-source set.
The set depends only on the deterministic compliance and cell radius. -/
theorem sub_mulVec_mem_phaseSourceCell
    {U : Matrix ι ι ℝ} (hU : U.PosSemidef) {R : ℝ} (hR : 0 ≤ R)
    {z p : ι → ℝ} (hz : ‖z‖ ≤ R) (hp : ‖p‖ ≤ R) :
    z - U *ᵥ p ∈ phaseSourceCell U R := by
  have hlo : ((1 + U) - (1 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef := by
    simpa using hU
  have hpos := posDef_of_scalar_identity_lower_bound (by norm_num : (0 : ℝ) < 1) hlo
  let _ := hpos.isUnit.invertible
  let y := (1 + U)⁻¹ *ᵥ (z + p) - p
  have hv : ‖z + p‖ ≤ 2 * R := (norm_add_le _ _).trans (by linarith)
  have hy : ‖y‖ ≤ phaseSourceCellRadius ι R := by
    calc
      _ ≤ ‖(1 + U)⁻¹ *ᵥ (z + p)‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ 2 * ((Fintype.card ι : ℝ) + 1) * R + R :=
        add_le_add (norm_inverse_mulVec_le_of_identity_lower_bound hU hR hv) hp
      _ = _ := by dsimp [phaseSourceCellRadius]; ring
  refine ⟨y, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  · change (1 + U) *ᵥ y = z - U *ᵥ p
    dsimp only [y]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    abel

/-- Membership is an explicit inverse-compliance inequality, suitable for measurable counts. -/
theorem mem_phaseSourceCell_iff {U : Matrix ι ι ℝ} (hU : U.PosSemidef)
    (R : ℝ) (x : ι → ℝ) :
    x ∈ phaseSourceCell U R ↔ ‖(1 + U)⁻¹ *ᵥ x‖ ≤ phaseSourceCellRadius ι R := by
  have hlo : ((1 + U) - (1 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef := by
    simpa using hU
  have hpos := posDef_of_scalar_identity_lower_bound (by norm_num : (0 : ℝ) < 1) hlo
  let _ := hpos.isUnit.invertible
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖(1 + U)⁻¹ *ᵥ ((1 + U) *ᵥ y)‖ ≤ _
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  · intro hx
    refine ⟨(1 + U)⁻¹ *ᵥ x, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    · change (1 + U) *ᵥ ((1 + U)⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]







end OTSelector.Reconstruction

end
end
