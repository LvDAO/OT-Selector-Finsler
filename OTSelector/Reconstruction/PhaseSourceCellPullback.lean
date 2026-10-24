import OTSelector.LinearAlgebra.Matrix.PhaseCell
import OTSelector.LinearAlgebra.Matrix.PositiveLegInverseQuadratic
import OTSelector.LinearAlgebra.Matrix.QuadraticMomentumBound
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Matrix.PosDef

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











/-- Each fixed phase envelope is compact in the original source coordinates. -/
theorem isCompact_phaseSourceCell (U : Matrix ι ι ℝ) (R : ℝ) :
    IsCompact (phaseSourceCell U R) :=
  (isCompact_closedBall _ _).image (Matrix.toLin' (1 + U)).continuous_of_finiteDimensional

/-- The source envelope volume contains only the genuine positive-leg determinant. -/
theorem volume_phaseSourceCell {U : Matrix ι ι ℝ} (hU : U.PosSemidef) (R : ℝ) :
    volume (phaseSourceCell U R) = ENNReal.ofReal (1 + U).det *
      volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R)) := by
  have hlo : ((1 + U) - (1 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef := by
    simpa using hU
  have hpos := posDef_of_scalar_identity_lower_bound (by norm_num : (0 : ℝ) < 1) hlo
  rw [phaseSourceCell, Measure.addHaar_image_linearMap, LinearMap.det_toLin',
    abs_of_pos hpos.det_pos]

/-- An arbitrary deterministic spatial frame contributes exactly its own Jacobian. -/
theorem volume_linearImage_phaseSourceCell
    (L : Matrix ι ι ℝ) {U : Matrix ι ι ℝ} (hU : U.PosSemidef) (R : ℝ) :
    volume ((Matrix.toLin' L) '' phaseSourceCell U R) =
      ENNReal.ofReal |L.det| * ENNReal.ofReal (1 + U).det *
        volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R)) := by
  rw [Measure.addHaar_image_linearMap, LinearMap.det_toLin', volume_phaseSourceCell hU,
    mul_assoc]

end OTSelector.Reconstruction
