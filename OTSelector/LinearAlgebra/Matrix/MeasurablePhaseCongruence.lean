import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedPhaseCellCongruence.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedPhaseCellCongruence`; the selected original proof blocks follow. -/
section

/-!
Conditions: A fixed matrix and a measurable matrix family, or a positive-semidefinite matrix for the positivity conclusion.

Objects: Measurability and positive semidefiniteness of T U T transpose.

Proof detail: Matrix multiplication is continuous/measurable; pull the quadratic form back by T transpose to preserve positivity.

Sources: Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Elementary congruence/readout adapters, not a residue or focal asymptotic claim.
-/

/-!
# Original marked phase-cell intensities under anisotropic compliance normalization

The same fixed real frame acts on the actual compliance by congruence. Its
marked source-cell intensity is bounded by a frame-dependent finite multiple of
the unchanged original determinant envelope, without an additional moment.
-/
open Set Function Matrix MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Fixed congruence preserves Borel dependence on original clock marks. -/
theorem measurable_phaseLegCongruence (T : Matrix ι ι ℝ)
    {U : ℝ → Matrix ι ι ℝ} (hU : Measurable U) :
    Measurable (fun a ↦ T * U a * Tᵀ) := by
  have hcont : Continuous (fun A : Matrix ι ι ℝ ↦ T * A * Tᵀ) := by fun_prop
  exact hcont.measurable.comp hU

omit [DecidableEq ι] in
/-- Every deterministic spatial normalization preserves positivity of the actual leg. -/
theorem phaseLegCongruence_posSemidef (T : Matrix ι ι ℝ)
    {U : Matrix ι ι ℝ} (hU : U.PosSemidef) : (T * U * Tᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hU.mul_mul_conjTranspose_same T



end OTSelector.Reconstruction

end
end
