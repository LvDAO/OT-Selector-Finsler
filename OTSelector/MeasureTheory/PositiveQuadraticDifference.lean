import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.MeasureTheory.AffineDerivativeAtomlessness
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerQuadraticCostDifference.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerQuadraticCostDifference`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two positive quadratic forms have distinct centers and the stated actual affine differential; the source law is absolutely continuous with respect to Haar.

Objects: Opposite-sign values, nonconstant quadratic difference and atomless pushforward.

Proof detail: Evaluate the difference at its two centers, derive nonconstancy, and apply the affine-gradient/density-point null-fiber criterion.

Sources: Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22).
Relation: Elementary positive-form algebra combined with the locally proved density-point atomlessness criterion.
-/

/-!
# Atomless differences of frozen positive quadratic transport costs

Two positive quadratic forms centered at distinct target positions have a
nonconstant difference: its values at the two targets have opposite signs.
Its derivative is affine, so every level set is Haar null. The matrices may
differ, as they do for targets with different marks in the Finsler model.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a translated quadratic is affine, without imposing
symmetry on the continuous bilinear representative. -/
theorem hasFDerivAt_centered_bilinear_quadratic
    (B : E →L[ℝ] E →L[ℝ] ℝ) (y x : E) :
    HasFDerivAt (fun z ↦ (1 / 2 : ℝ) * B (y - z) (y - z))
      (((1 / 2 : ℝ) • (B + B.flip)) x -
        ((1 / 2 : ℝ) • (B + B.flip)) y) x := by
  have hd := (B.hasFDerivAt_of_bilinear
    ((hasFDerivAt_const y x).sub (hasFDerivAt_id x))
    ((hasFDerivAt_const y x).sub (hasFDerivAt_id x))).const_mul (1 / 2 : ℝ)
  have heq : (((1 / 2 : ℝ) • (B + B.flip)) x -
      ((1 / 2 : ℝ) • (B + B.flip)) y) =
      (1 / 2 : ℝ) • (B.precompR E (y - x) (0 - ContinuousLinearMap.id ℝ E) +
        B.precompL E (0 - ContinuousLinearMap.id ℝ E) (y - x)) := by
    ext v
    change (1 / 2 : ℝ) * (B x v + B v x) - (1 / 2 : ℝ) * (B y v + B v y) =
      (1 / 2 : ℝ) * (B (y - x) (0 - v) + B (0 - v) (y - x))
    simp only [zero_sub, map_sub, map_neg, sub_apply, neg_apply]
    ring
  rw [heq]
  exact hd

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Distinct centers and positive diagonal evaluations make the difference of
two possibly different quadratic forms atomless for every Haar-continuous law. -/
theorem nullSingletonClass_map_centered_quadratic_sub
    (m : Measure E) [m.IsAddHaarMeasure] {μ : Measure E} (hμ : μ ≪ m)
    (A B : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ v ≠ 0, 0 < A v v) (hB : ∀ v ≠ 0, 0 < B v v)
    {y z : E} (hyz : y ≠ z) :
    NullSingletonClass (μ.map (fun x ↦
      (1 / 2 : ℝ) * A (y - x) (y - x) - (1 / 2 : ℝ) * B (z - x) (z - x))) := by
  let L := (1 / 2 : ℝ) • (A + A.flip)
  let K := (1 / 2 : ℝ) • (B + B.flip)
  apply nullSingletonClass_map_of_affine_fderiv m hμ (L - K) (K z - L y)
  · intro x
    have heq : (L - K) x + (K z - L y) = (L x - L y) - (K x - K z) := by
      rw [sub_apply]
      abel
    rw [heq]
    exact (hasFDerivAt_centered_bilinear_quadratic A y x).sub
      (hasFDerivAt_centered_bilinear_quadratic B z x)
  · refine ⟨y, z, ?_⟩
    have hAz := hA (y - z) (sub_ne_zero.mpr hyz)
    have hBy := hB (z - y) (sub_ne_zero.mpr hyz.symm)
    simp only [sub_self, map_zero, mul_zero,
      zero_sub, sub_zero]
    linarith

variable {ι : Type*} [Fintype ι]

/-- The literal one-half matrix quadratic convention used by the original
Finsler coefficient has atomless distinct-target differences. -/
theorem nullSingletonClass_map_matrixQuadratic_sub
    (m : Measure (ι → ℝ)) [m.IsAddHaarMeasure] {μ : Measure (ι → ℝ)} (hμ : μ ≪ m)
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {y z : ι → ℝ} (hyz : y ≠ z) :
    NullSingletonClass (μ.map (fun x ↦
      Reconstruction.matrixQuadratic A (y - x) -
        Reconstruction.matrixQuadratic B (z - x))) := by
  classical
  have hA' (v : ι → ℝ) (hv : v ≠ 0) : 0 < A.toBilin'.toContinuousBilinearMap v v := by
    simpa only [LinearMap.toContinuousBilinearMap_apply, Matrix.toBilin'_apply',
      star_trivial] using hA.dotProduct_mulVec_pos hv
  have hB' (v : ι → ℝ) (hv : v ≠ 0) : 0 < B.toBilin'.toContinuousBilinearMap v v := by
    simpa only [LinearMap.toContinuousBilinearMap_apply, Matrix.toBilin'_apply',
      star_trivial] using hB.dotProduct_mulVec_pos hv
  simpa only [LinearMap.toContinuousBilinearMap_apply, Matrix.toBilin'_apply',
    Reconstruction.matrixQuadratic] using
    nullSingletonClass_map_centered_quadratic_sub m hμ
      A.toBilin'.toContinuousBilinearMap B.toBilin'.toContinuousBilinearMap hA' hB' hyz

end OTSelector.Geometry

end
end
