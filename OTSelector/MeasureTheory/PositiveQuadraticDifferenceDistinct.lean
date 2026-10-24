import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.MeasureTheory.AffineDerivativeAtomlessness
import OTSelector.MeasureTheory.PositiveQuadraticDifference
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerQuadraticCostDifferenceDistinct.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerQuadraticCostDifferenceDistinct`; the selected original proof blocks follow. -/
section

/-!
Conditions: Positive quadratic forms have distinct centers or distinct matrices, and the input measure is Haar absolutely continuous.

Objects: Nonconstancy and atomlessness of their difference.

Proof detail: Use center evaluations or polarization to rule out a constant difference, compute its affine derivative and use the null-fiber criterion.

Sources: Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); D. H. Fremlin, Theorem 472D, pp. 22–23 (Besicovitch Density Theorem) (https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22).
Relation: Elementary positive-quadratic algebra plus the locally proved differential atomlessness theorem.
-/

/-!
# Atomless quadratic differences for distinct centers or matrices

Positive symmetric quadratic rows remain distinguishable when two target
positions coincide but their actual clock coefficients differ. Polarization
recovers a symmetric matrix from its quadratic values.
-/
open Set Filter MeasureTheory Matrix
open scoped Topology
noncomputable section
namespace OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/-- Distinct positive symmetric quadratic matrices have different values on
some vector, by polarization in the original coordinate space. -/
theorem exists_matrixQuadratic_ne_of_posDef_ne
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≠ B) :
    ∃ v : ι → ℝ, Reconstruction.matrixQuadratic A v ≠
      Reconstruction.matrixQuadratic B v := by
  classical
  by_contra h
  push Not at h
  apply hAB
  apply Matrix.toBilin'.injective
  apply LinearMap.BilinForm.ext_of_isSymm
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (by simpa using hA.isHermitian))
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (by simpa using hB.isHermitian))
  intro v
  have hv := h v
  simp only [Reconstruction.matrixQuadratic] at hv
  simpa only [Matrix.toBilin'_apply'] using (by linarith :
    v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (B *ᵥ v))

/-- Distinct centers OR distinct actual positive matrices make the original
quadratic row difference atomless, including coincident spatial targets. -/
theorem nullSingletonClass_map_matrixQuadratic_sub_of_distinct
    (m : Measure (ι → ℝ)) [m.IsAddHaarMeasure]
    {μ : Measure (ι → ℝ)} (hμ : μ ≪ m)
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {y z : ι → ℝ} (hdistinct : y ≠ z ∨ A ≠ B) :
    NullSingletonClass (μ.map (fun x ↦
      Reconstruction.matrixQuadratic A (y - x) -
        Reconstruction.matrixQuadratic B (z - x))) := by
  classical
  by_cases hyz : y ≠ z
  · exact nullSingletonClass_map_matrixQuadratic_sub m hμ hA hB hyz
  have hyz' : y = z := not_ne_iff.mp hyz
  subst z
  have hAB : A ≠ B := hdistinct.resolve_left hyz
  obtain ⟨v, hv⟩ := exists_matrixQuadratic_ne_of_posDef_ne hA hB hAB
  let A' := A.toBilin'.toContinuousBilinearMap
  let B' := B.toBilin'.toContinuousBilinearMap
  let L := (1 / 2 : ℝ) • (A' + A'.flip)
  let K := (1 / 2 : ℝ) • (B' + B'.flip)
  have hh : NullSingletonClass (μ.map (fun x ↦
      (1 / 2 : ℝ) * A' (y - x) (y - x) -
        (1 / 2 : ℝ) * B' (y - x) (y - x))) := by
    apply nullSingletonClass_map_of_affine_fderiv m hμ (L - K) (K y - L y)
    · intro x
      have heq : (L - K) x + (K y - L y) = (L x - L y) - (K x - K y) := by
        rw [_root_.sub_apply]
        abel
      rw [heq]
      exact (hasFDerivAt_centered_bilinear_quadratic A' y x).sub
        (hasFDerivAt_centered_bilinear_quadratic B' y x)
    · refine ⟨y - v, y, ?_⟩
      simpa only [A', B', sub_sub_cancel, sub_self, map_zero,
        mul_zero, sub_zero, LinearMap.toContinuousBilinearMap_apply,
        Matrix.toBilin'_apply', Reconstruction.matrixQuadratic] using
        (sub_ne_zero.mpr hv)
  simpa only [A', B', LinearMap.toContinuousBilinearMap_apply,
    Matrix.toBilin'_apply', Reconstruction.matrixQuadratic] using hh

end OTSelector.Geometry

end
end
