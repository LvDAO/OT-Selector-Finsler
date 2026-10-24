import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Probability.IdentDistrib
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.OrthonormalFaceCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.OrthonormalFaceCoordinates`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual finite-dimensional orthonormal basis and one chosen normal index.

Objects: The explicit codimension-one face map and its exact orthogonal-hyperplane range.

Proof detail: Expand in the orthonormal basis, omit the normal coefficient and characterize zero normal pairing.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Terence Tao, Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61).
Relation: Elementary face-coordinate construction; no distributional boundary theorem is used.
-/

/-! Literal codimension-one box coordinates in an actual orthonormal frame. -/

open Set Function Submodule
open scoped InnerProductSpace BigOperators
noncomputable section
namespace OTSelector.Probability

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A face has one scalar coordinate for each basis vector except its normal.
Its box is therefore genuinely codimension one. -/
def orthonormalFaceMap (b : OrthonormalBasis ι ℝ E) (i : ι) :
    ({k : ι // k ≠ i} → ℝ) →ₗ[ℝ] E where
  toFun z := ∑ k, z k • b k.1
  map_add' z w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c z := by simp [mul_smul, Finset.smul_sum]

/-- These concrete face coordinates cover precisely the hyperplane
perpendicular to the chosen normal in the same orthonormal frame. -/
theorem range_orthonormalFaceMap (b : OrthonormalBasis ι ℝ E) (i : ι) :
    (orthonormalFaceMap b i).range = (ℝ ∙ b i)ᗮ := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.2
    change ⟪b i, ∑ k : {k : ι // k ≠ i}, z k • b k.1⟫_ℝ = 0
    simp only [inner_sum, inner_smul_right]
    apply Finset.sum_eq_zero
    intro k _
    rw [b.inner_eq_zero (Ne.symm k.property), mul_zero]
  · intro hx
    have hz : ⟪b i, x⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 hx
    refine ⟨fun k ↦ ⟪b k.1, x⟫_ℝ, ?_⟩
    change (∑ k : {k : ι // k ≠ i}, ⟪b k.1, x⟫_ℝ • b k.1) = x
    rw [← Finset.sum_subtype (p := fun k : ι ↦ k ≠ i)
      (Finset.univ.erase i) (by simp [ne_comm]) (fun k ↦ ⟪b k, x⟫_ℝ • b k)]
    have hsum := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun k ↦ ⟪b k, x⟫_ℝ • b k) (Finset.mem_univ i)
    rw [hz, zero_smul, add_zero] at hsum
    exact hsum.trans (b.sum_repr' x)

end OTSelector.Probability

end
end
