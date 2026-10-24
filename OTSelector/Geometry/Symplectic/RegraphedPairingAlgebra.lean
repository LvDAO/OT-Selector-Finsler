import OTSelector.Geometry.Finsler.Jacobi.Pairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.RegraphedPairingAlgebra.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.RegraphedPairingAlgebra`; the selected original proof blocks follow. -/
section

/-!
Conditions: The explicit graph-time correction and energy-tangent phase vectors with the stated canonical orthogonality and nonzero scale.

Objects: Preservation and rescaling of canonical pairings after regraphing.

Proof detail: Expand all four vector/covector pairings, cancel the energy-tangent cross terms and collect the longitudinal scale.

Sources: Ana Cannas da Silva, Homework 1, Symplectic Linear Algebra, p. 8; Section 2.2, pp. 9–10 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=16); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Direct algebraic regraphing identity; geometry is represented by the explicit algebraic premises.
-/

/-!
# Algebra of fixed-energy graph reduction

This module expresses the old-time correction explicitly and proves that,
for directions tangent to the same Hamiltonian energy level, the canonical pairing
of their reduced position/momentum directions is the original pairing divided by
old speed. The actual graph derivative and energy-tangency inputs must be derived
from the same original family before this algebra is applied.
-/

open scoped NNReal

noncomputable section
namespace OTSelector.Geometry.RegraphedPairing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual old-time correction's algebraic expression at fixed graph time. -/
def correctedPhase (X A : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) :
    (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ) :=
  A - (A.1.1 / X.1.1) • X

/-- Spatial position and old-speed-normalized momentum after that time correction. -/
def reducedPhase (X : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) (S : ℝ)
    (A : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) : V × (V →L[ℝ] ℝ) :=
  ((correctedPhase X A).1.2,
    S⁻¹ • (correctedPhase X A).2.comp (ContinuousLinearMap.inr ℝ ℝ V))

/-- Corrected position has zero graph-time component when longitudinal velocity is nonzero. -/
theorem correctedPhase_first_eq_zero
    (X A : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) (hX : X.1.1 ≠ 0) :
    (correctedPhase X A).1.1 = 0 := by
  change A.1.1 - (A.1.1 / X.1.1) * X.1.1 = 0
  rw [div_mul_cancel₀ _ hX, sub_self]

/-- The time correction preserves the pairing on the true energy-tangent directions. -/
theorem correctedPhase_pairing
    (X A B : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))
    (hA : canonicalPhasePairing X A = 0) (hB : canonicalPhasePairing X B = 0) :
    canonicalPhasePairing (correctedPhase X A) (correctedPhase X B) =
      canonicalPhasePairing A B := by
  have heq : canonicalPhasePairing (correctedPhase X A) (correctedPhase X B) =
      canonicalPhasePairing A B - (A.1.1 / X.1.1) * canonicalPhasePairing X B +
        (B.1.1 / X.1.1) * canonicalPhasePairing X A := by
    simp only [canonicalPhasePairing, correctedPhase, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, sub_apply,
      smul_apply, map_sub, map_smul, smul_eq_mul]
    ring
  rw [heq, hA, hB]
  ring

/-- The reduced pairing is original pairing divided by old speed; the algebra holds for any S. -/
theorem reducedPhase_pairing
    (X A B : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) (S : ℝ)
    (hX : X.1.1 ≠ 0)
    (hA : canonicalPhasePairing X A = 0) (hB : canonicalPhasePairing X B = 0) :
    canonicalPhasePairing (reducedPhase X S A) (reducedPhase X S B) =
      S⁻¹ * canonicalPhasePairing A B := by
  have hpos (Z : (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) :
      ((0 : ℝ), (correctedPhase X Z).1.2) = (correctedPhase X Z).1 :=
    Prod.ext (correctedPhase_first_eq_zero X Z hX).symm rfl
  change S⁻¹ * (correctedPhase X B).2 (0, (correctedPhase X A).1.2) -
    S⁻¹ * (correctedPhase X A).2 (0, (correctedPhase X B).1.2) = _
  rw [hpos A, hpos B, ← mul_sub]
  exact congrArg (fun r ↦ S⁻¹ * r) (correctedPhase_pairing X A B hA hB)

end OTSelector.Geometry.RegraphedPairing

end
end
