import OTSelector.Geometry.Finsler.Jacobi.Pairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.LinearCotangentPhase.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.LinearCotangentPhase`; the selected original proof blocks follow. -/
section

/-!
Conditions: A continuous linear equivalence of the vector spaces.

Objects: Its linear cotangent phase lift and preservation of the canonical vector-covector pairing.

Proof detail: Map (x,p) to (Tx,p∘T inverse), construct the inverse explicitly and cancel T with its inverse in the two pairings.

Sources: Ana Cannas da Silva, Homework 1, Symplectic Linear Algebra, p. 8; Section 2.2, pp. 9–10 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=16); Ana Cannas da Silva, Section 2.4, Proposition 2.1 and Corollary 2.2, pp. 11–12 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=19).
Relation: Elementary linear version of cotangent naturality, proved directly for the stated normed spaces.
-/

/-!
# Linear cotangent changes of the original phase

A genuine linear change of position coordinates determines an invertible phase map.
Covectors use its inverse, preserving the canonical pairing exactly. This applies to
actual parameter and time derivatives because the same map is continuous linear.
-/

noncomputable section
namespace OTSelector.Geometry

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The position change and its inverse covector pullback as one phase equivalence. -/
def linearCotangentPhase (T : E ≃L[ℝ] G) :
    (E × (E →L[ℝ] ℝ)) ≃L[ℝ] (G × (G →L[ℝ] ℝ)) :=
  T.prodCongr (T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

/-- The phase equivalence uses the inverse position change on covectors. -/
theorem linearCotangentPhase_apply (T : E ≃L[ℝ] G) (z : E × (E →L[ℝ] ℝ)) :
    linearCotangentPhase T z = (T z.1, z.2.comp T.symm.toContinuousLinearMap) := by
  apply Prod.ext
  · rfl
  · ext w
    rfl

/-- The actual linear cotangent change preserves the canonical pairing exactly. -/
theorem linearCotangentPhase_pairing (T : E ≃L[ℝ] G)
    (u v : E × (E →L[ℝ] ℝ)) :
    canonicalPhasePairing (linearCotangentPhase T u) (linearCotangentPhase T v) =
      canonicalPhasePairing u v := by
  simp only [linearCotangentPhase_apply, canonicalPhasePairing,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

end OTSelector.Geometry

end
end
