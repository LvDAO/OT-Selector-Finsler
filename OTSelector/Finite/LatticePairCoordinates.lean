import OTSelector.Finite.LatticeWalkCodes
import OTSelector.Finite.LatticeWalkGeometry
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PhasePairCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PhasePairCoordinates`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.PhasePairCoordinates

**Conditions:** Finite position and momentum coordinate vectors of the same dimension.

**Objects:** Their literal concatenation in Fin(2q), projection indices and corresponding coordinates of phase-walk vertices.

**Proof detail:** Split a Fin(2q) index into its two q-coordinate blocks; simplification recovers each component and the coordinate supremum norm bounds either projected error by the full pair error.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Finite phase-animal counting in the high-dimensional localization proof](main.tex#eq:highd-phase-animal-tail), main.tex label eq:highd-phase-animal-tail, line 3267.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! # Literal position and momentum coordinates of finite phase candidates -/
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

/-- Position-coordinate inclusion into the doubled phase-coordinate space. -/
def phasePositionIndex (q : ℕ) (i : Fin q) : Fin (2 * q) := ⟨i, by omega⟩

/-- Momentum-coordinate inclusion into the same doubled space. -/
def phaseMomentumIndex (q : ℕ) (i : Fin q) : Fin (2 * q) := ⟨q + i, by omega⟩

/-- The actual ordered pair of position and momentum vectors in one coordinate vector. -/
def phasePairVector {q : ℕ} (z p : Fin q → ℝ) (k : Fin (2 * q)) : ℝ :=
  if h : (k : ℕ) < q then z ⟨k, h⟩ else p ⟨(k : ℕ) - q, by omega⟩

@[simp] theorem phasePairVector_position {q : ℕ} (z p : Fin q → ℝ) (i : Fin q) :
    phasePairVector z p (phasePositionIndex q i) = z i := by
  simp [phasePairVector, phasePositionIndex, i.isLt]

@[simp] theorem phasePairVector_momentum {q : ℕ} (z p : Fin q → ℝ) (i : Fin q) :
    phasePairVector z p (phaseMomentumIndex q i) = p i := by
  have hnot : ¬q + (i : ℕ) < q := by omega
  simp [phasePairVector, phaseMomentumIndex, hnot]

/-- The position center of a literal phase-code vertex. -/
def phaseWalkPosition {q m : ℕ} (code : PhaseWalkCode (2 * q) m) (n : ℕ) : Fin q → ℝ :=
  fun i ↦ phaseWalkVertex code n (phasePositionIndex q i)

/-- The momentum center of the same literal phase-code vertex. -/
def phaseWalkMomentum {q m : ℕ} (code : PhaseWalkCode (2 * q) m) (n : ℕ) : Fin q → ℝ :=
  fun i ↦ phaseWalkVertex code n (phaseMomentumIndex q i)

/-- Position distance is bounded by the actual joint phase distance. -/
theorem norm_position_sub_phaseWalkPosition_le {q m : ℕ}
    (z p : Fin q → ℝ) (code : PhaseWalkCode (2 * q) m) (n : ℕ) :
    ‖z - phaseWalkPosition code n‖ ≤ ‖phasePairVector z p - phaseWalkVertex code n‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [Pi.sub_apply, phaseWalkPosition, phasePairVector_position] using
    norm_le_pi_norm (phasePairVector z p - phaseWalkVertex code n) (phasePositionIndex q i)

/-- Momentum distance is bounded by the same joint phase distance. -/
theorem norm_momentum_sub_phaseWalkMomentum_le {q m : ℕ}
    (z p : Fin q → ℝ) (code : PhaseWalkCode (2 * q) m) (n : ℕ) :
    ‖p - phaseWalkMomentum code n‖ ≤ ‖phasePairVector z p - phaseWalkVertex code n‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [Pi.sub_apply, phaseWalkMomentum, phasePairVector_momentum] using
    norm_le_pi_norm (phasePairVector z p - phaseWalkVertex code n) (phaseMomentumIndex q i)

end OTSelector.Reconstruction

end
end
