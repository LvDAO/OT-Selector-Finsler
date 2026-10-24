import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! # The actual focal-birth, focal-old, and regular traffic index -/
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Birth pieces retain `(side, inward shell, elapsed shell)` and a finite
narrow-band sum. Old pieces retain `(side, physical inward shell)`. -/
abbrev OriginalClockTrafficPieceIndex :=
  ((Fin 2 × ℕ × ℕ) ⊕ (Fin 2 × ℕ)) ⊕ Fin 4

def originalFocalBirthRegionIndex (side : Fin 2) : Fin 8 :=
  ⟨4 * side.val, by have := side.isLt; omega⟩

def originalFocalOldRegionIndex (side : Fin 2) : Fin 8 :=
  ⟨4 * side.val + 2, by have := side.isLt; omega⟩

def originalRegularRegionIndex (i : Fin 4) : Fin 8 :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

/-- The unchanged original region containing each countable traffic piece. -/
def originalClockTrafficPieceRegionIndex : OriginalClockTrafficPieceIndex → Fin 8
  | .inl (.inl (side, _, _)) => originalFocalBirthRegionIndex side
  | .inl (.inr (side, _)) => originalFocalOldRegionIndex side
  | .inr i => originalRegularRegionIndex i

/-- The two birth, two old and four regular regions are exactly the original eight. -/
theorem sum_originalClockRegionIndex_partition (R : Fin 8 → ℝ≥0∞) :
    (∑ side : Fin 2, R (originalFocalBirthRegionIndex side)) +
      (∑ side : Fin 2, R (originalFocalOldRegionIndex side)) +
      (∑ i : Fin 4, R (originalRegularRegionIndex i)) = ∑ i : Fin 8, R i := by
  simp [Fin.sum_univ_succ, originalFocalBirthRegionIndex,
    originalFocalOldRegionIndex, originalRegularRegionIndex]
  change (R 0 + R 4) + (R 2 + R 6) + (R 1 + (R 3 + (R 5 + R 7))) =
    R 0 + (R 1 + (R 2 + (R 3 + (R 4 + (R 5 + (R 6 + R 7))))))
  ac_rfl

end OTSelector.Reconstruction
