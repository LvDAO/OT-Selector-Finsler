import OTSelector.Feedback.FeedbackRightBoundaryScalar

/-!
# The actual height at a frozen right boundary

Decode the revealed snapshot once and retain its measurable height for both
conditional-law and relative-VC continuation arguments.
-/

open MeasureTheory
open scoped NNReal

namespace OTSelector.FiniteSample

variable {n : ℕ}

/-- The actual frozen-tail height decoded from the revealed snapshot at the deterministic
boundary.  This definition remains meaningful on the exceptional samples as well. -/
noncomputable def actualRightTailHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)

theorem measurable_actualRightTailHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    Measurable (actualRightTailHeight (n := n) hlam0 hlamHalf x0 p0 T) :=
  (measurable_rightBoundaryFrozenHeight lam (x0 + (T : ℝ))).comp
    (measurable_revealedSnapshotAtElapsed (n := n) hlam0 hlamHalf x0 p0 T)

end OTSelector.FiniteSample
