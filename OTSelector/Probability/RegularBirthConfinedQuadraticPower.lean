import Mathlib.Analysis.Real.Sqrt

/-! The actual regular-birth physical one-edge and scalar momentum bounds
produce the original same-band second moment coefficient without a focal pole. -/
noncomputable section
namespace OTSelector.Probability

/-- Physical `sqrt(s)` occupation and actual scalar `s I` momentum energy give
the precise regular-birth coefficient `K C² Cv q s² V_i`. -/
theorem regularBirth_confined_quadratic_power_bound
    {q : ℕ} {s C Cv K w z v : ℝ} (hs : 0 < s)
    (hCv : 0 ≤ Cv) (hK : 0 ≤ K) (hz0 : 0 ≤ z)
    (hw : w ≤ Cv) (hz : z ≤ (s * (q : ℝ)) * v) :
    K * (C * Real.sqrt s) ^ 2 * w * z ≤
      (K * C ^ 2 * Cv * (q : ℝ)) * s ^ 2 * v := by
  calc
    _ ≤ K * (C * Real.sqrt s) ^ 2 * Cv * z := by gcongr
    _ ≤ K * (C * Real.sqrt s) ^ 2 * Cv * ((s * (q : ℝ)) * v) := by gcongr
    _ = _ := by rw [mul_pow, Real.sq_sqrt hs.le]; ring

end OTSelector.Probability
