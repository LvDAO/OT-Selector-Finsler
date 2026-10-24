import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Scaling identities for the block comparison

The grid-repair bound is stated at intensity `R` with the block count `m`; the
pressure comparison is stated at scale `L` with `R = (m L)^q`.  These are the
elementary real-power identities converting between the two forms.
-/

open scoped NNReal

noncomputable section
namespace OTSelector.Probability

/-- `(m L)^q / m^q = L^q`. -/
theorem mul_pow_div_pow (q m : ℕ) (hm : 0 < m) (L : ℝ) :
    (((m : ℝ) * L) ^ q) / ((m : ℝ) ^ q) = L ^ q := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [mul_pow]
  field_simp

/-- The kinetic exponent identity at scale `L`. -/
theorem rpow_div_mul_pow_kinetic (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (m : ℕ) (hm : 0 < m) :
    Real.rpow ((((m : ℝ) * L) ^ q) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) =
      Real.rpow L (2 - (q : ℝ) / 2) := by
  rw [mul_pow_div_pow q m hm L]
  rw [← Real.rpow_natCast L q]
  calc (L ^ (q : ℝ)) ^ (2 / (q : ℝ) - 1 / 2)
      = L ^ ((q : ℝ) * (2 / (q : ℝ) - 1 / 2)) :=
        (Real.rpow_mul hL.le _ _).symm
    _ = L ^ (2 - (q : ℝ) / 2) := by
        congr 1
        field_simp

/-- The probe exponent identity at scale `L`. -/
theorem rpow_div_mul_pow_probe (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (m : ℕ) (hm : 0 < m) :
    Real.rpow ((((m : ℝ) * L) ^ q) / ((m : ℝ) ^ q)) (-(1 / 2 : ℝ)) =
      Real.rpow L (-((q : ℝ) / 2)) := by
  rw [mul_pow_div_pow q m hm L]
  rw [← Real.rpow_natCast L q]
  calc (L ^ (q : ℝ)) ^ (-(1 / 2 : ℝ))
      = L ^ ((q : ℝ) * (-(1 / 2 : ℝ))) :=
        (Real.rpow_mul hL.le _ _).symm
    _ = L ^ (-((q : ℝ) / 2)) := by
        congr 1
        ring

end OTSelector.Probability
