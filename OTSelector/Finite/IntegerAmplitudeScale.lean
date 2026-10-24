import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite.IntegerAmplitudeScale

## Lemma skeleton

* **Conditions:** A real amplitude at least the positive natural scale N, and a coefficient C≥1.

* **Objects:** A natural ceiling scale and explicit linear upper/lower amplitude bounds.

* **Proof detail:** Choose the natural ceiling of C times amplitude, use x≤ceil(x)<x+1, and absorb the additive one using amplitude≥1. The auxiliary coefficient is an explicit sum of nonnegative terms.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The coefficient and constants are local arithmetic choices; the source supplies the Archimedean integer approximation principle.
-/

/-! A natural covering scale is chosen from the actual canonical-curve
amplitude, with the exact linear upper bound needed for original counts. -/
noncomputable section
namespace OTSelector.Reconstruction

/-- The natural cover scale of the actual amplitude. -/
def canonicalPhaseIntegerScale (C amplitude : ℝ) : ℕ := Nat.ceil (C * amplitude)

/-- One explicit coefficient covers both the canonical root and speed constants. -/
def canonicalPhaseCurveScaleCoefficient (L ρ A : ℝ) : ℝ :=
  max 1 (max (2 * (ρ + 1)) (4 * (1 + L) * A))

theorem canonicalPhaseCurveScaleCoefficient_bounds (L ρ A : ℝ) :
    1 ≤ canonicalPhaseCurveScaleCoefficient L ρ A ∧
      2 * (ρ + 1) ≤ canonicalPhaseCurveScaleCoefficient L ρ A ∧
      4 * (1 + L) * A ≤ canonicalPhaseCurveScaleCoefficient L ρ A :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

/-- Above the retained natural threshold, the chosen integer lies in the
same all-scale event and costs at most a fixed multiple of actual amplitude. -/
theorem canonicalPhaseIntegerScale_spec {C amplitude : ℝ} {N : ℕ}
    (hC : 1 ≤ C) (hN : 1 ≤ N) (hamp : (N : ℝ) ≤ amplitude) :
    N ≤ canonicalPhaseIntegerScale C amplitude ∧
      C * amplitude ≤ (canonicalPhaseIntegerScale C amplitude : ℝ) ∧
      (canonicalPhaseIntegerScale C amplitude : ℝ) ≤ (C + 1) * amplitude := by
  have hNa : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha1 : 1 ≤ amplitude := hNa.trans hamp
  have ha0 : 0 ≤ amplitude := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hmul : amplitude ≤ C * amplitude := by nlinarith
  have hc := Nat.le_ceil (C * amplitude)
  have hupper := Nat.ceil_lt_add_one (mul_nonneg hC0 ha0)
  refine ⟨?_, hc, ?_⟩
  · exact_mod_cast hamp.trans (hmul.trans hc)
  · unfold canonicalPhaseIntegerScale
    nlinarith

end OTSelector.Reconstruction
