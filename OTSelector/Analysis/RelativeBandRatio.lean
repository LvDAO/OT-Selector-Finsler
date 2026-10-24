import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Analysis.RelativeBandRatio

Conditions: Positive a, relative perturbation |s-a|≤epsilon*a, with 0≤epsilon≤1/2.

Objects: The ratio a²/s² differs from one by at most ten epsilon.

Proof detail: The relative band yields a/2≤s≤3a/2; factor a²-s², bound its two factors and use the denominator lower bound.

## Mathematical sources

- [Stephen Boyd, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=85): Section 3.1.5, powers and geometric mean examples, pp. 71–73.

Source relation: Elementary band/ratio inequality; this is not a theorem about a geometric focal pole.
-/

/-! A fixed scalar bound on the genuine double-pole ratio in a relative time band. -/
namespace OTSelector.Reconstruction

/-- A relative time band of width ε≤1/2 stays positive and changes the double-pole
coefficient by at most 10ε. The fixed constant is independent of the endpoint distance. -/
theorem doublePole_ratio_relativeBand
    {a s ε : ℝ} (ha : 0<a) (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hband : |s-a|≤ε*a) :
    a/2≤s ∧ s≤3*a/2 ∧ |a^2/s^2-1|≤10*ε := by
  have hlo := (abs_le.mp hband).1
  have hhi := (abs_le.mp hband).2
  have hεa := mul_le_mul_of_nonneg_right hεhalf ha.le
  have hslo : a/2≤s := by linarith
  have hshi : s≤3*a/2 := by linarith
  have hs : 0<s := (half_pos ha).trans_le hslo
  refine ⟨hslo,hshi,?_⟩
  have hratio : a^2/s^2-1=(a^2-s^2)/s^2 := by field_simp
  rw [hratio,abs_div,abs_of_pos (sq_pos_of_pos hs)]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  have hfactor : |a^2-s^2|=|s-a| *(a+s) := by
    calc
      _ = |(a-s)*(a+s)| := by congr 1; ring
      _ = |s-a| *(a+s) := by rw [abs_mul,abs_of_pos (add_pos ha hs),abs_sub_comm]
  rw [hfactor]
  have hbound : |s-a| *(a+s)≤(ε*a)*(5*a/2) := by
    apply mul_le_mul hband
    · linarith
    · positivity
    · positivity
  have hsq : a^2≤4*s^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hε
  nlinarith

end OTSelector.Reconstruction
