import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Analysis.RelativeErrorConvergence

Conditions: A real reference family satisfies a relative absolute error inequality with epsilon<1 and the stated vanishing epsilon and additive error.

Objects: An explicit rearranged absolute error bound and convergence to the reference value.

Proof detail: First bound the unknown reference by moving its epsilon multiple to the left. Substitute this bound into the original error and apply limit/squeeze.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=62): Section 2.2, Lemma 2.2.3, p. 62; Section 2.3, Proposition 2.3.5, pp. 76–77.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation: Elementary relative-error rearrangement; no independent boundedness assumption on the reference family is added.
-/

/-! Relative pressure errors identify a convergent finite-class approximation
without assuming a separate uniform bound on its unknown pressure values. -/
open Set Function Filter
open scoped Topology
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The reference pressure on the right side of a relative error estimate is
eliminated algebraically using the same error itself. -/
theorem abs_pressure_sub_le_of_relative_error {p pref ε B D : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (herror : |p - pref| ≤ ε * (pref + B) + D) :
    |p - pref| ≤ (ε * (p + B) + D) / (1 - ε) := by
  have hpref : pref ≤ p + |p - pref| := by
    have h := neg_le_abs (p - pref)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hpref hε0
  apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
  nlinarith only [herror,hmul]

/-- Vanishing relative coefficient and probe errors force convergence to the
same original pressure, without an extra pressure-boundedness assumption. -/
theorem tendsto_pressure_of_relative_error
    {J : Type*} (l : Filter J) (pref ε D : J → ℝ) (p B : ℝ)
    (hε : Tendsto ε l (𝓝 0)) (hD : Tendsto D l (𝓝 0))
    (herror : ∀ᶠ j in l, 0 ≤ ε j ∧ ε j < 1 ∧
      |p - pref j| ≤ ε j * (pref j + B) + D j) :
    Tendsto pref l (𝓝 p) := by
  have hb : Tendsto (fun j ↦ (ε j * (p + B) + D j) / (1 - ε j)) l (𝓝 0) := by
    have h := ((hε.mul_const (p + B)).add hD).div
      (tendsto_const_nhds.sub hε) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    change Tendsto (fun j ↦ (ε j * (p + B) + D j) / (1 - ε j)) l
      (𝓝 ((0 * (p + B) + 0) / (1 - 0))) at h
    simpa only [zero_mul,zero_add,sub_zero,zero_div] using h
  apply tendsto_iff_dist_tendsto_zero.mpr
  have ha : Tendsto (fun j ↦ |p - pref j|) l (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _) _ hb
    filter_upwards [herror] with j hj
    exact abs_pressure_sub_le_of_relative_error hj.1 hj.2.1 hj.2.2
  simpa only [Real.dist_eq,abs_sub_comm] using ha

end OTSelector.Reconstruction
