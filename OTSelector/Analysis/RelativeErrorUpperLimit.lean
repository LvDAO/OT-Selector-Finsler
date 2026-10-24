import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Analysis.RelativeErrorUpperLimit

Conditions: A real reference family has the stated relative error upper comparison and the two errors are sufficiently small; the limiting reference is below the target upper bound.

Objects: An eventual strict upper bound on the compared values.

Proof detail: Absorb the small relative error to get a finite upper comparison, then choose positive error tolerances inside the given strict gap.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=62): Section 2.2, Lemma 2.2.3, p. 62; Section 2.3, Proposition 2.3.5, pp. 76–77.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation: Locally derived upper-limit stability under relative errors.
-/

/-! Relative geometric error preserves an original pressure upper limit.
Only a one-sided original law limit is needed; no pressure bound is assumed. -/
open Filter
open scoped Topology
namespace OTSelector.Reconstruction

/-- A vanishing relative original coefficient/probe error preserves the
actual pressure upper limit. The reference sequence supplies its own eventual
upper bound through that same original upper limit. -/
theorem eventually_pressure_lt_of_relative_error
    {J : Type*} (l : Filter J) (p r ε D : J → ℝ) (pref B : ℝ)
    (hε : Tendsto ε l (𝓝 0)) (hD : Tendsto D l (𝓝 0))
    (hε0 : ∀ j, 0 ≤ ε j)
    (hr : ∀ η > 0, ∀ᶠ j in l, r j < pref + η)
    (herror : ∀ j, |p j - r j| ≤ ε j * (r j + B) + D j) :
    ∀ η > 0, ∀ᶠ j in l, p j < pref + η := by
  intro η hη
  have hsmall : Tendsto (fun j ↦ ε j * (pref + 1 + B) + D j) l (𝓝 0) := by
    simpa only [zero_mul,zero_add] using (hε.mul_const (pref + 1 + B)).add hD
  have hsmall' : ∀ᶠ j in l, ε j * (pref + 1 + B) + D j < η / 2 :=
    (tendsto_order.mp hsmall).2 _ (half_pos hη)
  filter_upwards [hr 1 zero_lt_one,hr (η / 2) (half_pos hη),hsmall'] with j hj1 hjη hjerr
  have hrel := (abs_le.mp (herror j)).2
  have hmult := mul_le_mul_of_nonneg_left (add_le_add_right hj1.le B) (hε0 j)
  linarith only [hrel,hmult,hjη,hjerr]

/-- Arbitrarily small eventual relative original errors preserve the pressure
upper limit. This form accepts the actual compact geometric neighborhoods
directly, without inventing a prescribed error sequence. -/
theorem eventually_pressure_lt_of_small_relative_errors
    {J : Type*} (l : Filter J) (p r : J → ℝ) (pref B : ℝ)
    (hr : ∀ η > 0, ∀ᶠ j in l, r j < pref + η)
    (herror : ∀ ε > 0, ε ≤ 1 → ∀ D > 0,
      ∀ᶠ j in l, |p j - r j| ≤ ε * (r j + B) + D) :
    ∀ η > 0, ∀ᶠ j in l, p j < pref + η := by
  intro η hη
  let M := pref + 1 + B
  let ε := min 1 (η / (4 * (|M| + 1)))
  have hM : 0 < |M| + 1 := by positivity
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hη (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεsmall : ε * M ≤ η / 4 := by
    calc
      ε * M ≤ ε * (|M| + 1) := mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self M) (le_add_of_nonneg_right zero_le_one)) hε.le
      _ ≤ (η / (4 * (|M| + 1))) * (|M| + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
      _ = η / 4 := by field_simp [hM.ne']
  filter_upwards [hr 1 zero_lt_one,hr (η / 2) (half_pos hη),
    herror ε hε hε1 (η / 4) (by positivity)] with j hj1 hjη hjerr
  have hrel := (abs_le.mp hjerr).2
  have hbase : r j + B ≤ M := by dsimp only [M]; linarith only [hj1]
  have hmult := mul_le_mul_of_nonneg_left hbase hε.le
  linarith only [hrel,hmult,hεsmall,hjη]

end OTSelector.Reconstruction
