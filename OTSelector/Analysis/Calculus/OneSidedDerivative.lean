import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.LeftRight

/-!
# Analysis.Calculus.OneSidedDerivative

Conditions: A real function has lower and upper bounds on its positive and negative secant quotients, with the prescribed common finite limit.

Objects: Signed neighborhood changes, squeeze limits, and a genuine HasDerivAt at zero.

Proof detail: Reflect the negative half-line into the positive one, apply squeeze to each secant, then join the two punctured half-neighborhood limits.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=155): Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean): Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation: Direct consequences of the derivative definition and squeeze, with Lean filter bookkeeping.
-/

/-!
# Two-sided differentiability from one-sided secant limits

A function of one real variable is differentiable at a point as soon as the
right secants `(P h - P 0) / h` and the left secants `(P 0 - P (-h)) / h` have
the same limit as `h ↓ 0`.  This is the abstract form of the pressure secant
argument: opposite tilted optima supply the two signs.
-/

open Filter Set Topology
open scoped Topology

namespace OTSelector

/-- Negation maps the right neighborhood at zero to the left one. -/
theorem tendsto_neg_nhdsGT_zero : Tendsto (fun y : ℝ ↦ -y) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [mem_Iio, neg_zero] using neg_lt_zero.mpr hy

/-- Negation maps the left neighborhood at zero to the right one. -/
theorem tendsto_neg_nhdsLT_zero : Tendsto (fun y : ℝ ↦ -y) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [mem_Ioi, neg_zero] using neg_pos.mpr hy

/-- A function is differentiable at zero with derivative `d` when both one-sided
secant families converge to `d`. -/
theorem hasDerivAt_of_tendsto_slope_pos_neg {P : ℝ → ℝ} {d : ℝ}
    (hpos : Tendsto (fun h : ℝ ↦ (P h - P 0) / h) (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hneg : Tendsto (fun h : ℝ ↦ (P 0 - P (-h)) / h) (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    HasDerivAt P d 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have hleft := hneg.comp tendsto_neg_nhdsLT_zero
    refine hleft.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Function.comp_apply, neg_neg, slope, sub_zero, smul_eq_mul]
    rw [div_neg, vsub_eq_sub]
    ring
  · have hright := hpos
    refine hright.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope, sub_zero, smul_eq_mul]
    rw [div_eq_inv_mul, vsub_eq_sub]

/-- Squeeze a function between two functions with the same limit. -/
theorem tendsto_of_squeeze {S L U : ℝ → ℝ} {d : ℝ}
    (hlo : ∀ᶠ h in 𝓝[>] (0 : ℝ), L h ≤ S h)
    (hhi : ∀ᶠ h in 𝓝[>] (0 : ℝ), S h ≤ U h)
    (hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hU : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 d) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU hlo hhi

/-- Squeeze the right secant quotients between two functions with the same limit. -/
theorem tendsto_slope_of_squeeze {P L U : ℝ → ℝ} {d : ℝ}
    (hlo : ∀ᶠ h in 𝓝[>] (0 : ℝ), L h ≤ (P h - P 0) / h)
    (hhi : ∀ᶠ h in 𝓝[>] (0 : ℝ), (P h - P 0) / h ≤ U h)
    (hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hU : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    Tendsto (fun h : ℝ ↦ (P h - P 0) / h) (𝓝[>] (0 : ℝ)) (𝓝 d) :=
  tendsto_of_squeeze hlo hhi hL hU

set_option maxHeartbeats 800000 in
/-- Two-sided differentiability from squeezed one-sided secants at every tilt. -/
theorem hasDerivAt_of_squeeze_pos_neg {P Lpos Upos Lneg Uneg : ℝ → ℝ} {d : ℝ}
    (hlo_pos : ∀ᶠ h in 𝓝[>] (0 : ℝ), Lpos h ≤ (P h - P 0) / h)
    (hhi_pos : ∀ᶠ h in 𝓝[>] (0 : ℝ), (P h - P 0) / h ≤ Upos h)
    (hlo_neg : ∀ᶠ h in 𝓝[>] (0 : ℝ), Lneg h ≤ (P 0 - P (-h)) / h)
    (hhi_neg : ∀ᶠ h in 𝓝[>] (0 : ℝ), (P 0 - P (-h)) / h ≤ Uneg h)
    (hLpos : Tendsto Lpos (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hUpos : Tendsto Upos (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hLneg : Tendsto Lneg (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hUneg : Tendsto Uneg (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    HasDerivAt P d 0 :=
  hasDerivAt_of_tendsto_slope_pos_neg
    (tendsto_slope_of_squeeze hlo_pos hhi_pos hLpos hUpos)
    (tendsto_of_squeeze (S := fun h : ℝ ↦ (P 0 - P (-h)) / h)
      hlo_neg hhi_neg hLneg hUneg)

end OTSelector
