import OTSelector.Analysis.Calculus.OneSidedDerivative
import OTSelector.Analysis.Convex.ConcaveDifferentiability
import OTSelector.Analysis.Convex.ConcaveSecantBounds
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.CurriedMeanDifferentiability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.CurriedMeanDifferentiability`; the selected original proof blocks follow. -/
section

/-!
# Limit.CurriedMeanDifferentiability

**Conditions:** Finite concave means converge pointwise near zero; their opposite supergradients have the explicit sample-before-tilt curried vanishing gap.

**Objects:** The width of opposite secants and differentiability of the limiting pressure.

**Proof detail:** Bracket each mean’s secant width by the absolute supergradient gap, pass to the limit at each fixed tilt, then send the tilt to zero to identify its bounded monotone one-sided slope limits.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83), Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=149), Section 3.6, Proposition 3.6.2 and Corollary 3.6.4, pp. 149–151; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=155), Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Differentiability from the actual sample-before-tilt slope-gap bound

Opposite finite mean supergradients bound the finite left-minus-right secant
width by the expected absolute readout gap. At each fixed tilt, pointwise
mean convergence passes the width bound to the pressure. Curried vanishing
of the gap then identifies the limiting one-sided derivatives.
-/

open Set Function Filter
open scoped Topology

noncomputable section
namespace OTSelector

/-- Opposite finite-level supergradients bound the finite secant width by
their absolute difference, with no limit or differentiability hypothesis. -/
theorem mean_secant_width_le_abs_supergradient_gap
    (p : ℝ → ℝ) {t qp qn : ℝ} (ht : 0 < t)
    (hp : ∀ s, p s ≤ p t + qp * (s - t))
    (hn : ∀ s, p s ≤ p (-t) + qn * (s + t)) :
    (p 0 - p (-t)) / t - (p t - p 0) / t ≤ |qp - qn| := by
  have hpos := (intervalSlope_le_of_supergradient_pos ht hp).2
  have hneg := (leftSlope_le_of_supergradient_neg ht hn).1
  calc
    _ ≤ qn - qp := sub_le_sub hneg hpos
    _ ≤ |qn - qp| := le_abs_self _
    _ = |qp - qn| := abs_sub_comm _ _

/-- One actual positive tilt sequence and the whole curried expected gap
suffice for differentiability of a pointwise limiting concave mean pressure.
The original inner sample limit is taken at each fixed outer tilt. -/
theorem hasDerivAt_of_concave_mean_of_curry_supergradient_gap
    {ε : ℝ} (hε : 0 < ε) (pn : ℕ → ℝ → ℝ) (pressure : ℝ → ℝ)
    (hconc : ∀ n, ConcaveOn ℝ (Ioo (-ε) ε) (pn n))
    (hpt : ∀ s ∈ Ioo (-ε) ε,
      Tendsto (fun n ↦ pn n s) atTop (𝓝 (pressure s)))
    (t : ℕ → ℝ) (htpos : ∀ ℓ, 0 < t ℓ) (ht : Tendsto t atTop (𝓝 0))
    (qp qn gap : ℕ → ℕ → ℝ)
    (hp : ∀ ℓ n s, pn n s ≤ pn n (t ℓ) + qp ℓ n * (s - t ℓ))
    (hn : ∀ ℓ n s, pn n s ≤ pn n (-(t ℓ)) + qn ℓ n * (s + t ℓ))
    (hbound : ∀ ℓ n, |qp ℓ n - qn ℓ n| ≤ gap ℓ n)
    (hgap : Tendsto (fun p : ℕ × ℕ ↦ gap p.1 p.2)
      ((atTop : Filter ℕ).curry atTop) (𝓝 0)) :
    ∃ d : ℝ, HasDerivAt pressure d 0 := by
  have hconcP : ConcaveOn ℝ (Ioo (-ε) ε) pressure :=
    concaveOn_of_pointwise_tendsto hpt hconc
  let width : ℕ → ℝ := fun ℓ ↦
    (pressure 0 - pressure (-(t ℓ))) / t ℓ - (pressure (t ℓ) - pressure 0) / t ℓ
  have hsmall : ∀ᶠ ℓ in atTop, t ℓ < ε := ht.eventually (Iio_mem_nhds hε)
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hmem (ℓ : ℕ) (hℓ : t ℓ < ε) :
      t ℓ ∈ Ioo (-ε) ε ∧ -(t ℓ) ∈ Ioo (-ε) ε := by
    have hpos := htpos ℓ
    exact ⟨⟨by linarith, hℓ⟩, ⟨by linarith, by linarith⟩⟩
  have hwidth_nonneg (ℓ : ℕ) (hℓ : t ℓ < ε) : 0 ≤ width ℓ := by
    have hs := hconcP.slope_anti_adjacent (hmem ℓ hℓ).2 (hmem ℓ hℓ).1
      (by linarith [htpos ℓ] : -(t ℓ) < 0) (htpos ℓ)
    have hs' : (pressure (t ℓ) - pressure 0) / t ℓ ≤
        (pressure 0 - pressure (-(t ℓ))) / t ℓ := by
      simpa only [slope_def_field, sub_zero, zero_sub, neg_neg] using hs
    exact sub_nonneg.mpr hs'
  have hfinite_limit (ℓ : ℕ) (hℓ : t ℓ < ε) :
      Tendsto (fun n ↦ (pn n 0 - pn n (-(t ℓ))) / t ℓ -
        (pn n (t ℓ) - pn n 0) / t ℓ) atTop (𝓝 (width ℓ)) :=
    (((hpt 0 hzero).sub (hpt _ (hmem ℓ hℓ).2)).div_const (t ℓ)).sub
      (((hpt _ (hmem ℓ hℓ).1).sub (hpt 0 hzero)).div_const (t ℓ))
  have hfinite_bound (ℓ n : ℕ) :
      (pn n 0 - pn n (-(t ℓ))) / t ℓ - (pn n (t ℓ) - pn n 0) / t ℓ ≤ gap ℓ n :=
    (mean_secant_width_le_abs_supergradient_gap (pn n) (htpos ℓ) (hp ℓ n) (hn ℓ n)).trans
      (hbound ℓ n)
  have hwidth : Tendsto width atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hhalf : (0 : ℝ) < η / 2 := by positivity
    have hrows : ∀ᶠ ℓ in atTop, ∀ᶠ n in atTop, gap ℓ n < η / 2 :=
      eventually_curry_iff.mp (hgap.eventually (Iio_mem_nhds hhalf))
    filter_upwards [hsmall, hrows] with ℓ hℓ hgℓ
    have hw : width ℓ ≤ η / 2 :=
      le_of_tendsto (hfinite_limit ℓ hℓ)
        (hgℓ.mono fun n hgn ↦ (hfinite_bound ℓ n).trans hgn.le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hwidth_nonneg ℓ hℓ)]
    exact hw.trans_lt (by linarith)
  have htGT : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall htpos⟩
  have hright := tendsto_rightSecant hε hconcP
  have hleft := tendsto_leftSecant hε hconcP
  have hlim : Tendsto width atTop
      (𝓝 (sInf (leftSecant pressure '' Ioo 0 ε) -
        sSup (rightSecant pressure '' Ioo 0 ε))) :=
    (hleft.comp htGT).sub (hright.comp htGT)
  have heq := sub_eq_zero.mp (tendsto_nhds_unique hlim hwidth)
  refine ⟨sSup (rightSecant pressure '' Ioo 0 ε),
    hasDerivAt_of_tendsto_slope_pos_neg hright ?_⟩
  rw [← heq]
  exact hleft

end OTSelector

end
end
