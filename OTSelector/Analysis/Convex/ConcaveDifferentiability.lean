import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import OTSelector.Analysis.Calculus.OneSidedDerivative
import OTSelector.Analysis.Convex.ConcaveSecantBounds
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.ConcaveDifferentiability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.ConcaveDifferentiability`; the selected original proof blocks follow. -/
section

/-!
# Limit.ConcaveDifferentiability

**Conditions:** Real pressures are concave on an open interval; the supplied interval slopes or opposite supergradient gaps vanish under the stated tilt/error limits.

**Objects:** Monotone one-sided secants, their finite limits, and a common derivative; optional countable forbidden tilts are avoided.

**Proof detail:** Concavity brackets secants between fixed opposite slopes, giving bounded monotone limits; dilated interval identities identify the limits, while two-point errors cost 2δ/t and a square-root-scale tilt makes δ/t vanish.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83), Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=149), Section 3.6, Proposition 3.6.2 and Corollary 3.6.4, pp. 149–151; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=155), Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=42), Section 1.4, Theorem 1.4.2 (Cantor), p. 42; Section 1.5, Theorem 1.5.2, p. 46; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Differentiability of a concave pressure from interval slopes

The paper's differentiability theorem chooses a sequence of tilts `t n ↓ 0`,
brackets the one-sided pressure slopes between secant slopes over
`[t n, 2 t n]` and `[-2 t n, -t n]`, and concludes that the two one-sided
derivatives coincide.  This module supplies the analytic engine:

if `p` is concave near zero and the interval slopes over `[t n, 2 t n]` and
`[-2 t n, -t n]` share a limit `d`, then `p` is differentiable at zero with
derivative `d`.

The proof does not need differentiability or monotonicity of the approximating
pressures: concavity makes the right secant slopes antitone and the left secant
slopes monotone, and local continuity at zero bounds both.  The two monotone
limits exist by order completeness, and the interval-slope identities of
`ConcaveSecantBounds` identify them with the common limit `d`.
-/

open Filter Set Topology MeasureTheory
open scoped Topology

noncomputable section
namespace OTSelector

variable {p : ℝ → ℝ} {ε : ℝ}

/-- The right secant slope at zero. -/
noncomputable def rightSecant (p : ℝ → ℝ) (h : ℝ) : ℝ := (p h - p 0) / h

/-- The left secant slope at zero, written with a positive step. -/
noncomputable def leftSecant (p : ℝ → ℝ) (h : ℝ) : ℝ := (p 0 - p (-h)) / h

/-- Concavity makes the right secant slopes antitone. -/
theorem antitoneOn_rightSecant (hε : 0 < ε) (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p) :
    AntitoneOn (rightSecant p) (Ioo 0 ε) := by
  intro u hu v hv huv
  have hu0 : 0 < u := hu.1
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  rcases eq_or_lt_of_le huv with rfl | huv'
  · rfl
  have hmem0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hmemv : v ∈ Ioo (-ε) ε := ⟨by linarith, hv.2⟩
  have hslope := ConcaveOn.slope_anti_adjacent hconc hmem0 hmemv hu0 huv'
  have hweighted : rightSecant p v =
      (u / v) * rightSecant p u + ((v - u) / v) * ((p v - p u) / (v - u)) := by
    unfold rightSecant
    field_simp [hu0.ne', hv0.ne', (sub_pos.mpr huv').ne']
    ring
  rw [hweighted]
  have hpos : 0 ≤ (v - u) / v := div_nonneg (sub_nonneg.mpr huv) hv0.le
  calc
    (u / v) * rightSecant p u + ((v - u) / v) * ((p v - p u) / (v - u))
        ≤ (u / v) * rightSecant p u + ((v - u) / v) * rightSecant p u := by
          gcongr
          unfold rightSecant
          simpa using hslope
    _ = rightSecant p u := by
      unfold rightSecant
      field_simp [hv0.ne']
      ring

/-- Concavity makes the left secant slopes monotone. -/
theorem monotoneOn_leftSecant (hε : 0 < ε) (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p) :
    MonotoneOn (leftSecant p) (Ioo 0 ε) := by
  intro u hu v hv huv
  have hu0 : 0 < u := hu.1
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  rcases eq_or_lt_of_le huv with rfl | huv'
  · rfl
  have hmemv : (-v : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith [hv.2], by linarith [hv.2]⟩
  have hmem0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hslope := ConcaveOn.slope_anti_adjacent hconc hmemv hmem0
    (by linarith : -v < -u) (by linarith : -u < 0)
  have hweighted : leftSecant p v =
      (u / v) * leftSecant p u + ((v - u) / v) * ((p (-u) - p (-v)) / (v - u)) := by
    unfold leftSecant
    field_simp [hu0.ne', hv0.ne', (sub_pos.mpr huv').ne']
    ring
  have hpos : 0 ≤ (v - u) / v := div_nonneg (sub_nonneg.mpr huv) hv0.le
  have hterm : leftSecant p u ≤ (p (-u) - p (-v)) / (v - u) := by
    have h' := hslope
    have hden : -u - -v = v - u := by ring
    rw [hden] at h'
    simpa [leftSecant] using h'
  calc
    leftSecant p u = (u / v) * leftSecant p u + ((v - u) / v) * leftSecant p u := by
      field_simp [hv0.ne']
      ring
    _ ≤ (u / v) * leftSecant p u + ((v - u) / v) * ((p (-u) - p (-v)) / (v - u)) := by
      gcongr
    _ = leftSecant p v := hweighted.symm

/-- The right secant slopes are bounded above near zero: concavity bounds them
by the slope over a fixed interval ending at zero. -/
theorem bddAbove_rightSecant_image (hε : 0 < ε)
    (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p) :
    BddAbove (rightSecant p '' Ioo 0 ε) := by
  refine ⟨max ((p 0 - p (-(ε / 2))) / (ε / 2)) (rightSecant p (ε / 2)), ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  have hηmem : (ε / 2 : ℝ) ∈ Ioo 0 ε := ⟨by linarith, by linarith⟩
  by_cases hlt : h < ε / 2
  · have hmemneg : (-(ε / 2) : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    have hmemh : h ∈ Ioo (-ε) ε := ⟨by linarith [hh.1], hh.2⟩
    have hslope := ConcaveOn.slope_anti_adjacent hconc hmemneg hmemh
      (by linarith : -(ε / 2) < 0) hh.1
    have hbound : rightSecant p h ≤ (p 0 - p (-(ε / 2))) / (ε / 2) := by
      simpa [rightSecant] using hslope
    exact hbound.trans (le_max_left _ _)
  · have hle : ε / 2 ≤ h := le_of_not_gt hlt
    exact (antitoneOn_rightSecant hε hconc hηmem hh hle).trans (le_max_right _ _)

/-- The left secant slopes are bounded below near zero: concavity bounds them
by the slope over a fixed interval starting at zero. -/
theorem bddBelow_leftSecant_image (hε : 0 < ε)
    (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p) :
    BddBelow (leftSecant p '' Ioo 0 ε) := by
  refine ⟨min ((p (ε / 2) - p 0) / (ε / 2)) (leftSecant p (ε / 2)), ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  have hηmem : (ε / 2 : ℝ) ∈ Ioo 0 ε := ⟨by linarith, by linarith⟩
  by_cases hlt : h < ε / 2
  · have hmemnegh : (-h : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith [hh.2], by linarith [hh.1]⟩
    have hmemη : (ε / 2 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    have hslope := ConcaveOn.slope_anti_adjacent hconc hmemnegh hmemη
      (by linarith [hh.1] : -h < 0) (by linarith : (0 : ℝ) < ε / 2)
    have hbound : (p (ε / 2) - p 0) / (ε / 2) ≤ leftSecant p h := by
      simpa [leftSecant] using hslope
    exact (min_le_left _ _).trans hbound
  · have hle : ε / 2 ≤ h := le_of_not_gt hlt
    exact (min_le_right _ _).trans (monotoneOn_leftSecant hε hconc hηmem hh hle)

/-- The right secant slopes have a limit at zero, equal to their supremum. -/
theorem tendsto_rightSecant (hε : 0 < ε) (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p) :
    Tendsto (rightSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) :=
  AntitoneOn.tendsto_nhdsWithin_Ioo_right
    ⟨ε / 2, by linarith, by linarith⟩
    (antitoneOn_rightSecant hε hconc)
    (bddAbove_rightSecant_image hε hconc)

/-- The left secant slopes have a limit at zero, equal to their infimum. -/
theorem tendsto_leftSecant (hε : 0 < ε) (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p) :
    Tendsto (leftSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_right
    ⟨ε / 2, by linarith, by linarith⟩
    (monotoneOn_leftSecant hε hconc)
    (bddBelow_leftSecant_image hε hconc)

/-- **Differentiability of a concave pressure from interval slopes.**  If `p`
is concave near zero and, along a sequence `t n > 0` tending to zero, the
interval slopes over `[t n, 2 t n]` and `[-2 t n, -t n]` share a limit `d`,
then `p` is differentiable at zero with derivative `d`.

This is the final analytic step of the paper's differentiability proof: the
interval slopes are supplied by the opposite-tilt optima, and the common
diffuse representation makes their two limits coincide. -/
theorem hasDerivAt_of_concave_intervalSlope_tendsto {p : ℝ → ℝ} {ε d : ℝ}
    (hε : 0 < ε) (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p)
    {t : ℕ → ℝ} (htpos : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 (0 : ℝ)))
    (hintervalPos : Tendsto (fun n : ℕ => (p (2 * t n) - p (t n)) / t n) atTop (𝓝 d))
    (hintervalNeg : Tendsto (fun n : ℕ => (p (-(t n)) - p (-(2 * t n))) / t n)
      atTop (𝓝 d)) :
    HasDerivAt p d 0 := by
  have hsr : Tendsto (rightSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) :=
    tendsto_rightSecant (p := p) hε hconc
  have hsl : Tendsto (leftSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) :=
    tendsto_leftSecant (p := p) hε hconc
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Filter.Eventually.of_forall htpos⟩
  have h1 : Tendsto (fun n : ℕ => (p (2 * t n) - p (t n)) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hsr' : Tendsto (fun h : ℝ => (p h - p 0) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
      show Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsr
    exact (tendsto_intervalSlope_pos_of_tendsto_slope hsr').comp ht'
  have h2 : Tendsto (fun n : ℕ => (p (-(t n)) - p (-(2 * t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hsl' : Tendsto (fun h : ℝ => (p 0 - p (-h)) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
      show Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsl
    exact (tendsto_intervalSlope_neg_of_tendsto_slope hsl').comp ht'
  have hLp : sSup (rightSecant p '' Ioo 0 ε) = d := tendsto_nhds_unique h1 hintervalPos
  have hLm : sInf (leftSecant p '' Ioo 0 ε) = d := tendsto_nhds_unique h2 hintervalNeg
  have hsr2 : Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    rw [← hLp]; exact hsr
  have hsl2 : Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    rw [← hLm]; exact hsl
  refine hasDerivAt_of_tendsto_slope_pos_neg ?_ ?_
  · show Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d)
    exact hsr2
  · show Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d)
    exact hsl2


/-- A uniform error bound of `δ` on two functions at `0` and `t` bounds the
difference of their right secant slopes at `t` by `2 δ / t`. -/
theorem abs_rightSecant_sub_le_two_mul_div {f g : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < t) (hft : |f t - g t| ≤ δ) (hf0 : |f 0 - g 0| ≤ δ) :
    |rightSecant f t - rightSecant g t| ≤ 2 * δ / t := by
  unfold rightSecant
  rw [← sub_div, abs_div, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  calc
    |(f t - f 0) - (g t - g 0)| = |(f t - g t) - (f 0 - g 0)| := by ring_nf
    _ ≤ |f t - g t| + |f 0 - g 0| := abs_sub _ _
    _ ≤ δ + δ := add_le_add hft hf0
    _ = 2 * δ := by ring

/-- The same bound for the left secant slopes. -/
theorem abs_leftSecant_sub_le_two_mul_div {f g : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < t) (hft : |f (-t) - g (-t)| ≤ δ) (hf0 : |f 0 - g 0| ≤ δ) :
    |leftSecant f t - leftSecant g t| ≤ 2 * δ / t := by
  unfold leftSecant
  rw [← sub_div, abs_div, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  calc
    |(f 0 - f (-t)) - (g 0 - g (-t))| = |(f 0 - g 0) - (f (-t) - g (-t))| := by ring_nf
    _ ≤ |f 0 - g 0| + |f (-t) - g (-t)| := abs_sub _ _
    _ ≤ δ + δ := add_le_add hf0 hft
    _ = 2 * δ := by ring

/-- A uniform error bound bounds the difference of the interval slopes over
`[t, 2t]` by `2 δ / t`. -/
theorem abs_intervalSlope_sub_le_two_mul_div {f g : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < t) (hft2 : |f (2 * t) - g (2 * t)| ≤ δ) (hft : |f t - g t| ≤ δ) :
    |(f (2 * t) - f t) / t - (g (2 * t) - g t) / t| ≤ 2 * δ / t := by
  rw [← sub_div, abs_div, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  calc
    |(f (2 * t) - f t) - (g (2 * t) - g t)|
        = |(f (2 * t) - g (2 * t)) - (f t - g t)| := by ring_nf
    _ ≤ |f (2 * t) - g (2 * t)| + |f t - g t| := abs_sub _ _
    _ ≤ δ + δ := add_le_add hft2 hft
    _ = 2 * δ := by ring

/-- The same bound for the interval slopes over `[-2t, -t]`. -/
theorem abs_intervalSlopeNeg_sub_le_two_mul_div {f g : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < t) (hft : |f (-t) - g (-t)| ≤ δ)
    (hft2 : |f (-(2 * t)) - g (-(2 * t))| ≤ δ) :
    |(f (-t) - f (-(2 * t))) / t - (g (-t) - g (-(2 * t))) / t| ≤ 2 * δ / t := by
  rw [← sub_div, abs_div, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  calc
    |(f (-t) - f (-(2 * t))) - (g (-t) - g (-(2 * t)))|
        = |(f (-t) - g (-t)) - (f (-(2 * t)) - g (-(2 * t)))| := by ring_nf
    _ ≤ |f (-t) - g (-t)| + |f (-(2 * t)) - g (-(2 * t))| := abs_sub _ _
    _ ≤ δ + δ := add_le_add hft hft2
    _ = 2 * δ := by ring

/-- **Finite-level supergradients give differentiability of the limit.**  Let
`p` be concave near zero and let `p n` approximate `p` uniformly with error
`δ n`, where `δ n / t n → 0`.  Suppose `q⁺ n` and `q⁻ n` are bracketed by the
right and left secant data at `± t n`:
`interval⁺ ≤ q⁺ ≤ rightSecant`, `leftSecant ≤ q⁻ ≤ interval⁻`, and both
sequences converge to `d`.  Then `p` is differentiable at zero with derivative
`d`.

This is the paper's differentiability argument reduced to its final form: the
uniform error is `o(t n)`, the probes of the opposite tilted optima supply the
brackets, and the common diffuse representation gives the common limit. -/
theorem hasDerivAt_of_concave_supergradient_sequence {p : ℝ → ℝ} {pn : ℕ → ℝ → ℝ}
    {δ : ℕ → ℝ} {t qpos qneg : ℕ → ℝ} {ε d : ℝ}
    (hε : 0 < ε) (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p)
    (hconv : ∀ n, ∀ s ∈ Ioo (-ε) ε, |pn n s - p s| ≤ δ n)
    (hδ : Tendsto (fun n => δ n / t n) atTop (𝓝 0))
    (htpos : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 (0 : ℝ)))
    (htsmall : ∀ᶠ n in atTop, 2 * t n < ε)
    (hposLow : ∀ᶠ n in atTop,
      (pn n (2 * t n) - pn n (t n)) / t n ≤ qpos n)
    (hposHigh : ∀ᶠ n in atTop,
      qpos n ≤ (pn n (t n) - pn n 0) / t n)
    (hnegLow : ∀ᶠ n in atTop,
      (pn n 0 - pn n (-(t n))) / t n ≤ qneg n)
    (hnegHigh : ∀ᶠ n in atTop,
      qneg n ≤ (pn n (-(t n)) - pn n (-(2 * t n))) / t n)
    (hqpos : Tendsto qpos atTop (𝓝 d)) (hqneg : Tendsto qneg atTop (𝓝 d)) :
    HasDerivAt p d 0 := by
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Filter.Eventually.of_forall htpos⟩
  have hsr : Tendsto (rightSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := tendsto_rightSecant hε hconc
  have hsl : Tendsto (leftSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := tendsto_leftSecant hε hconc
  -- The `p`-interval slopes and `p`-secant slopes along `t n`.
  have hIP : Tendsto (fun n => (p (2 * t n) - p (t n)) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hsr' : Tendsto (fun h : ℝ => (p h - p 0) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
      show Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsr
    exact (tendsto_intervalSlope_pos_of_tendsto_slope hsr').comp ht'
  have hRS : Tendsto (fun n => (p (t n) - p 0) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hsr' : Tendsto (fun h : ℝ => (p h - p 0) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
      show Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsr
    exact hsr'.comp ht'
  have hIL : Tendsto (fun n => (p (-(t n)) - p (-(2 * t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hsl' : Tendsto (fun h : ℝ => (p 0 - p (-h)) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
      show Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsl
    exact (tendsto_intervalSlope_neg_of_tendsto_slope hsl').comp ht'
  have hLS : Tendsto (fun n => (p 0 - p (-(t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hsl' : Tendsto (fun h : ℝ => (p 0 - p (-h)) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
      show Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsl
    exact hsl'.comp ht'
  -- Eventual membership of `t n` and `2 t n` in the concavity interval.
  have hmem (n : ℕ) (hsmall : 2 * t n < ε) : t n ∈ Ioo (-ε) ε ∧
      2 * t n ∈ Ioo (-ε) ε ∧ (-(t n) : ℝ) ∈ Ioo (-ε) ε ∧
      (-(2 * t n) : ℝ) ∈ Ioo (-ε) ε := by
    have ht0 := htpos n
    have h2t : 0 < 2 * t n := by positivity
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hsmall⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  -- Convergence of the finite-level secant data to the `p` data.
  have hIPn : Tendsto (fun n => (pn n (2 * t n) - pn n (t n)) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n (2 * t n) - pn n (t n)) / t n - (p (2 * t n) - p (t n)) / t n)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨hmemt, h2mem, -, -⟩ := hmem n hn
        have h1 := hconv n (2 * t n) h2mem
        have h2 := hconv n (t n) hmemt
        have hbd := abs_intervalSlope_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h2
        simpa only [Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hIP.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  have hRSn : Tendsto (fun n => (pn n (t n) - pn n 0) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n (t n) - pn n 0) / t n - (p (t n) - p 0) / t n) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨hmemt, -, -, -⟩ := hmem n hn
        have h1 := hconv n (t n) hmemt
        have h0 := hconv n 0 ⟨by linarith, hε⟩
        have hbd := abs_rightSecant_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h0
        simpa only [rightSecant, Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hRS.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  have hILn : Tendsto (fun n => (pn n (-(t n)) - pn n (-(2 * t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n (-(t n)) - pn n (-(2 * t n))) / t n -
          (p (-(t n)) - p (-(2 * t n))) / t n) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨-, -, hmemn, hmemn2⟩ := hmem n hn
        have h1 := hconv n (-(t n)) hmemn
        have h2 := hconv n (-(2 * t n)) hmemn2
        have hbd := abs_intervalSlopeNeg_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h2
        simpa only [Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hIL.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  have hLSn : Tendsto (fun n => (pn n 0 - pn n (-(t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n 0 - pn n (-(t n))) / t n - (p 0 - p (-(t n))) / t n) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨-, -, hmemn, -⟩ := hmem n hn
        have h1 := hconv n (-(t n)) hmemn
        have h0 := hconv n 0 ⟨by linarith, hε⟩
        have hbd := abs_leftSecant_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h0
        simpa only [leftSecant, Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hLS.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  -- The two-sided squeeze of the common limit.
  have hLp_le : sSup (rightSecant p '' Ioo 0 ε) ≤ d :=
    le_of_tendsto_of_tendsto hIPn hqpos hposLow
  have hd_le : d ≤ sSup (rightSecant p '' Ioo 0 ε) :=
    le_of_tendsto_of_tendsto hqpos hRSn hposHigh
  have hLm_le : sInf (leftSecant p '' Ioo 0 ε) ≤ d :=
    le_of_tendsto_of_tendsto hLSn hqneg hnegLow
  have hd_le_Lm : d ≤ sInf (leftSecant p '' Ioo 0 ε) :=
    le_of_tendsto_of_tendsto hqneg hILn hnegHigh
  have hLp : sSup (rightSecant p '' Ioo 0 ε) = d := le_antisymm hLp_le hd_le
  have hLm : sInf (leftSecant p '' Ioo 0 ε) = d := le_antisymm hLm_le hd_le_Lm
  have hsr2 : Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    rw [← hLp]; exact hsr
  have hsl2 : Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    rw [← hLm]; exact hsl
  refine hasDerivAt_of_tendsto_slope_pos_neg ?_ ?_
  · show Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d)
    exact hsr2
  · show Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) (𝓝 d)
    exact hsl2

/-- A pointwise limit of concave functions is concave. -/
theorem concaveOn_of_pointwise_tendsto {s : Set ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hconv : ∀ t ∈ s, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hconc : ∀ n, ConcaveOn ℝ s (f n)) :
    ConcaveOn ℝ s g := by
  have hconvex : Convex ℝ s := (hconc 0).1
  refine ⟨hconvex, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hx' := hconv x hx
  have hy' := hconv y hy
  have hxy' := hconv (a * x + b * y) (hconvex hx hy ha hb hab)
  have hlim : Tendsto (fun n => a * f n x + b * f n y) atTop
      (𝓝 (a * g x + b * g y)) :=
    (hx'.const_mul a).add (hy'.const_mul b)
  have hineq : ∀ n, a * f n x + b * f n y ≤ f n (a * x + b * y) := by
    intro n
    simpa only [smul_eq_mul] using (hconc n).2 hx hy ha hb hab
  exact le_of_tendsto_of_tendsto hlim hxy' (Filter.Eventually.of_forall hineq)

/-- **Slowing down a vanishing error.**  Given nonnegative errors `δ n → 0`, there
is a sequence of positive tilts `t n → 0` with `δ n / t n → 0`: take
`t n = sqrt (δ n + 1/(n+1))`.  This is the paper's choice of tilts decreasing
slowly enough that the uniform pressure error is `o(t n)`. -/
theorem exists_tilt_tendsto_zero_of_error_tendsto_zero {δ : ℕ → ℝ}
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto (fun n => δ n / t n) atTop (𝓝 0) := by
  let t : ℕ → ℝ := fun n => Real.sqrt (δ n + 1 / (n + 1 : ℝ))
  have htpos : ∀ n, 0 < t n := by
    intro n
    exact Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (hδ0 n) (by positivity : (0 : ℝ) < 1 / (n + 1)))
  have ht : Tendsto t atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => δ n + 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
      have := hδ.add tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this
    have := Real.continuous_sqrt.continuousAt.tendsto.comp hbase
    simpa only [t, Function.comp_def, Real.sqrt_zero] using this
  have hratio : Tendsto (fun n => δ n / t n) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
      div_nonneg (hδ0 n) (le_of_lt (htpos n)))
      (Filter.Eventually.of_forall fun n => ?_) ht
    have hpos := htpos n
    rw [div_le_iff₀ hpos]
    have hsq : t n * t n = δ n + 1 / (n + 1 : ℝ) := by
      exact Real.mul_self_sqrt
        (add_nonneg (hδ0 n) (by positivity : (0 : ℝ) ≤ 1 / (n + 1)))
    rw [hsq]
    have : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
    linarith
  exact ⟨t, htpos, ht, hratio⟩

/-- A nondegenerate real interval is not contained in a countable set. -/
theorem exists_mem_Icc_notMem_countable {a b : ℝ} (hab : a < b) (C : Set ℝ)
    (hC : C.Countable) : ∃ x ∈ Icc a b, x ∉ C := by
  by_contra h
  push Not at h
  have hsub : Icc a b ⊆ C := h
  have h0 : volume (Icc a b) = 0 := measure_mono_null hsub (hC.measure_zero volume)
  have hne : volume (Icc a b) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)
  exact hne h0

/-- **Slow tilts avoiding a countable exceptional set.**  Given vanishing errors
`δ`, there is a positive tilt sequence `t → 0` with `δ n / t n → 0` that avoids
both `B` and `-B`.  The proof shrinks each term of the construction
`exists_tilt_tendsto_zero_of_error_tendsto_zero` by at most a factor of two into
the complement of the countable set. -/
theorem exists_tilt_tendsto_zero_of_error_tendsto_zero_avoiding {δ : ℕ → ℝ}
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (B : Set ℝ) (hB : B.Countable) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto (fun n => δ n / t n) atTop (𝓝 0) ∧
      (∀ n, t n ∉ B) ∧ (∀ n, -t n ∉ B) := by
  obtain ⟨t₀, ht₀pos, ht₀, hratio₀⟩ :=
    exists_tilt_tendsto_zero_of_error_tendsto_zero hδ0 hδ
  let C : Set ℝ := B ∪ Neg.neg '' B
  have hC : C.Countable := hB.union (hB.image Neg.neg)
  have hex : ∀ n, ∃ t : ℝ, t ∈ Icc (t₀ n / 2) (t₀ n) ∧ t ∉ C := by
    intro n
    exact exists_mem_Icc_notMem_countable (by linarith [ht₀pos n]) C hC
  choose t ht_mem ht_notC using hex
  have htpos : ∀ n, 0 < t n := fun n =>
    lt_of_lt_of_le (by linarith [ht₀pos n]) (ht_mem n).1
  have ht_le : ∀ n, t n ≤ t₀ n := fun n => (ht_mem n).2
  have ht_ge : ∀ n, t₀ n / 2 ≤ t n := fun n => (ht_mem n).1
  have ht : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun n => le_of_lt (htpos n)) ht_le ht₀
  have hratio : Tendsto (fun n => δ n / t n) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => 2 * (δ n / t₀ n)) atTop (𝓝 0) := by
      simpa using hratio₀.const_mul 2
    refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
      div_nonneg (hδ0 n) (le_of_lt (htpos n))) ?_ hupper
    filter_upwards with n
    have hpos := htpos n
    rw [div_le_iff₀ hpos]
    have hnonneg : 0 ≤ 2 * (δ n / t₀ n) :=
      mul_nonneg (by norm_num) (div_nonneg (hδ0 n) (le_of_lt (ht₀pos n)))
    have hstep : 2 * (δ n / t₀ n) * (t₀ n / 2) = δ n := by
      field_simp [ne_of_gt (ht₀pos n)]
    have hmono : 2 * (δ n / t₀ n) * (t₀ n / 2) ≤ 2 * (δ n / t₀ n) * t n := by
      gcongr
      exact ht_ge n
    linarith
  have hB' : ∀ n, t n ∉ B := by
    intro n hn
    exact ht_notC n (Or.inl hn)
  have hBneg : ∀ n, -t n ∉ B := by
    intro n hn
    exact ht_notC n (Or.inr ⟨-t n, hn, neg_neg (t n)⟩)
  exact ⟨t, htpos, ht, hratio, hB', hBneg⟩

/-- **Common supergradient differences force differentiability.**  The same
finite-level squeeze as `hasDerivAt_of_concave_supergradient_sequence`, but the
stochastic input is only that the two opposite-tilt probe costs share a limit:
`qpos n - qneg n → 0`.  The common one-sided limit is then produced by the
concavity squeeze. -/
theorem hasDerivAt_of_concave_supergradient_sequence_of_diff {p : ℝ → ℝ} {pn : ℕ → ℝ → ℝ}
    {δ : ℕ → ℝ} {t qpos qneg : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hconc : ConcaveOn ℝ (Ioo (-ε) ε) p)
    (hconv : ∀ n, ∀ s ∈ Ioo (-ε) ε, |pn n s - p s| ≤ δ n)
    (hδ : Tendsto (fun n => δ n / t n) atTop (𝓝 0))
    (htpos : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 (0 : ℝ)))
    (htsmall : ∀ᶠ n in atTop, 2 * t n < ε)
    (hposLow : ∀ᶠ n in atTop,
      (pn n (2 * t n) - pn n (t n)) / t n ≤ qpos n)
    (hposHigh : ∀ᶠ n in atTop,
      qpos n ≤ (pn n (t n) - pn n 0) / t n)
    (hnegLow : ∀ᶠ n in atTop,
      (pn n 0 - pn n (-(t n))) / t n ≤ qneg n)
    (hnegHigh : ∀ᶠ n in atTop,
      qneg n ≤ (pn n (-(t n)) - pn n (-(2 * t n))) / t n)
    (hdiff : Tendsto (fun n => qpos n - qneg n) atTop (𝓝 0)) :
    ∃ d : ℝ, HasDerivAt p d 0 := by
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Filter.Eventually.of_forall htpos⟩
  have hsr : Tendsto (rightSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := tendsto_rightSecant hε hconc
  have hsl : Tendsto (leftSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := tendsto_leftSecant hε hconc
  -- The `p`-interval slopes and `p`-secant slopes along `t n`.
  have hIP : Tendsto (fun n => (p (2 * t n) - p (t n)) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hsr' : Tendsto (fun h : ℝ => (p h - p 0) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
      show Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsr
    exact (tendsto_intervalSlope_pos_of_tendsto_slope hsr').comp ht'
  have hRS : Tendsto (fun n => (p (t n) - p 0) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hsr' : Tendsto (fun h : ℝ => (p h - p 0) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
      show Tendsto (rightSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsr
    exact hsr'.comp ht'
  have hIL : Tendsto (fun n => (p (-(t n)) - p (-(2 * t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hsl' : Tendsto (fun h : ℝ => (p 0 - p (-h)) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
      show Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsl
    exact (tendsto_intervalSlope_neg_of_tendsto_slope hsl').comp ht'
  have hLS : Tendsto (fun n => (p 0 - p (-(t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hsl' : Tendsto (fun h : ℝ => (p 0 - p (-h)) / h) (𝓝[>] (0 : ℝ))
        (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
      show Tendsto (leftSecant p) (𝓝[>] (0 : ℝ)) _
      exact hsl
    exact hsl'.comp ht'
  -- Eventual membership of `t n` and `2 t n` in the concavity interval.
  have hmem (n : ℕ) (hsmall : 2 * t n < ε) : t n ∈ Ioo (-ε) ε ∧
      2 * t n ∈ Ioo (-ε) ε ∧ (-(t n) : ℝ) ∈ Ioo (-ε) ε ∧
      (-(2 * t n) : ℝ) ∈ Ioo (-ε) ε := by
    have ht0 := htpos n
    have h2t : 0 < 2 * t n := by positivity
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hsmall⟩,
      ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  -- Convergence of the finite-level secant data to the `p` data.
  have hIPn : Tendsto (fun n => (pn n (2 * t n) - pn n (t n)) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n (2 * t n) - pn n (t n)) / t n - (p (2 * t n) - p (t n)) / t n)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨hmemt, h2mem, -, -⟩ := hmem n hn
        have h1 := hconv n (2 * t n) h2mem
        have h2 := hconv n (t n) hmemt
        have hbd := abs_intervalSlope_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h2
        simpa only [Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hIP.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  have hRSn : Tendsto (fun n => (pn n (t n) - pn n 0) / t n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n (t n) - pn n 0) / t n - (p (t n) - p 0) / t n) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨hmemt, -, -, -⟩ := hmem n hn
        have h1 := hconv n (t n) hmemt
        have h0 := hconv n 0 ⟨by linarith, hε⟩
        have hbd := abs_rightSecant_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h0
        simpa only [rightSecant, Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hRS.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  have hILn : Tendsto (fun n => (pn n (-(t n)) - pn n (-(2 * t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n (-(t n)) - pn n (-(2 * t n))) / t n -
          (p (-(t n)) - p (-(2 * t n))) / t n) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨-, -, hmemn, hmemn2⟩ := hmem n hn
        have h1 := hconv n (-(t n)) hmemn
        have h2 := hconv n (-(2 * t n)) hmemn2
        have hbd := abs_intervalSlopeNeg_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h2
        simpa only [Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hIL.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  have hLSn : Tendsto (fun n => (pn n 0 - pn n (-(t n))) / t n) atTop
      (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) := by
    have hdiff : Tendsto (fun n =>
        (pn n 0 - pn n (-(t n))) / t n - (p 0 - p (-(t n))) / t n) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun n => 2 * (δ n / t n)) ?_ ?_
      · filter_upwards [htsmall] with n hn
        obtain ⟨-, -, hmemn, -⟩ := hmem n hn
        have h1 := hconv n (-(t n)) hmemn
        have h0 := hconv n 0 ⟨by linarith, hε⟩
        have hbd := abs_leftSecant_sub_le_two_mul_div (f := pn n) (g := p)
          (δ := δ n) (t := t n) (htpos n) h1 h0
        simpa only [leftSecant, Real.norm_eq_abs, mul_div_assoc] using hbd
      · have h2 : Tendsto (fun n => 2 * (δ n / t n)) atTop (𝓝 (2 * 0)) :=
          hδ.const_mul 2
        simpa only [mul_zero] using h2
    have := hLS.add hdiff
    simpa only [add_sub_cancel, add_zero] using this
  -- The common one-sided limit from the difference hypothesis.
  have hqpos : Tendsto qpos atTop (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hIPn hRSn hposLow hposHigh
  have hqneg : Tendsto qneg atTop (𝓝 (sInf (leftSecant p '' Ioo 0 ε))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hLSn hILn hnegLow hnegHigh
  have hlim : Tendsto (fun n => qpos n - qneg n) atTop
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε) - sInf (leftSecant p '' Ioo 0 ε))) :=
    hqpos.sub hqneg
  have hzero : sSup (rightSecant p '' Ioo 0 ε) - sInf (leftSecant p '' Ioo 0 ε) = 0 :=
    tendsto_nhds_unique hlim hdiff
  have heq : sSup (rightSecant p '' Ioo 0 ε) = sInf (leftSecant p '' Ioo 0 ε) := by
    linarith
  have hsl2 : Tendsto (leftSecant p) (𝓝[>] (0 : ℝ))
      (𝓝 (sSup (rightSecant p '' Ioo 0 ε))) := by
    have hL : sInf (leftSecant p '' Ioo 0 ε) = sSup (rightSecant p '' Ioo 0 ε) := heq.symm
    rwa [hL] at hsl
  exact ⟨_, hasDerivAt_of_tendsto_slope_pos_neg hsr hsl2⟩

end OTSelector

end
end
