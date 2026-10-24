import OTSelector.Analysis.Calculus.OneSidedDerivative
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.ConcaveSecantBounds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.ConcaveSecantBounds`; the selected original proof blocks follow. -/
section

/-!
# Limit.ConcaveSecantBounds

**Conditions:** Real supergradient inequalities at opposite nonzero tilts, or explicit one-sided secant limits; no concavity is needed for the algebraic bounds themselves.

**Objects:** Adjacent interval slopes and right/left secants at zero.

**Proof detail:** Evaluate each supergradient at the neighboring endpoint and zero; express the adjacent interval slope as twice a dilated secant minus the original secant and identify common limits.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83), Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=155), Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Secant bounds from supergradients and interval slopes

The paper's differentiability argument reads the one-sided pressure slopes off
supergradients at opposite tilts.  This module isolates the elementary analytic
bookkeeping:

* a supergradient at a positive tilt `t` brackets the interval slope over
  `[t, 2t]` and the right secant slope at `t`;
* a supergradient at a negative tilt `-t` brackets the left secant slope at
  `t` and the interval slope over `[-2t, -t]`;
* the interval slopes over `[h, 2h]` and `[-2h, -h]` converge to the same
  limit as the corresponding one-sided secant slopes at zero.

None of these statements uses concavity: concavity enters only when it supplies
the supergradients (through optimality) or the existence of the one-sided
limits.  The final squeeze identifies the two one-sided derivatives once the
two supergradient families share a limit.
-/

open Filter Set Topology
open scoped Topology

noncomputable section
namespace OTSelector

/-- **Right supergradient brackets.**  If `q` is a supergradient of `p` at
`t > 0`, then the interval slope over `[t, 2t]` is at most `q` and `q` is at
most the right secant slope at `t`. -/
theorem intervalSlope_le_of_supergradient_pos {p : ℝ → ℝ} {t q : ℝ} (ht : 0 < t)
    (hsup : ∀ s, p s ≤ p t + q * (s - t)) :
    (p (2 * t) - p t) / t ≤ q ∧ q ≤ (p t - p 0) / t := by
  constructor
  · have h := hsup (2 * t)
    rw [div_le_iff₀ ht]
    linarith
  · have h := hsup 0
    rw [le_div_iff₀ ht]
    linarith

/-- **Left supergradient brackets.**  If `q` is a supergradient of `p` at
`-t` with `t > 0`, then the left secant slope at `t` is at most `q` and `q` is
at most the interval slope over `[-2t, -t]`. -/
theorem leftSlope_le_of_supergradient_neg {p : ℝ → ℝ} {t q : ℝ} (ht : 0 < t)
    (hsup : ∀ s, p s ≤ p (-t) + q * (s + t)) :
    (p 0 - p (-t)) / t ≤ q ∧ q ≤ (p (-t) - p (-(2 * t))) / t := by
  constructor
  · have h := hsup 0
    rw [div_le_iff₀ ht]
    linarith
  · have h := hsup (-(2 * t))
    rw [le_div_iff₀ ht]
    linarith

/-- **Right interval slopes inherit the one-sided limit.**  If the right
secant slopes at zero converge to `L`, then the slopes over `[h, 2h]` do too.
The proof is the identity `(p (2h) - p h)/h = 2 s(2h) - s(h)` for the secant
slope `s(h) = (p h - p 0)/h`. -/
theorem tendsto_intervalSlope_pos_of_tendsto_slope {p : ℝ → ℝ} {L : ℝ}
    (hslope : Tendsto (fun h : ℝ => (p h - p 0) / h) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun h : ℝ => (p (2 * h) - p h) / h) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have h2 : Tendsto (fun h : ℝ => 2 * h) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have hcont : Continuous fun h : ℝ => (2 : ℝ) * h :=
      continuous_const.mul continuous_id
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact mul_pos (show (0 : ℝ) < 2 from by norm_num) hh
  have hcomp : Tendsto (fun h : ℝ => (p (2 * h) - p 0) / (2 * h))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := hslope.comp h2
  have hcomb : Tendsto (fun h : ℝ =>
      2 * ((p (2 * h) - p 0) / (2 * h)) - (p h - p 0) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * L - L)) :=
    (hcomp.const_mul 2).sub hslope
  have hlim : (2 : ℝ) * L - L = L := by ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  field_simp
  ring

/-- **Left interval slopes inherit the one-sided limit.**  If the left secant
slopes `(p 0 - p (-h))/h` at zero converge to `L`, then the slopes over
`[-2h, -h]` do too, by the identity
`(p (-h) - p (-2h))/h = 2 s(2h) - s(h)` for `s(h) = (p 0 - p (-h))/h`. -/
theorem tendsto_intervalSlope_neg_of_tendsto_slope {p : ℝ → ℝ} {L : ℝ}
    (hslope : Tendsto (fun h : ℝ => (p 0 - p (-h)) / h) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun h : ℝ => (p (-h) - p (-(2 * h))) / h) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have h2 : Tendsto (fun h : ℝ => 2 * h) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have hcont : Continuous fun h : ℝ => (2 : ℝ) * h :=
      continuous_const.mul continuous_id
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact mul_pos (show (0 : ℝ) < 2 from by norm_num) hh
  have hcomp : Tendsto (fun h : ℝ => (p 0 - p (-(2 * h))) / (2 * h))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := hslope.comp h2
  have hcomb : Tendsto (fun h : ℝ =>
      2 * ((p 0 - p (-(2 * h))) / (2 * h)) - (p 0 - p (-h)) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * L - L)) :=
    (hcomp.const_mul 2).sub hslope
  have hlim : (2 : ℝ) * L - L = L := by ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  field_simp
  ring

/-- **Common interval-slope limit gives differentiability.**  Suppose the two
one-sided secant slopes at zero have (real) limits `Lp`, `Lm`, and along a
sequence `t n > 0` tending to zero the interval slopes over `[t n, 2 t n]` and
over `[-2 t n, - t n]` have a common limit `d`.  Then `Lp = Lm = d` and `p` is
differentiable at zero with derivative `d`.

This packages the final step of the paper's differentiability proof: the
one-sided derivative limits are read off from the tilted optima, and the
common diffuse representation supplies the common interval-slope limit. -/
theorem hasDerivAt_of_intervalSlope_tendsto {p : ℝ → ℝ} {t : ℕ → ℝ} {d Lp Lm : ℝ}
    (htpos : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 (0 : ℝ)))
    (hslopePos : Tendsto (fun h : ℝ => (p h - p 0) / h) (𝓝[>] (0 : ℝ)) (𝓝 Lp))
    (hslopeNeg : Tendsto (fun h : ℝ => (p 0 - p (-h)) / h) (𝓝[>] (0 : ℝ)) (𝓝 Lm))
    (hintervalPos : Tendsto (fun n : ℕ => (p (2 * t n) - p (t n)) / t n) atTop (𝓝 d))
    (hintervalNeg : Tendsto (fun n : ℕ => (p (-(t n)) - p (-(2 * t n))) / t n)
      atTop (𝓝 d)) :
    HasDerivAt p d 0 := by
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Filter.Eventually.of_forall htpos⟩
  have hpos := tendsto_intervalSlope_pos_of_tendsto_slope hslopePos
  have hneg := tendsto_intervalSlope_neg_of_tendsto_slope hslopeNeg
  have hpos' : Tendsto (fun n : ℕ => (p (2 * t n) - p (t n)) / t n) atTop (𝓝 Lp) :=
    hpos.comp ht'
  have hneg' : Tendsto (fun n : ℕ => (p (-(t n)) - p (-(2 * t n))) / t n) atTop (𝓝 Lm) :=
    hneg.comp ht'
  have hLp : Lp = d := tendsto_nhds_unique hpos' hintervalPos
  have hLm : Lm = d := tendsto_nhds_unique hneg' hintervalNeg
  subst hLp
  subst hLm
  exact hasDerivAt_of_tendsto_slope_pos_neg hslopePos hslopeNeg

end OTSelector

end
end
