import OTSelector.Analysis.Convex.ConcaveDifferentiability
import OTSelector.Analysis.Convex.ConcaveSecantBounds
import OTSelector.Analysis.Convex.LocallyUniformConcave
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.PressureDifferentiabilityAssembly.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.PressureDifferentiabilityAssembly`; the selected original proof blocks follow. -/
section

/-!
# Analysis.Convex.PressureDifferentiabilityAssembly

Conditions: Real concave functions on an open interval, pointwise convergence, and explicit opposite-tilt supergradient hypotheses. The avoiding form additionally specifies a countable exceptional set.
Objects: Finite concave functions, their limiting function, vanishing positive tilts and two supergradient sequences; output is existence of a derivative at zero.
Proof detail: Choose a local uniform error and a tilt dominating it, bracket opposite supergradients by secant slopes, then squeeze. The common-limit and unrestricted forms reduce to the avoiding difference form.

## Mathematical sources

- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Section Differentiability from a common diffuse representation, Theorem thm:highd-pressure-differentiability; closing opposite-tilt supergradient/secant squeeze. ../main.tex#L4573
- Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)*: Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits. https://www.jirka.org/ra/realanal.pdf#page=155
- Terence Tao, *Analysis I*: Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test). https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean

Source relation: A generic analytic extraction of the manuscript argument. The precise sequence/exception-set API is a local generalization; the book supplies the derivative and squeeze principles, not this exact assembled theorem.
-/

/-!
# Assembling the differentiability squeeze

This module combines the three analytic ingredients of the paper's
differentiability-at-zero argument into one theorem:

* local uniform convergence of the concave finite-level pressures
  (`exists_delta_of_pointwise_tendsto_concave`);
* the diagonal tilt selection making the uniform error `o(t)`
  (`exists_tilt_tendsto_zero_of_error_tendsto_zero`);
* supergradient brackets at the opposite tilts `±t` with probe costs sharing a
  common limit (`hasDerivAt_of_concave_supergradient_sequence`).

The resulting statement takes pointwise convergence and concavity as concrete
hypotheses, and isolates the genuinely stochastic input as `hsup`: for *any*
vanishing positive tilt sequence, opposite tilted optima exist and their probe
costs converge to a common value along that sequence.
-/

open Filter Set Topology
open scoped Topology

noncomputable section
namespace OTSelector

/-- **Differentiability with tilts avoiding a countable exceptional set.**
The stochastic input only has to hold for tilt sequences that avoid both `B` and
`-B`; this matches the countable set of tilts at which tilted cost differences
may be atomic. -/
theorem hasDerivAt_of_concave_pointwise_tendsto_of_supergradient_diff_avoiding
    {ε : ℝ} (hε : 0 < ε) {p : ℝ → ℝ} {pn : ℕ → ℝ → ℝ}
    (hconc : ∀ n, ConcaveOn ℝ (Ioo (-ε) ε) (pn n))
    (hpt : ∀ s ∈ Ioo (-ε) ε, Tendsto (fun n => pn n s) atTop (𝓝 (p s)))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ < ε)
    (B : Set ℝ) (hB : B.Countable)
    (hsup : ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) →
      (∀ᶠ n in atTop, 2 * t n < ρ) →
      (∀ n, t n ∉ B) → (∀ n, -t n ∉ B) →
      ∃ qpos qneg : ℕ → ℝ,
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (t n) + qpos n * (s - t n)) ∧
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (-(t n)) + qneg n * (s + t n)) ∧
        Tendsto (fun n => qpos n - qneg n) atTop (𝓝 0)) :
    ∃ d : ℝ, HasDerivAt p d 0 := by
  obtain ⟨δ, hδ0, hδ, hδbound⟩ :=
    exists_delta_of_pointwise_tendsto_concave hε hconc hpt hρ0 hρε
  obtain ⟨t, htpos, ht, hratio, htB, htBneg⟩ :=
    exists_tilt_tendsto_zero_of_error_tendsto_zero_avoiding hδ0 hδ B hB
  have htsmall : ∀ᶠ n in atTop, 2 * t n < ρ := by
    have hlt : ∀ᶠ n in atTop, t n < ρ / 2 :=
      ht.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ρ / 2))
    filter_upwards [hlt] with n hn
    linarith
  obtain ⟨qpos, qneg, hsupPos, hsupNeg, hdiff⟩ :=
    hsup t htpos ht htsmall htB htBneg
  have hplim : ConcaveOn ℝ (Ioo (-ε) ε) p := concaveOn_of_pointwise_tendsto hpt hconc
  have hconcP : ConcaveOn ℝ (Ioo (-ρ) ρ) p :=
    hplim.subset (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) (convex_Ioo (-ρ) ρ)
  have hposLower : ∀ᶠ n in atTop, (pn n (2 * t n) - pn n (t n)) / t n ≤ qpos n := by
    filter_upwards [hsupPos] with n hn
    exact (intervalSlope_le_of_supergradient_pos (p := pn n) (t := t n) (q := qpos n)
      (htpos n) hn).1
  have hposUpper : ∀ᶠ n in atTop, qpos n ≤ (pn n (t n) - pn n 0) / t n := by
    filter_upwards [hsupPos] with n hn
    exact (intervalSlope_le_of_supergradient_pos (p := pn n) (t := t n) (q := qpos n)
      (htpos n) hn).2
  have hnegLower : ∀ᶠ n in atTop, (pn n 0 - pn n (-(t n))) / t n ≤ qneg n := by
    filter_upwards [hsupNeg] with n hn
    exact (leftSlope_le_of_supergradient_neg (p := pn n) (t := t n) (q := qneg n)
      (htpos n) hn).1
  have hnegUpper : ∀ᶠ n in atTop, qneg n ≤ (pn n (-(t n)) - pn n (-(2 * t n))) / t n := by
    filter_upwards [hsupNeg] with n hn
    exact (leftSlope_le_of_supergradient_neg (p := pn n) (t := t n) (q := qneg n)
      (htpos n) hn).2
  exact hasDerivAt_of_concave_supergradient_sequence_of_diff (p := p) (pn := pn)
    (δ := δ) (t := t) (qpos := qpos) (qneg := qneg) (ε := ρ)
    hρ0 hconcP hδbound hratio htpos ht htsmall
    hposLower hposUpper hnegLower hnegUpper hdiff

/-- **Differentiability from vanishing opposite-tilt probe-cost differences.**
This is the assembly theorem in the form supplied by the cavity/two-cycle
analysis: the stochastic input only asserts that the two opposite-tilt probe
costs agree asymptotically, not that either converges separately. -/
theorem hasDerivAt_of_concave_pointwise_tendsto_of_supergradient_diff
    {ε : ℝ} (hε : 0 < ε) {p : ℝ → ℝ} {pn : ℕ → ℝ → ℝ}
    (hconc : ∀ n, ConcaveOn ℝ (Ioo (-ε) ε) (pn n))
    (hpt : ∀ s ∈ Ioo (-ε) ε, Tendsto (fun n => pn n s) atTop (𝓝 (p s)))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ < ε)
    (hsup : ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) →
      (∀ᶠ n in atTop, 2 * t n < ρ) →
      ∃ qpos qneg : ℕ → ℝ,
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (t n) + qpos n * (s - t n)) ∧
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (-(t n)) + qneg n * (s + t n)) ∧
        Tendsto (fun n => qpos n - qneg n) atTop (𝓝 0)) :
    ∃ d : ℝ, HasDerivAt p d 0 := by
  apply hasDerivAt_of_concave_pointwise_tendsto_of_supergradient_diff_avoiding
    hε hconc hpt hρ0 hρε ∅ Set.countable_empty
  intro t htpos ht hsmall _ _
  exact hsup t htpos ht hsmall

/-- **Differentiability of a pointwise limit of concave functions from opposite
tilt supergradients.**  If

* each `pn n` is concave on `Ioo (-ε) ε` and `pn n → p` pointwise there,
* for every positive tilt sequence `t n → 0` there are opposite-tilt
  supergradient data `qpos n`, `qneg n` whose values converge to one common `d`,

then `p` is differentiable at zero with derivative that common limit. -/
theorem hasDerivAt_of_concave_pointwise_tendsto_of_supergradient_sequence
    {ε : ℝ} (hε : 0 < ε) {p : ℝ → ℝ} {pn : ℕ → ℝ → ℝ}
    (hconc : ∀ n, ConcaveOn ℝ (Ioo (-ε) ε) (pn n))
    (hpt : ∀ s ∈ Ioo (-ε) ε, Tendsto (fun n => pn n s) atTop (𝓝 (p s)))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ < ε)
    (hsup : ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → Tendsto t atTop (𝓝 0) →
      (∀ᶠ n in atTop, 2 * t n < ρ) →
      ∃ qpos qneg : ℕ → ℝ,
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (t n) + qpos n * (s - t n)) ∧
        (∀ᶠ n in atTop, ∀ s, pn n s ≤ pn n (-(t n)) + qneg n * (s + t n)) ∧
        ∃ d : ℝ, Tendsto qpos atTop (𝓝 d) ∧ Tendsto qneg atTop (𝓝 d)) :
    ∃ d : ℝ, HasDerivAt p d 0 := by
  apply hasDerivAt_of_concave_pointwise_tendsto_of_supergradient_diff hε hconc hpt hρ0 hρε
  intro t htpos ht hsmall
  obtain ⟨qpos, qneg, hpos, hneg, d, hqpos, hqneg⟩ := hsup t htpos ht hsmall
  refine ⟨qpos, qneg, hpos, hneg, ?_⟩
  simpa only [sub_self] using hqpos.sub hqneg

end OTSelector

end
end
