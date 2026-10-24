import Mathlib.Analysis.Calculus.Deriv.Slope
import OTSelector.Probability.RowProbabilityFilter
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.PressureReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.PressureReadout`; the selected original proof blocks follow. -/
section

/-!
# Limit.PressureReadout

**Conditions:** Each candidate optimizer has the stated affine comparison; central values converge and neighboring tilted values have vanishing lower errors, with differentiable limiting pressure.

**Objects:** Uniform readout convergence across the entire optimizer face, and its probability-row version.

**Proof detail:** Choose fixed small positive and negative tilts with secants near the derivative; affine comparison traps every readout between them, while the probabilistic version bounds the bad set by the finite union of value/comparison failures.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83), Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=155), Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Uniform readout from differentiable pressure

An affine comparison against every unperturbed optimizer turns a lower bound for perturbed
values into a uniform bound for their readouts. Convergence of the central value and
differentiability of the lower limiting pressure identify every readout simultaneously.
Only lower bounds at the neighboring tilts are required. These are conditional analytic
lemmas; they do not assert the geometric or stochastic pressure limits for any transport model.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace OTSelector.Pressure

/-- A differentiable lower pressure and the affine optimizer comparison force every current
optimizer's readout to approach the derivative. The tilted comparisons are simultaneous over
the whole optimal set, and no choice, uniqueness, or nonemptiness of optimizers is required. -/
theorem eventually_forall_readout_of_pressure
    {ι Candidate : Type*} {l : Filter ι} (opt : ι → Set Candidate)
    (readout : ι → Candidate → ℝ)
    (value : ι → ℝ → ℝ) (pressure : ℝ → ℝ) {radius derivative : ℝ}
    (hradius : 0 < radius) (hderiv : HasDerivAt pressure derivative 0)
    (hzero : Tendsto (fun z ↦ value z 0) l (𝓝 (pressure 0)))
    (hlower : ∀ t, |t| < radius →
      Tendsto (fun z ↦ max (pressure t - value z t) 0) l (𝓝 0))
    (haffine : ∀ t, |t| < radius → ∀ᶠ z in l,
      ∀ π ∈ opt z, value z t ≤ value z 0 + t * readout z π)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in l, ∀ π ∈ opt z, |readout z π - derivative| < ε := by
  have hright := (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).2
  have hleft := (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).1
  have hrightClose := (Metric.tendsto_nhds.mp hright) (ε / 2) (by positivity)
  have hleftClose := (Metric.tendsto_nhds.mp hleft) (ε / 2) (by positivity)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hneg : ∀ᶠ t : ℝ in 𝓝[<] 0, t < 0 := self_mem_nhdsWithin
  have hrightRange : ∀ᶠ t : ℝ in 𝓝[>] 0, t < radius :=
    (eventually_lt_nhds hradius).filter_mono nhdsWithin_le_nhds
  have hleftRange : ∀ᶠ t : ℝ in 𝓝[<] 0, -radius < t :=
    (eventually_gt_nhds (neg_neg_of_pos hradius)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htpos, htrange, htclose⟩ := (hpos.and (hrightRange.and hrightClose)).exists
  obtain ⟨s, hsneg, hsrange, hsclose⟩ := (hneg.and (hleftRange.and hleftClose)).exists
  have ht : |t| < radius := by rwa [abs_of_pos htpos]
  have hs : |s| < radius := by rw [abs_of_neg hsneg]; linarith
  have htsec : |(pressure t - pressure 0) / t - derivative| < ε / 2 := by
    simpa only [Real.dist_eq, slope_def_field, sub_zero] using htclose
  have hssec : |(pressure s - pressure 0) / s - derivative| < ε / 2 := by
    simpa only [Real.dist_eq, slope_def_field, sub_zero] using hsclose
  have hcentral : Tendsto (fun z ↦ |value z 0 - pressure 0|) l (𝓝 0) := by
    simpa using (hzero.sub_const (pressure 0)).abs
  have htError : Tendsto
      (fun z ↦ max (pressure t - value z t) 0 + |value z 0 - pressure 0|)
      l (𝓝 0) := by
    simpa using (hlower t ht).add hcentral
  have hsError : Tendsto
      (fun z ↦ max (pressure s - value z s) 0 + |value z 0 - pressure 0|)
      l (𝓝 0) := by
    simpa using (hlower s hs).add hcentral
  have hterror : 0 < ε * t / 2 := by positivity
  have hserror : 0 < ε * (-s) / 2 :=
    div_pos (mul_pos hε (neg_pos.mpr hsneg)) (by norm_num)
  filter_upwards [haffine t ht, haffine s hs,
    htError.eventually (gt_mem_nhds hterror),
    hsError.eventually (gt_mem_nhds hserror)] with z hzt hzs het hes
  intro π hπ
  have hvt := hzt π hπ
  have hvs := hzs π hπ
  have hztLower : pressure t - value z t ≤ max (pressure t - value z t) 0 :=
    le_max_left _ _
  have hzsLower : pressure s - value z s ≤ max (pressure s - value z s) 0 :=
    le_max_left _ _
  have hzUpper : value z 0 - pressure 0 ≤ |value z 0 - pressure 0| := le_abs_self _
  have htPressure : t * (derivative - ε / 2) < pressure t - pressure 0 := by
    have h := (abs_lt.mp htsec).1
    have hquot : derivative - ε / 2 < (pressure t - pressure 0) / t := by linarith
    have hmul := (lt_div_iff₀ htpos).mp hquot
    simpa only [mul_comm] using hmul
  have hsPressure : s * (derivative + ε / 2) < pressure s - pressure 0 := by
    have h := (abs_lt.mp hssec).2
    have hquot : (pressure s - pressure 0) / s < derivative + ε / 2 := by linarith
    have hmul := (div_lt_iff_of_neg hsneg).mp hquot
    simpa only [mul_comm] using hmul
  have hreadoutLower : derivative - ε < readout z π := by
    nlinarith
  have hreadoutUpper : readout z π < derivative + ε := by
    nlinarith
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The uniform pressure readout holds under the original row laws, with a failure event
quantifying over every optimizer. Measures of arbitrary failure sets are allowed; hence no
measurable optimizer selection or measurability of the optimal-set map is assumed. -/
theorem tendsto_measureReal_exists_readout_of_pressure
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (P n)]
    {Candidate : Type*} (opt : (Σ n, Ω n) → Set Candidate)
    (readout : (Σ n, Ω n) → Candidate → ℝ)
    (value : (Σ n, Ω n) → ℝ → ℝ) (pressure : ℝ → ℝ) {radius derivative : ℝ}
    (hradius : 0 < radius) (hderiv : HasDerivAt pressure derivative 0)
    (hzero : ∀ ε, 0 < ε → Tendsto
      (fun n ↦ (P n).real {ω | ε ≤ |value ⟨n, ω⟩ 0 - pressure 0|}) atTop (𝓝 0))
    (hlower : ∀ t, |t| < radius → ∀ ε, 0 < ε → Tendsto
      (fun n ↦ (P n).real {ω | ε ≤ max (pressure t - value ⟨n, ω⟩ t) 0})
      atTop (𝓝 0))
    (haffine : ∀ t, |t| < radius → Tendsto
      (fun n ↦ (P n).real {ω | ¬ ∀ π ∈ opt ⟨n, ω⟩,
        value ⟨n, ω⟩ t ≤ value ⟨n, ω⟩ 0 + t * readout ⟨n, ω⟩ π}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real
      {ω | ∃ π ∈ opt ⟨n, ω⟩, ε ≤ |readout ⟨n, ω⟩ π - derivative|}) atTop (𝓝 0) := by
  have hzero' : Tendsto (fun z ↦ value z 0) (Probability.rowProbabilityFilter P)
      (𝓝 (pressure 0)) :=
    (Probability.tendsto_rowProbabilityFilter_real_iff P _ _).mpr hzero
  have hlower' (t : ℝ) (ht : |t| < radius) : Tendsto
      (fun z ↦ max (pressure t - value z t) 0) (Probability.rowProbabilityFilter P)
      (𝓝 0) := by
    apply (Probability.tendsto_rowProbabilityFilter_real_iff P _ _).mpr
    intro δ hδ
    have habs (x : ℝ) : |max x 0| = max x 0 := abs_of_nonneg (le_max_right x 0)
    simpa only [sub_zero, habs] using hlower t ht δ hδ
  have haffine' (t : ℝ) (ht : |t| < radius) :
      ∀ᶠ z in Probability.rowProbabilityFilter P,
        ∀ π ∈ opt z, value z t ≤ value z 0 + t * readout z π :=
    (Probability.eventually_rowProbabilityFilter_iff P _).mpr (haffine t ht)
  have h := eventually_forall_readout_of_pressure opt readout value pressure
    hradius hderiv hzero' hlower' haffine' hε
  have hprob := (Probability.eventually_rowProbabilityFilter_iff P _).mp h
  simpa only [not_forall, not_lt, exists_prop] using hprob

end OTSelector.Pressure

end
