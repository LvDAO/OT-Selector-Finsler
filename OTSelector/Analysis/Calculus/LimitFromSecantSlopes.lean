import OTSelector.Analysis.Calculus.OneSidedDerivative
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.MeanSlopeDifferentiability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.MeanSlopeDifferentiability`; the selected original proof blocks follow. -/
section

/-!
# Limit.MeanSlopeDifferentiability

**Conditions:** Finite-level real functions converge pointwise near zero; their fixed positive/negative secants have the stated limits, which approach a common d.

**Objects:** The two one-sided difference quotients and differentiability of their limiting function at zero.

**Proof detail:** Pass each fixed secant through pointwise convergence, identify its unique limit, and combine equal left and right difference-quotient limits into the derivative.

**Sources:** [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=155), Section 4.1.1, Definition 4.1.1, p. 155; Section 3.1, limits and one-sided limits; [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=62), Section 2.2, Lemma 2.2.3, p. 62; Section 2.3, Proposition 2.3.5, pp. 76–77.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Differentiability of a pointwise limit from finite-level secant slopes

Let `J n` be the finite-sample Dirichlet semidiscrete mean and suppose it
converges pointwise to a pressure `P` on a neighborhood of zero.  If, in
addition, the one-sided secant slopes of `J n` at zero converge for every fixed
small step to a common slope function, and these slope functions tend to one
number `d` as the step tends to zero, then `P` is differentiable at zero with
derivative `d`.

This isolates the differentiability half of the pressure producer: it is
enough to identify the one-sided slopes of the finite-level means at every
fixed tilt and to let the tilt vanish afterwards.  No concavity of the limit
is needed; concavity is only a convenient way to produce the slope limits.
-/

open Filter Set Topology
open scoped Topology

namespace OTSelector

/-- The right secant slope of a pointwise limit is the pointwise limit of the
right secant slopes. -/
theorem tendsto_slope_pos_of_tendsto {J : ℕ → ℝ → ℝ} {P : ℝ → ℝ} :
    (∀ t, Tendsto (fun n ↦ J n t) atTop (𝓝 (P t))) →
    ∀ h : ℝ, h ≠ 0 →
      Tendsto (fun n ↦ (J n h - J n 0) / h) atTop
        (𝓝 ((P h - P 0) / h)) := by
  intro hconv h hh
  have hsub : Tendsto (fun n ↦ J n h - J n 0) atTop (𝓝 (P h - P 0)) :=
    (hconv h).sub (hconv 0)
  simpa only [div_eq_mul_inv] using hsub.mul_const h⁻¹

/-- The left secant slope of a pointwise limit is the pointwise limit of the
left secant slopes. -/
theorem tendsto_slope_neg_of_tendsto {J : ℕ → ℝ → ℝ} {P : ℝ → ℝ} :
    (∀ t, Tendsto (fun n ↦ J n t) atTop (𝓝 (P t))) →
    ∀ h : ℝ, h ≠ 0 →
      Tendsto (fun n ↦ (J n 0 - J n (-h)) / h) atTop
        (𝓝 ((P 0 - P (-h)) / h)) := by
  intro hconv h hh
  have hsub : Tendsto (fun n ↦ J n 0 - J n (-h)) atTop (𝓝 (P 0 - P (-h))) :=
    (hconv 0).sub (hconv (-h))
  simpa only [div_eq_mul_inv] using hsub.mul_const h⁻¹

/-- Differentiability of a pointwise limit at zero from the limiting
one-sided secant slopes of the approximating sequence, on a local tilt
interval.

For every fixed positive step `h < ε`, the right slopes of `J n` converge to
`Dpos h`; for every fixed positive step, the left slopes converge to
`Dneg h`.  If both slope families tend to `d` as `h ↓ 0`, then the pointwise
limit `P` has derivative `d` at zero. -/
theorem hasDerivAt_of_tendsto_mean_slope
    {J : ℕ → ℝ → ℝ} {P : ℝ → ℝ} {Dpos Dneg : ℝ → ℝ} {d ε : ℝ}
    (hε : 0 < ε)
    (hconv : ∀ t, |t| < ε → Tendsto (fun n ↦ J n t) atTop (𝓝 (P t)))
    (hpos : ∀ h : ℝ, 0 < h → h < ε →
      Tendsto (fun n ↦ (J n h - J n 0) / h) atTop (𝓝 (Dpos h)))
    (hneg : ∀ h : ℝ, 0 < h → h < ε →
      Tendsto (fun n ↦ (J n 0 - J n (-h)) / h) atTop (𝓝 (Dneg h)))
    (hDpos : Tendsto Dpos (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hDneg : Tendsto Dneg (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    HasDerivAt P d 0 := by
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < ε :=
    (show ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), h < ε from Iio_mem_nhds hε).filter_mono
      nhdsWithin_le_nhds
  have hright : Tendsto (fun h : ℝ ↦ (P h - P 0) / h) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    refine hDpos.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hlt
    have hPh : Tendsto (fun n ↦ J n h) atTop (𝓝 (P h)) :=
      hconv h (by rw [abs_of_pos hh]; exact hlt)
    have hP0 : Tendsto (fun n ↦ J n 0) atTop (𝓝 (P 0)) :=
      hconv 0 (by simpa using hε)
    have hsub : Tendsto (fun n ↦ J n h - J n 0) atTop (𝓝 (P h - P 0)) := hPh.sub hP0
    have hlim : Tendsto (fun n ↦ (J n h - J n 0) / h) atTop
        (𝓝 ((P h - P 0) / h)) := by
      simpa only [div_eq_mul_inv] using hsub.mul_const h⁻¹
    exact (tendsto_nhds_unique hlim (hpos h hh hlt)).symm
  have hleft : Tendsto (fun h : ℝ ↦ (P 0 - P (-h)) / h) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    refine hDneg.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hlt
    have hPh : Tendsto (fun n ↦ J n (-h)) atTop (𝓝 (P (-h))) :=
      hconv (-h) (by rw [abs_neg, abs_of_pos hh]; exact hlt)
    have hP0 : Tendsto (fun n ↦ J n 0) atTop (𝓝 (P 0)) :=
      hconv 0 (by simpa using hε)
    have hsub : Tendsto (fun n ↦ J n 0 - J n (-h)) atTop (𝓝 (P 0 - P (-h))) := hP0.sub hPh
    have hlim : Tendsto (fun n ↦ (J n 0 - J n (-h)) / h) atTop
        (𝓝 ((P 0 - P (-h)) / h)) := by
      simpa only [div_eq_mul_inv] using hsub.mul_const h⁻¹
    exact (tendsto_nhds_unique hlim (hneg h hh hlt)).symm
  exact hasDerivAt_of_tendsto_slope_pos_neg hright hleft

end OTSelector

end
