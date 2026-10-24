import OTSelector.Reconstruction.FinslerOriginalUniformNearMinimizerProof

/-!
# The Fenchel / Legendre perturbation mechanism behind near-minimizer readout

For a stationary pressure datum, `Iw t` is the infimum of `K c + t * P c` over `Cw`
(`D.Iw t = stationaryValue D.K D.P D.Cw t = sInf ((fun c => D.K c + t * D.P c) '' D.Cw)`),
so for every `c ∈ Cw` and every `t : ℝ` the Fenchel inequality holds:

    Iw t <= K c + t * P c.

This module formalizes the resulting perturbation (Legendre) identity and what it does,
and does NOT, give for near-minimizers:

* `probe_perturbation_identity`: exactly
  `t * (P c - p) = (K c + t * P c - Iw t) + (Iw t - Iw 0 - t * p) - (K c - Iw 0)`;
* `fenchel_probe_inequality`: since the first term is nonnegative,
  `t * (P c - p) >= (Iw t - Iw 0 - t * p) - (K c - Iw 0)`;
* `nearMinimizer_probe_bound_of_derivative_gap`: if `K c <= Iw 0 + δ` and the derivative
  gap `|Iw (±δ) - Iw 0 ∓ δ p| <= ε δ` holds at the TWO tilts `±δ`, then
  `|P c - p| <= 1 + ε` — a CONSTANT modulus, not δ;
* `nearMinimizer_sqrt_rate` (docstring-level scaling): with `t = sqrt δ` the same argument
  gives the rate `|P c - p| <= sqrt δ + ε` (using `δ / sqrt δ = sqrt δ`).

## Exact relationship to `ZeroTiltNearMinimizerReadoutUniform`

Differentiability `HasDerivAt Iw p 0` plus Fenchel can only produce the **square-root**
readout modulus `|P c - p| <= sqrt (K c - Iw 0)` (constant modulus after rescaling).
The uniform bound of batch108 asks for the SAME δ in energy excess and probe error,
which is strictly stronger.  So `ZeroTiltNearMinimizerReadoutUniform` is NOT a
consequence of the tangent/competitor family at `Iw`; the two-sided tangent family gives
`Iw t <= Iw 0 + t p + o(t)`, hence only the sequential near-minimizer readout with
`sqrt` rate.  Closing the uniform form needs the additional one-sided competitor
inequality at the frozen geometric lane (or the producer must be restated at the
`sqrt`-rate / two-sided-slope form).

No `sorry`, `admit` or added axiom.
-/

noncomputable section
namespace OTSelector.Reconstruction

/-- **The perturbation (Legendre) identity.**  Pure algebra, valid for any `K P Iw`. -/
theorem probe_perturbation_identity (K P Iw : ℝ → ℝ) (c p t : ℝ) :
    t * (P c - p) =
      (K c + t * P c - Iw t) + (Iw t - Iw 0 - t * p) - (K c - Iw 0) := by
  ring

/-- **The Fenchel probe inequality.**  If `Iw t <= K c + t * P c` for all tilts
(the infimum property of a stationary pressure datum), then the probe perturbation
is bounded below by the derivative gap minus the kinetic excess. -/
theorem fenchel_probe_inequality (K P Iw : ℝ → ℝ) (c p t : ℝ)
    (hmin : ∀ t : ℝ, Iw t ≤ K c + t * P c) :
    (Iw t - Iw 0 - t * p) - (K c - Iw 0) ≤ t * (P c - p) := by
  have hid := probe_perturbation_identity K P Iw c p t
  have hnonneg : 0 ≤ K c + t * P c - Iw t := by linarith [hmin t]
  linarith

/-- **Near-minimizer probe bound from the two-sided derivative gap.**  If `K c` is within
`δ` of `Iw 0` and the derivative gap at the two tilts `±δ` is at most `ε * δ`, then
`|P c - p| <= 1 + ε`: a constant (in δ) readout modulus. -/
theorem nearMinimizer_probe_bound_of_derivative_gap
    (K P Iw : ℝ → ℝ) (c p δ ε : ℝ)
    (hδ : 0 < δ) (_hε : 0 ≤ ε)
    (hmin : ∀ t : ℝ, Iw t ≤ K c + t * P c)
    (hK : K c ≤ Iw 0 + δ)
    (hgapδ : |Iw δ - Iw 0 - δ * p| ≤ ε * δ)
    (hgapneg : |Iw (-δ) - Iw 0 - (-δ) * p| ≤ ε * δ) :
    |P c - p| ≤ 1 + ε := by
  have hK' : -(K c - Iw 0) ≥ -δ := by linarith
  have hI_pos : (Iw δ - Iw 0 - δ * p) ≥ -ε * δ := by
    have h := (abs_le.mp hgapδ).1
    linarith
  have hI_neg : (Iw (-δ) - Iw 0 - (-δ) * p) ≥ -ε * δ := by
    have h := (abs_le.mp hgapneg).1
    linarith
  have hpos : δ * (P c - p) ≥ -ε * δ - δ := by
    have h := fenchel_probe_inequality K P Iw c p δ hmin
    linarith
  have hneg : (-δ) * (P c - p) ≥ -ε * δ - δ := by
    have h := fenchel_probe_inequality K P Iw c p (-δ) hmin
    linarith
  have hlow : P c - p ≥ -(1 + ε) := by nlinarith [hpos, hδ]
  have hhigh : P c - p ≤ 1 + ε := by nlinarith [hneg, hδ]
  rw [abs_le]
  exact ⟨hlow, hhigh⟩

end OTSelector.Reconstruction
