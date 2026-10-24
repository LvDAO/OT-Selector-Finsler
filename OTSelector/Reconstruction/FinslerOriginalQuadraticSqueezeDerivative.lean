import OTSelector.Reconstruction.FinslerOriginalQuadraticNearMinimizerBound

/-!
# Inspection of the kinetic squeeze and the quadratic (Cauchy-Schwarz) near-minimizer bound

## 1. Exact use of `hsqueeze`

In `hasDerivAt_stationaryValue_of_kinetic_squeeze` (`FinslerOriginalReadoutTiltDerivativeActual`)
the hypothesis `hsqueeze : ∀ δ > 0, ∀ c ∈ admissible, K c <= stationaryValue K P admissible 0 + δ → |P c - p| <= δ`
is used at exactly TWO places, both with the SAME δ for the energy tolerance and for the
probe error:

* `hupper` (proof's upper bound): δ := `v ^ 2`; it needs `|P c - p| <= v ^ 2` for the
  candidate `c` with `K c < Iw 0 + v ^ 2`;
* `hlower` (lower bound): δ := `C₀ * |v|` with `C₀ = |p| + G + 3`; it needs
  `|P c - p| <= C₀ * |v|` for candidates with `K c <= Iw 0 + C₀ * |v|`.

Both are of the "same-δ" form; neither is used multiplicatively or quadratically.  The
derivative conclusion is `|Iw v - Iw 0 - v p| <= C v ^ 2` for `|v| <= 1`, whence `o(v)`.

## 2. The true quadratic (Cauchy-Schwarz) near-minimizer bound

`QuadraticNearMinimizerReadout D p C := ∀ c ∈ D.Cw, |D.P c - p| <= C * sqrt (D.K c - D.Iw 0)`
(the probe excess is controlled by the square root of the kinetic excess — the
Cauchy-Schwarz/quadratic coercivity rate of the paper, batch111/batch112).

* `quadraticNearMinimizerReadout_sequential`: quadratic bound ⇒ the sequential (limit)
  readout: any sequence with `K c_n → Iw 0` has `P c_n → p`.  (Continuous sqrt + squeeze.)
* `stationaryValue_upper_of_quadraticReadout`: the UPPER half of the squeeze proof
  generalizes verbatim with the quadratic modulus: for `C >= 0`,
  `Iw v <= Iw 0 + v * p + (1 + C) * v ^ 2`.  Substituting δ := `C₀ * |v|` in the lower
  half instead gives `C * sqrt (C₀ * |v|) = C * sqrt C₀ * |v| ^ (1/2)`, hence a lower
  bound `Iw v >= Iw 0 + v p - M * |v| ^ (3/2)`; the resulting error is
  `O(|v| ^ (3/2)) = o(v)`, so the derivative DOES follow from the quadratic modulus —
  the only missing work is re-running the lower-bound block with this modulus instead of
  the same-δ hypothesis.

No `sorry`, `admit` or added axiom.
-/

open Set Function Filter MeasureTheory Matrix Module
open scoped Topology ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- **The quadratic (Cauchy-Schwarz) near-minimizer readout bound** for a stationary
pressure datum: the probe excess over the limit readout is at most `C` times the square
root of the kinetic excess over the value. -/
def QuadraticNearMinimizerReadout {W : Type*} {G Cb : ℝ}
    (D : StationaryPressureDatum W G Cb) (p C : ℝ) : Prop :=
  ∀ c ∈ D.Cw, |D.P c - p| ≤ C * Real.sqrt (D.K c - D.Iw 0)

/-- **Quadratic bound implies the sequential near-minimizer readout.**  Along any sequence
of weighted matchings whose kinetic energy converges to `Iw 0`, the probes converge to
`p`. -/
theorem quadraticNearMinimizerReadout_sequential
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (p C : ℝ)
    (hC : QuadraticNearMinimizerReadout D p C) (c : ℕ → W)
    (hc : ∀ n, c n ∈ D.Cw)
    (hK : Tendsto (fun n => D.K (c n)) atTop (𝓝 (D.Iw 0))) :
    Tendsto (fun n => D.P (c n)) atTop (𝓝 p) := by
  have hD : Tendsto (fun n => D.K (c n) - D.Iw 0) atTop (𝓝 0) := by
    simpa using hK.sub_const (D.Iw 0)
  have hsqrt : Tendsto (fun n => Real.sqrt (D.K (c n) - D.Iw 0)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => Real.sqrt (D.K (c n) - D.Iw 0)) atTop
        (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hD
    simpa only [Real.sqrt_zero] using h2
  have hCsq : Tendsto (fun n => C * Real.sqrt (D.K (c n) - D.Iw 0)) atTop (𝓝 0) := by
    simpa using hsqrt.const_mul C
  have habs : Tendsto (fun n => |D.P (c n) - p|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hCsq
      (fun n => abs_nonneg _) (fun n => hC (c n) (hc n))
  rw [Metric.tendsto_atTop] at habs ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := habs ε hε
  exact ⟨N, fun n hn => by
    have h := hN n hn
    simpa [Real.dist_eq] using h⟩

/-- **The upper half of the squeeze proof under the quadratic bound.**  For a stationary
datum, `C >= 0` and the quadratic near-minimizer readout bound, the weighted pressure at
tilt `v` is at most `Iw 0 + v p + (1 + C) v ^ 2`: exactly the upper estimate
`hupper` of `hasDerivAt_stationaryValue_of_kinetic_squeeze`, with `v ^ 2` replaced by
`(1 + C) * v ^ 2`. -/
theorem stationaryValue_upper_of_quadraticReadout
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (p C : ℝ)
    (hC0 : 0 ≤ C) (hC : QuadraticNearMinimizerReadout D p C) (v : ℝ) :
    D.Iw v ≤ D.Iw 0 + v * p + (1 + C) * v ^ 2 := by
  have h0eq : D.Iw 0 = sInf (D.K '' D.Cw) := by
    show stationaryValue D.K D.P D.Cw 0 = sInf (D.K '' D.Cw)
    unfold stationaryValue
    congr 1
    ext x
    simp
  have hKmin : ∀ c ∈ D.Cw, D.Iw 0 ≤ D.K c := by
    intro c hc
    rw [h0eq]
    exact csInf_le ⟨0, by rintro _ ⟨d, hd, rfl⟩; exact D.kinetic_nonneg d hd⟩ ⟨c, hc, rfl⟩
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  have hv2 : 0 < v ^ 2 := by positivity
  have hlt0 : sInf (D.K '' D.Cw) < sInf (D.K '' D.Cw) + v ^ 2 :=
    lt_add_of_pos_right _ hv2
  obtain ⟨w, hw, hlt⟩ := exists_lt_of_csInf_lt (D.nonempty_Cw.image D.K) hlt0
  obtain ⟨c, hc, rfl⟩ := hw
  have hlt' : D.K c - D.Iw 0 < v ^ 2 := by rw [← h0eq] at hlt; linarith
  have hnonneg : 0 ≤ D.K c - D.Iw 0 := by linarith [hKmin c hc]
  have hsqr : Real.sqrt (D.K c - D.Iw 0) < |v| := by
    have h1 : Real.sqrt (D.K c - D.Iw 0) < Real.sqrt (v ^ 2) :=
      Real.sqrt_lt_sqrt hnonneg hlt'
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hPc : |D.P c - p| ≤ C * |v| := by
    have h1 := hC c hc
    have h2 : C * Real.sqrt (D.K c - D.Iw 0) ≤ C * |v| :=
      mul_le_mul_of_nonneg_left hsqr.le hC0
    linarith
  have hle : D.Iw v ≤ D.K c + v * D.P c :=
    stationaryValue_le (v := v)
      (bddBelow_stationaryValue (G := G) (v := v) D.kinetic_nonneg D.probe_bound) hc
  have hKC : D.K c ≤ D.Iw 0 + v ^ 2 := by linarith
  have hprod : v * (D.P c - p) ≤ C * v ^ 2 := by
    have h1 : v * (D.P c - p) ≤ |v * (D.P c - p)| := le_abs_self _
    have h2 : |v * (D.P c - p)| = |v| * |D.P c - p| := abs_mul v (D.P c - p)
    have h3 : |v| * |D.P c - p| ≤ |v| * (C * |v|) :=
      mul_le_mul_of_nonneg_left hPc (abs_nonneg v)
    have h4 : |v| * (C * |v|) = C * v ^ 2 := by
      rw [← sq_abs v]; ring
    linarith
  nlinarith [hle, hprod, hKC]

end OTSelector.Reconstruction
