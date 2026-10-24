import OTSelector.Reconstruction.FinslerOriginalQuadraticSqueezeDerivative
import OTSelector.Reconstruction.FinslerOriginalLaneDatumIdentification

/-!
# Completing the quadratic squeeze: the readout tilt derivative from the
Cauchy-Schwarz near-minimizer bound

`FinslerOriginalQuadraticSqueezeDerivative` proved the UPPER half of the squeeze
mechanism under `QuadraticNearMinimizerReadout D p C`:
`Iw v <= Iw 0 + v * p + (1 + C) * v ^ 2`.
This file completes the LOWER half by running the lower-bound block of
`hasDerivAt_stationaryValue_of_kinetic_squeeze` with the quadratic modulus:

* `stationaryValue_lower_of_quadraticReadout`: for `|v| <= 1`,
  `Iw 0 + v * p - M * |v| * sqrt |v| <= Iw v` with `M = C * sqrt (|p| + G + C + 3) + 1`
  (the same-`δ` hypothesis is replaced by `|P c - p| <= C * sqrt (K c - Iw 0) `
  `<= C * sqrt (C₀ * |v|)`, giving the `|v| ^ (3/2)` error);
* `hasDerivAt_stationaryValue_of_quadraticReadout`: combining with the upper half gives
  `HasDerivAt (fun v => D.Iw v) p 0` (`o(v)` error);
* `finslerReadoutTiltDerivative_frozenLowerField_of_quadraticReadout`: the V4 endgame
  `pressureLower` field (`frozenPressureLower ...`) carries the readout tilt derivative
  from the frozen Campbell readout plus the quadratic near-minimizer bound.

No `sorry`, `admit` or added axiom.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace Asymptotics
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable {A B : Set M}

/-- **Lower bound under the quadratic near-minimizer readout.**  For `|v| <= 1`,
`Iw 0 + v p` exceeds `Iw v` by at most `M |v| sqrt |v|` with
`M = C * sqrt (|p| + G + C + 3) + 1`. -/
theorem stationaryValue_lower_of_quadraticReadout
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (p C : ℝ)
    (hC0 : 0 ≤ C) (hread : QuadraticNearMinimizerReadout D p C) :
    ∀ v : ℝ, |v| ≤ 1 →
      D.Iw 0 + v * p - (C * Real.sqrt (|p| + G + C + 3) + 1) * |v| * Real.sqrt |v| ≤
        D.Iw v := by
  intro v hv1
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  set C₀ : ℝ := |p| + G + C + 3 with hC₀
  have hC₀pos : 0 < C₀ := by
    have hp := abs_nonneg p
    have hG := D.bound_nonneg
    rw [hC₀]; linarith
  have hv2 : 0 < v ^ 2 := by positivity
  have hvabs : 0 ≤ |v| := abs_nonneg v
  have hv2le : v ^ 2 ≤ |v| := by nlinarith [sq_abs v, hvabs, hv1]
  have hv2le' : v ^ 2 ≤ |v| * Real.sqrt |v| := by
    have hsq : |v| ≤ Real.sqrt |v| := by
      have h1 : Real.sqrt (|v| ^ 2) ≤ Real.sqrt |v| :=
        Real.sqrt_le_sqrt (by nlinarith [hvabs, hv1])
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hvabs] at h1
    have h2 : |v| ^ 2 ≤ |v| * Real.sqrt |v| := by nlinarith [hsq, hvabs]
    rw [← sq_abs]; exact h2
  obtain ⟨w, hw, hlt⟩ := exists_lt_of_csInf_lt
    (D.nonempty_Cw.image (fun c => D.K c + v * D.P c)) (lt_add_of_pos_right _ hv2)
  obtain ⟨c, hc, rfl⟩ := hw
  have hlt' : D.K c + v * D.P c < D.Iw v + v ^ 2 := by
    simpa [StationaryPressureDatum.Iw, stationaryValue] using hlt
  have hup := stationaryValue_upper_of_quadraticReadout D p C hC0 hread v
  have hneg : -(v * D.P c) ≤ |v| * G := by
    calc -(v * D.P c) ≤ |v * D.P c| := neg_le_abs _
      _ = |v| * |D.P c| := abs_mul v (D.P c)
      _ ≤ |v| * G := mul_le_mul_of_nonneg_left (D.probe_bound c hc) hvabs
  have hvp : v * p ≤ |v| * |p| := by
    calc v * p ≤ |v * p| := le_abs_self _
      _ = |v| * |p| := abs_mul v p
  have hstep : D.Iw v + v ^ 2 - v * D.P c ≤ D.Iw 0 + C₀ * |v| := by
    rw [hC₀]
    nlinarith [hup, hneg, hvp, hv2le, hvabs, abs_nonneg p, D.bound_nonneg]
  have hKc : D.K c ≤ D.Iw 0 + C₀ * |v| := by linarith
  have h0eq : D.Iw 0 = sInf (D.K '' D.Cw) := by
    show stationaryValue D.K D.P D.Cw 0 = sInf (D.K '' D.Cw)
    unfold stationaryValue
    congr 1
    ext x
    simp
  have hKmin : D.Iw 0 ≤ D.K c := by
    rw [h0eq]
    exact csInf_le ⟨0, by rintro _ ⟨d, hd, rfl⟩; exact D.kinetic_nonneg d hd⟩ ⟨c, hc, rfl⟩
  have hKnonneg : 0 ≤ D.K c - D.Iw 0 := by linarith
  have hPc : |D.P c - p| ≤ C * Real.sqrt (C₀ * |v|) := by
    have h1 := hread c hc
    have h2 : Real.sqrt (D.K c - D.Iw 0) ≤ Real.sqrt (C₀ * |v|) :=
      Real.sqrt_le_sqrt (by linarith)
    have h3 : C * Real.sqrt (D.K c - D.Iw 0) ≤ C * Real.sqrt (C₀ * |v|) :=
      mul_le_mul_of_nonneg_left h2 hC0
    linarith
  have hsqrtprod : Real.sqrt (C₀ * |v|) = Real.sqrt C₀ * Real.sqrt |v| :=
    Real.sqrt_mul hC₀pos.le |v|
  have herr : v * (D.P c - p) ≥ -(C * Real.sqrt C₀) * (|v| * Real.sqrt |v|) := by
    have h1 : v * (D.P c - p) ≥ -|v * (D.P c - p)| := neg_abs_le _
    rw [abs_mul] at h1
    have h2 : |v| * |D.P c - p| ≤ |v| * (C * Real.sqrt (C₀ * |v|)) :=
      mul_le_mul_of_nonneg_left hPc hvabs
    have h3 : |v| * (C * Real.sqrt (C₀ * |v|)) =
        (C * Real.sqrt C₀) * (|v| * Real.sqrt |v|) := by
      rw [hsqrtprod]; ring
    linarith
  have hmain : D.Iw 0 + v * p -
      (C * Real.sqrt C₀ + 1) * (|v| * Real.sqrt |v|) ≤ D.Iw v := by
    have h1 : D.Iw v > D.K c + v * D.P c - v ^ 2 := by linarith
    nlinarith [h1, herr, hKnonneg, hv2le']
  have hgoal : D.Iw 0 + v * p -
      (C * Real.sqrt C₀ + 1) * |v| * Real.sqrt |v| ≤ D.Iw v := by
    have hkey := hmain
    nlinarith [hkey]
  rw [hC₀] at hgoal ⊢
  exact hgoal

/-- **The readout tilt derivative from the quadratic near-minimizer bound.**  The upper
bound of `FinslerOriginalQuadraticSqueezeDerivative` and the lower bound above combine
to a Little-o estimate of order `|v| ^ (3/2)`, hence to differentiability at zero. -/
theorem hasDerivAt_stationaryValue_of_quadraticReadout
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (p C : ℝ)
    (hC0 : 0 ≤ C) (hread : QuadraticNearMinimizerReadout D p C) :
    HasDerivAt (fun v : ℝ => D.Iw v) p 0 := by
  set M : ℝ := C * Real.sqrt (|p| + G + C + 3) + 1 with hM
  have hv2le' : ∀ v : ℝ, |v| ≤ 1 → v ^ 2 ≤ |v| * Real.sqrt |v| := by
    intro v hv1
    have hvabs : 0 ≤ |v| := abs_nonneg v
    have hsq : |v| ≤ Real.sqrt |v| := by
      have h1 : Real.sqrt (|v| ^ 2) ≤ Real.sqrt |v| :=
        Real.sqrt_le_sqrt (by nlinarith [hvabs, hv1])
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hvabs] at h1
    have h2 : |v| ^ 2 ≤ |v| * Real.sqrt |v| := by nlinarith [hsq, hvabs]
    rw [← sq_abs]; exact h2
  have herr : ∀ v : ℝ, |v| ≤ 1 →
      |D.Iw v - D.Iw 0 - v * p| ≤ (M + 1 + C) * |v| * Real.sqrt |v| := by
    intro v hv1
    have hlow := stationaryValue_lower_of_quadraticReadout D p C hC0 hread v hv1
    have hup := stationaryValue_upper_of_quadraticReadout D p C hC0 hread v
    have hsq := hv2le' v hv1
    rw [abs_le]
    constructor
    · have hMlow : M * |v| * Real.sqrt |v| ≤ (M + 1 + C) * |v| * Real.sqrt |v| := by
        have hnn : 0 ≤ |v| * Real.sqrt |v| :=
          mul_nonneg (abs_nonneg v) (Real.sqrt_nonneg |v|)
        nlinarith [hnn]
      linarith
    · have hbound : D.Iw v - D.Iw 0 - v * p ≤ (1 + C) * v ^ 2 := by linarith
      have h2 : (1 + C) * v ^ 2 ≤ (1 + C) * (|v| * Real.sqrt |v|) :=
        mul_le_mul_of_nonneg_left hsq (by linarith)
      have hM0 : 0 ≤ M := by
        rw [hM]
        have hp := abs_nonneg p
        have hG := D.bound_nonneg
        nlinarith [Real.sqrt_nonneg (|p| + G + C + 3)]
      have hnn : 0 ≤ |v| * Real.sqrt |v| :=
        mul_nonneg (abs_nonneg v) (Real.sqrt_nonneg |v|)
      have h3 : (1 + C) * (|v| * Real.sqrt |v|) ≤
          (M + 1 + C) * |v| * Real.sqrt |v| := by nlinarith [hM0, hnn, hC0]
      linarith
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine isLittleO_of_tendsto ?_ ?_
  · intro v hv
    subst hv
    simp
  · have hbound : ∀ᶠ v : ℝ in 𝓝 0,
        ‖(D.Iw (0 + v) - D.Iw 0 - v • p) / v‖ ≤ (M + 1 + C) * Real.sqrt |v| := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with v hv1
      have hv1' : |v| ≤ 1 := by simpa [Real.dist_eq] using hv1
      rw [Real.norm_eq_abs, abs_div]
      simp only [zero_add, smul_eq_mul]
      rcases eq_or_ne v 0 with hv0 | hv0
      · simp [hv0]
      · have hvabs : 0 < |v| := abs_pos.mpr hv0
        have herr' := herr v hv1'
        have hstep : |D.Iw v - D.Iw 0 - v * p| / |v| ≤
            ((M + 1 + C) * |v| * Real.sqrt |v|) / |v| := by gcongr
        have hdiv : ((M + 1 + C) * |v| * Real.sqrt |v|) / |v| =
            (M + 1 + C) * Real.sqrt |v| := by
          field_simp
        linarith
    have hlim : Tendsto (fun v : ℝ => (M + 1 + C) * Real.sqrt |v|) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous fun v : ℝ => (M + 1 + C) * Real.sqrt |v| :=
        continuous_const.mul (Real.continuous_sqrt.comp continuous_abs)
      simpa using hcont.tendsto 0
    exact squeeze_zero_norm' hbound hlim

/-- **The frozen-field readout tilt derivative from the quadratic near-minimizer
bound.**  V4 endgame `pressureLower := frozenPressureLower ...` carries the readout tilt
derivative, from the frozen Campbell readout and the pointwise quadratic bound alone. -/
theorem finslerReadoutTiltDerivative_frozenLowerField_of_quadraticReadout
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum)
    (p : FinalProbeSpace A B → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hread : ∀ f : FinalProbeSpace A B,
      QuadraticNearMinimizerReadout (datum f) (p f) C) :
    FinslerReadoutTiltDerivative
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) := by
  have hIw := frozenCampbellReadout_Iw_eq_frozenPressureLower Seed a κ lambda g q datum hC
  refine ⟨p, fun f => ?_⟩
  have hd := hasDerivAt_stationaryValue_of_quadraticReadout (datum f) (p f) C hC0 (hread f)
  have hfield : (fun t => frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f t) =
      fun t => (datum f).Iw t := by
    funext t
    exact (congrFun (hIw f) t).symm
  rw [hfield]
  exact hd

end OTSelector.Reconstruction
