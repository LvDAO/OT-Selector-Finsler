import OTSelector.Reconstruction.FinslerOriginalQuadraticSqueezeDerivativeComplete

/-!
# Quadratic coercion from frozen minimality

`QuadraticNearMinimizerReadout` (batch112) asks for the square-root probe-kinetic bound
`|P c - p| <= C * sqrt (K c - Iw 0)`.  This file reduces it to a purely ALGEBRAIC
**squared** Cauchy-Schwarz stability statement and then to minimizer stability:

* `SquaredProbeKineticCoercion D p C`: `(P c - p)^2 <= C^2 * (K c - Iw 0)` for
  `c ∈ Cw` (no `Real.sqrt`!);
* `quadraticNearMinimizerReadout_of_squaredCoercion`: for `0 <= C`, the squared coercion
  implies `QuadraticNearMinimizerReadout D p C` (via `Real.sqrt_le_sqrt` /
  `Real.sqrt_sq_eq_abs`);
* `squaredProbeKineticCoercion_of_minimizer_stability`: if `c0 ∈ Cw` is a tilt-0
  minimizer (`K c0 = Iw 0`, `P c0 = p`), `d` is a nonnegative discrepancy,
  `|P c - P c0| <= L * sqrt (d c c0)` and the kinetic energy is strongly convex,
  `d c c0 <= (2 / m_conv) * (K c - K c0)`, then the squared coercion holds with
  `C = L * sqrt (2 / m_conv)` (and `C >= 0`);
* `finslerReadoutTiltDerivative_frozenLowerField_of_squaredCoercion`: the V4 endgame
  `pressureLower` field carries the readout tilt derivative from the ALGEBRAIC squared
  coercion alone (no same-δ squeeze, no square-root input).

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

/-- **Squared Cauchy-Schwarz probe-kinetic coercion.**  The probe difference from the
limit readout is controlled quadratically by the kinetic excess over the value. -/
def SquaredProbeKineticCoercion {W : Type*} {G Cb : ℝ}
    (D : StationaryPressureDatum W G Cb) (p C : ℝ) : Prop :=
  ∀ c ∈ D.Cw, (D.P c - p) ^ 2 ≤ C ^ 2 * (D.K c - D.Iw 0)

/-- **Squared coercion implies the square-root near-minimizer readout.** -/
theorem quadraticNearMinimizerReadout_of_squaredCoercion
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (p C : ℝ)
    (hC0 : 0 ≤ C) (hcoerc : SquaredProbeKineticCoercion D p C) :
    QuadraticNearMinimizerReadout D p C := by
  intro c hc
  have hsq := hcoerc c hc
  rcases eq_or_lt_of_le hC0 with hC | hC
  · -- C = 0: the square vanishes
    have hzero : (D.P c - p) ^ 2 = 0 := by
      have hle : (D.P c - p) ^ 2 ≤ 0 := by
        rw [← hC] at hsq
        simpa using hsq
      exact le_antisymm hle (sq_nonneg _)
    have hsub : D.P c - p = 0 := sq_eq_zero_iff.mp hzero
    rw [hsub, ← hC]
    simp
  · have hnonneg : 0 ≤ D.K c - D.Iw 0 := by
      have h1 : 0 ≤ (D.K c - D.Iw 0) * C ^ 2 := by
        rw [mul_comm]
        exact le_trans (sq_nonneg _) hsq
      have h2 : 0 < C ^ 2 := by positivity
      exact nonneg_of_mul_nonneg_left h1 h2
    have hsq2 : (D.P c - p) ^ 2 ≤ C ^ 2 * (D.K c - D.Iw 0) := hsq
    have h1 : Real.sqrt ((D.P c - p) ^ 2) ≤ Real.sqrt (C ^ 2 * (D.K c - D.Iw 0)) :=
      Real.sqrt_le_sqrt hsq2
    have h2 : Real.sqrt ((D.P c - p) ^ 2) = |D.P c - p| := Real.sqrt_sq_eq_abs _
    have h3 : Real.sqrt (C ^ 2 * (D.K c - D.Iw 0)) =
        C * Real.sqrt (D.K c - D.Iw 0) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]
    rw [h2, h3] at h1
    exact h1

/-- **Squared coercion from tilt-0 minimizer stability.**  With a tilt-0 minimizer `c0`,
a nonnegative discrepancy `d`, an `L`-Lipschitz probe bound in `sqrt d` and strong
convexity of the kinetic energy, the squared coercion holds with
`C = L * sqrt (2 / m_conv)`. -/
theorem squaredProbeKineticCoercion_of_minimizer_stability
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (p L m_conv : ℝ)
    (c0 : W) (d : W → W → ℝ)
    (hc0 : c0 ∈ D.Cw) (hKc0 : D.K c0 = D.Iw 0) (hPc0 : D.P c0 = p)
    (hL0 : 0 ≤ L) (hm : 0 < m_conv)
    (hd : ∀ c ∈ D.Cw, 0 ≤ d c c0)
    (hLip : ∀ c ∈ D.Cw, |D.P c - D.P c0| ≤ L * Real.sqrt (d c c0))
    (hconv : ∀ c ∈ D.Cw, d c c0 ≤ (2 / m_conv) * (D.K c - D.K c0)) :
    SquaredProbeKineticCoercion D p (L * Real.sqrt (2 / m_conv))
      ∧ 0 ≤ L * Real.sqrt (2 / m_conv) := by
  have hm2 : (0 : ℝ) ≤ 2 / m_conv := div_nonneg (by norm_num) hm.le
  have hC0 : 0 ≤ L * Real.sqrt (2 / m_conv) :=
    mul_nonneg hL0 (Real.sqrt_nonneg _)
  refine ⟨?_, hC0⟩
  intro c hc
  have hd0 : 0 ≤ d c c0 := hd c hc
  have hLipc := hLip c hc
  have hLsqrt_nonneg : 0 ≤ L * Real.sqrt (d c c0) :=
    mul_nonneg hL0 (Real.sqrt_nonneg _)
  have hsq1 : (D.P c - D.P c0) ^ 2 ≤ (L * Real.sqrt (d c c0)) ^ 2 := by
    have habs : |D.P c - D.P c0| ≤ L * Real.sqrt (d c c0) := hLipc
    have h1 : |D.P c - D.P c0| ^ 2 ≤ (L * Real.sqrt (d c c0)) ^ 2 := by
      nlinarith [habs, abs_nonneg (D.P c - D.P c0), hLsqrt_nonneg]
    rwa [sq_abs] at h1
  have hsq2 : (L * Real.sqrt (d c c0)) ^ 2 = L ^ 2 * d c c0 := by
    rw [mul_pow, Real.sq_sqrt hd0]
  have hsq3 : L ^ 2 * d c c0 ≤ L ^ 2 * ((2 / m_conv) * (D.K c - D.K c0)) :=
    mul_le_mul_of_nonneg_left (hconv c hc) (sq_nonneg L)
  have hsq4 : L ^ 2 * ((2 / m_conv) * (D.K c - D.K c0)) =
      (L * Real.sqrt (2 / m_conv)) ^ 2 * (D.K c - D.K c0) := by
    rw [mul_pow, Real.sq_sqrt hm2]
    ring
  have hK := hKc0
  calc (D.P c - p) ^ 2 = (D.P c - D.P c0) ^ 2 := by rw [hPc0]
    _ ≤ (L * Real.sqrt (d c c0)) ^ 2 := hsq1
    _ = L ^ 2 * d c c0 := hsq2
    _ ≤ L ^ 2 * ((2 / m_conv) * (D.K c - D.K c0)) := hsq3
    _ = (L * Real.sqrt (2 / m_conv)) ^ 2 * (D.K c - D.K c0) := hsq4
    _ = (L * Real.sqrt (2 / m_conv)) ^ 2 * (D.K c - D.Iw 0) := by rw [hK]

/-- **The frozen-field readout tilt derivative from the ALGEBRAIC squared coercion.** -/
theorem finslerReadoutTiltDerivative_frozenLowerField_of_squaredCoercion
    {W : Type*} {G Cb : ℝ}
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum)
    (p : FinalProbeSpace A B → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hcoerc : ∀ f : FinalProbeSpace A B, SquaredProbeKineticCoercion (datum f) (p f) C) :
    FinslerReadoutTiltDerivative
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) :=
  finslerReadoutTiltDerivative_frozenLowerField_of_quadraticReadout Seed a κ lambda g q
    datum hC p C hC0
    (fun f => quadraticNearMinimizerReadout_of_squaredCoercion (datum f) (p f) C hC0
      (hcoerc f))

end OTSelector.Reconstruction
