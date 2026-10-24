import OTSelector.Reconstruction.FinslerOriginalTileFrozenBoundWiring

/-!
# Linear Palm identification: reduction to the frozen-cost part

This module addresses the last analytic input of the plan-free tile lane,

```Tendsto (fun n => T.tileFixedPairLinearPart ... n c - T.tilePopValue ... c) 0,```

and proves the strongest true form available from the existing formalization.

**Proved.**

* `tileLinearIntegrand_eq_cost_add_probe`: the linear masked integrand splits exactly
  into the frozen-cost part and the probe part (pointwise; mask cases + linearity);
* `tileFixedPairLinearPart_eq_cost_add_probe`: hence the linear part of the fixed-pair
  masked expectation splits additively into a cost integral and a probe integral;
* `t_probe_mul_normalizedProbe_abs_le`: the tilt times the normalized scene probe has
  entries `≤ Bp/(n+1)`;
* `tileLinearProbePart_tendsto_zero`: **the probe contribution of the linear part
  vanishes** (squeezed by `Bp/(n+1) → 0`);
* `linearPalmIdentification_of_cost`: so the linear Palm identification follows from
  the **cost** identification plus the proved probe vanishing;
* `planFreeTileMeanIdentification_of_costPalm`: in the tile lane, the cost
  identification alone gives the linear Palm identification;
* `TileCostPalmIdentification`: the remaining statement, named with explicit
  quantifiers.

**Why the cost identification is NOT derivable from the current lane.**  The tile
lane's `sample n`, `X n`, `Y n` are abstract: no law or stationarity hypothesis relates
`sample n` to the population measure `lambda` in
`tilePopValue c = ∫ z in (T.partition c.1).cell c.2, θ ^ (-2/q) * G c z ∂lambda`.
The identification needs the new structural hypothesis that the sample law is the
population Palm product law of the scene (under which the repo's Campbell bridge
`campbellAveragedFrozenCost_eq_tileSum_add_tail` links sample averages to cell
integrals).  This is missing structure, not a missing lemma.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-- **The tilt times the normalized scene probe has entries `≤ Bp/(n+1)`.** -/
theorem t_probe_mul_normalizedProbe_abs_le {Ω : ℕ → Type*} {ι : Type*} {K : Set M}
    (base : ∀ n, Ω n → ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c : ι) (i j : Fin (n + 1)),
      |base n s c i j| ≤ Bp)
    (t : ℝ) (n : ℕ) (s : Ω n) (c : ι) (i j : Fin (n + 1)) :
    |t * normalizedProbe (K := K) base t n s c i j| ≤ Bp / ((n + 1 : ℕ) : ℝ) := by
  have hpos1 : (0 : ℝ) < 1 + |t| := by positivity
  have hcoef : |t| / (1 + |t|) ≤ 1 := by
    rw [div_le_one hpos1]
    linarith [le_abs_self t]
  have hnm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hden : (0 : ℝ) < (1 + |t|) * ((n + 1 : ℕ) : ℝ) := mul_pos hpos1 hnm
  calc |t * normalizedProbe (K := K) base t n s c i j|
      = |t| * (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * |base n s c i j| := by
        rw [normalizedProbe, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)))]
        ring
    _ ≤ |t| * (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * Bp := by
        refine mul_le_mul_of_nonneg_left (hbase n s c i j) ?_
        exact mul_nonneg (abs_nonneg t) (le_of_lt (by positivity))
    _ = (|t| / (1 + |t|)) * (Bp / ((n + 1 : ℕ) : ℝ)) := by
        field_simp
    _ ≤ 1 * (Bp / ((n + 1 : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hcoef ?_
        exact div_nonneg hBp (le_of_lt hnm)
    _ = Bp / ((n + 1 : ℕ) : ℝ) := one_mul _

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

/-- The **frozen-cost contribution** of the linear masked integrand. -/
noncomputable def tileLinearCostIntegrand
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) : ℝ :=
  (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
    (fun p : Fin (n + 1) × Fin (n + 1) ↦
      (1 - 2 * ε) *
        (scale n * (T.core c).frozenPhysicalCost (T.reference c)
          (X n p.1 s) (Y n p.2 s)))
    (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩)

/-- The **probe contribution** of the linear masked integrand. -/
noncomputable def tileLinearProbeIntegrand
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) : ℝ :=
  (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
    (fun p : Fin (n + 1) × Fin (n + 1) ↦ t * hprobe f t n s c p.1 p.2)
    (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩)

/-- **The linear integrand splits exactly into cost and probe contributions.** -/
theorem tileLinearIntegrand_eq_cost_add_probe
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) :
    T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c s =
      T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s +
        T.tileLinearProbeIntegrand f t X Y hprobe n c s := by
  simp only [tileLinearIntegrand, tileLinearCostIntegrand, tileLinearProbeIntegrand]
  by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
      T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h]
    simp only [tileLinearTerm]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
      Set.indicator_of_notMem h, add_zero]

/-- **The linear part splits additively into a cost integral and a probe integral.** -/
theorem tileFixedPairLinearPart_eq_cost_add_probe
    (sample : ∀ n, Measure (Ω n))
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (hintC : Integrable (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : Integrable (T.tileLinearProbeIntegrand f t X Y hprobe n c) (sample n)) :
    T.tileFixedPairLinearPart f t sample X Y scale hprobe n c =
      (∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s ∂sample n) +
        (∫ s, T.tileLinearProbeIntegrand f t X Y hprobe n c s ∂sample n) := by
  have hfun : (fun s ↦ T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c s) =
      (fun s ↦ T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c s +
        T.tileLinearProbeIntegrand f t X Y hprobe n c s) :=
    funext fun s ↦ T.tileLinearIntegrand_eq_cost_add_probe f t X Y scale hprobe n c s
  show (∫ s, T.tileLinearIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n) = _
  rw [hfun]
  exact integral_add hintC hintP

/-- **The probe contribution of the linear part vanishes.** -/
theorem tileLinearProbePart_tendsto_zero
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t X Y
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n)) :
    Tendsto (fun n ↦ ∫ s, T.tileLinearProbeIntegrand f t X Y
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : ∀ n, |∫ s, T.tileLinearProbeIntegrand f t X Y
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n|
      ≤ Bp / ((n + 1 : ℕ) : ℝ) := by
    intro n
    calc |∫ s, T.tileLinearProbeIntegrand f t X Y
          (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n|
        = |∫ s, (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
            (fun p : Fin (n + 1) × Fin (n + 1) ↦
              t * normalizedProbe (K := K) base t n s c p.1 p.2)
            (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∂sample n| := by
          simp only [tileLinearProbeIntegrand]
      _ ≤ ∫ s, |(T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c).indicator
            (fun p : Fin (n + 1) × Fin (n + 1) ↦
              t * normalizedProbe (K := K) base t n s c p.1 p.2)
            (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩)| ∂sample n :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _s : Ω n, (Bp / ((n + 1 : ℕ) : ℝ)) ∂sample n := by
          refine integral_mono_ae ((hintP n).abs) (integrable_const _) (Eventually.of_forall ?_)
          intro s
          beta_reduce
          by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
              T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
          · rw [Set.indicator_of_mem h]
            exact t_probe_mul_normalizedProbe_abs_le base hBp hbase t n s c _ _
          · rw [Set.indicator_of_notMem h, abs_zero]
            exact probeBound_nonneg hBp n
      _ = Bp / ((n + 1 : ℕ) : ℝ) := by simp
  exact squeeze_zero (fun n ↦ abs_nonneg _) hbound (probeBound_tendsto_zero hBp)

/-- **The cost Palm identification (the remaining analytic input).**  The
frozen-cost contribution of the linear part, normalized, converges to the population
tile value. -/
def TileCostPalmIdentification
    (cost popVal : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ cost n - popVal n) atTop (𝓝 0)

/-- **Linear Palm identification from the cost identification and probe vanishing.** -/
theorem linearPalmIdentification_of_cost
    (linear cost probe popVal : ℕ → ℝ)
    (hsplit : ∀ n, linear n = cost n + probe n)
    (hcost : Tendsto (fun n ↦ cost n - popVal n) atTop (𝓝 0))
    (hprobe : Tendsto probe atTop (𝓝 0)) :
    Tendsto (fun n ↦ linear n - popVal n) atTop (𝓝 0) := by
  have h := hcost.add hprobe
  have heq : (fun n ↦ (cost n - popVal n) + probe n) =
      (fun n ↦ linear n - popVal n) := by
    funext n
    rw [hsplit n]
    ring
  rw [heq] at h
  simpa using h

/-- **The linear Palm identification in the tile lane**, reduced to the cost
identification (the probe contribution is proved to vanish). -/
theorem tileLinearPalmIdentification_of_costPalm
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ n, Integrable (T.tileLinearCostIntegrand (ε := ε) f t X Y tileScale n c)
      (sample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t X Y
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (G : ℕ → (ℚ → M) → ℝ)
    (hcost : Tendsto (fun n ↦
      ∫ s, T.tileLinearCostIntegrand (ε := ε) f t X Y tileScale n c s ∂sample n -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦
      T.tileFixedPairLinearPart f t sample X Y tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0) := by
  refine linearPalmIdentification_of_cost
    (fun n ↦ T.tileFixedPairLinearPart f t sample X Y tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
    (fun n ↦ ∫ s,
      T.tileLinearCostIntegrand (ε := ε) f t X Y tileScale n c s ∂sample n)
    (fun n ↦ ∫ s, T.tileLinearProbeIntegrand f t X Y
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s ∂sample n)
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    (fun n ↦ T.tileFixedPairLinearPart_eq_cost_add_probe sample f t X Y tileScale
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c
      (hintC n) (hintP n))
    hcost (T.tileLinearProbePart_tendsto_zero sample f t X Y c base hBp hbase hintP)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
