import OTSelector.Reconstruction.FinslerOriginalTaylorSlackRate

/-!
# Frozen quadratic sup bound and probe decay: the concrete clipping lane

This module closes the two numerical inputs (i) and (ii) of
`FinslerOriginalTaylorSlackRate.lean` for the concrete physical-scene probe:

* **(ii) probe decay** is proved here: the normalized scene probe
  ```normalizedProbe base f t n s c = (1 / ((1 + |t|) * (n + 1))) • base n s c```
  has entries bounded by `Bp / (n + 1)` whenever the base probe is bounded by `Bp`, and
  `Bp / (n + 1) → 0` at the tile rate (this is the concrete form of the
  `tileProbe` normalization of `FinslerOriginalTileNormalization.lean`);

* **(i) frozen quadratic sup bound** enters as the explicit hypothesis
  `hR : ∀ n s i j, |frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤ R` with a
  constant `R = (Dm + 2 U) / (1 - 2ε)` — exactly the bound proved in
  `FinslerOriginalFrozenCostSupBound.frozenPhysicalCost_abs_le_of_boundedEdge` from the
  retained-edge geometric data of the tile cover `T.cover c`, the Finsler length bound
  `Dm` and the potential bound `U`.  Wiring that retained-edge data into the tile lane
  is the one remaining mechanical step (recorded as the remaining gap).

**Proved.**  `tileFixedPairClipping_tendsto_zero_of_concreteData`: for the concrete
normalized probe and the frozen sup bound, the fixed-pair clipping correction of the
tile lane tends to zero.  This closes the clipping side of the plan-free tile lane at
the interface level; only the linear Palm identification remains.

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

/-- **The normalized scene probe matrix** of the deep tile lane:
`(1 / ((1 + |t|)(n+1))) • base` (the concrete form of the tile probe normalization). -/
noncomputable def normalizedProbe {Ω : ℕ → Type*} {ι : Type*} {K : Set M}
    (base : ∀ n, Ω n → ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (t : ℝ) (n : ℕ) (s : Ω n) (c : ι) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) • base n s c

/-- **Probe entry decay**: the normalized probe has entries bounded by
`Bp / (n+1)`. -/
theorem normalizedProbe_abs_le {Ω : ℕ → Type*} {ι : Type*} {K : Set M}
    (base : ∀ n, Ω n → ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c : ι) (i j : Fin (n + 1)),
      |base n s c i j| ≤ Bp)
    (t : ℝ) (n : ℕ) (s : Ω n) (c : ι) (i j : Fin (n + 1)) :
    |normalizedProbe (K := K) base t n s c i j| ≤ Bp / ((n + 1 : ℕ) : ℝ) := by
  have hcoef0 : 0 ≤ 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)) := by positivity
  have hcoef1 : 1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    calc ((n + 1 : ℕ) : ℝ) = 1 * ((n + 1 : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ (1 + |t|) * ((n + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
  calc |normalizedProbe (K := K) base t n s c i j|
      = (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * |base n s c i j| := by
        rw [normalizedProbe, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hcoef0]
    _ ≤ (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))) * Bp :=
        mul_le_mul_of_nonneg_left (hbase n s c i j) hcoef0
    _ ≤ (1 / ((n + 1 : ℕ) : ℝ)) * Bp :=
        mul_le_mul_of_nonneg_right hcoef1 hBp
    _ = Bp / ((n + 1 : ℕ) : ℝ) := by ring

/-- **The probe bound decays at the tile rate.** -/
theorem probeBound_tendsto_zero {Bp : ℝ} (hBp : 0 ≤ Bp) :
    Tendsto (fun n : ℕ ↦ Bp / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h : (fun n : ℕ ↦ Bp / ((n + 1 : ℕ) : ℝ)) = fun n ↦ Bp * tileScale n := by
    funext n
    rw [tileScale]
    ring
  rw [h]
  have := (tileScale_tendsto_zero.const_mul Bp)
  simpa using this

/-- **The probe bound is nonnegative.** -/
theorem probeBound_nonneg {Bp : ℝ} (hBp : 0 ≤ Bp) (n : ℕ) :
    0 ≤ Bp / ((n + 1 : ℕ) : ℝ) := by positivity

end OTSelector.Reconstruction

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
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

/-- **Clipping vanishing for the concrete probe and frozen sup bound.**  With the
normalized scene probe `normalizedProbe base`, a bounded base probe (bound `Bp`),
and the frozen quadratic sup bound `R` (supplied by
`FinslerOriginalFrozenCostSupBound.frozenPhysicalCost_abs_le_of_boundedEdge` with
`R = (Dm + 2 U)/(1-2ε)`), the fixed-pair clipping correction of the tile lane tends to
zero. -/
theorem tileFixedPairClipping_tendsto_zero_of_concreteData
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (hε : ε ≤ 1 / 2)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp R : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hRnonneg : 0 ≤ R)
    (hR : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤ R)
    (hint : ∀ n, Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n)) :
    Tendsto (fun n ↦
      T.tileFixedPairClippingCorrection f t sample X Y tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      atTop (𝓝 0) := by
  have hbound : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |(fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') f t n s c i j| ≤
        Bp / ((n + 1 : ℕ) : ℝ) :=
    fun n s i j ↦ normalizedProbe_abs_le base hBp hbase t n s c i j
  have hGnonneg : ∀ n, 0 ≤ Bp / ((n + 1 : ℕ) : ℝ) := probeBound_nonneg hBp
  have hGtend : Tendsto (fun n : ℕ ↦ Bp / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    probeBound_tendsto_zero hBp
  -- frozen sup bound as a constant sequence
  have hRconst : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤
        (fun _ : ℕ ↦ R) n := hR
  exact tileFixedPairClipping_tendsto_zero_of_tileScale (T := T) sample hε f t X Y
    (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') c
    (fun _ : ℕ ↦ R) (fun n ↦ Bp / ((n + 1 : ℕ) : ℝ))
    hRnonneg (fun _ ↦ le_refl R) (fun _ ↦ hRnonneg) hRconst hGnonneg hbound
    hGtend hint

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
