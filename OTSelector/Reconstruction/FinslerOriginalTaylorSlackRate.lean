import OTSelector.Reconstruction.FinslerOriginalClippingBudget

/-!
# Taylor slack rate with the concrete tile scale

This module closes gap (a) of `FinslerOriginalClippingBudget.lean` by instantiating the
abstract tile scale with the concrete normalization

```tileScale n = 1 / (n + 1),```

so that the frozen absolute entry budget becomes
```(1 - 2ε) * (R n / (n + 1)) + |t| * G n,```
and the slack rate reduces to: the frozen quadratic magnitude `R` is **bounded** and the
probe bound `G` **tends to zero** — or, in remainder form, the Taylor remainder is
`o(n+1)`.

**Proved.**

* `tileScale_pos`, `tileScale_tendsto_zero` — the concrete scale is positive and
  vanishes;
* `tendsto_tileScale_mul_of_bounded` — bounded sequence times the concrete scale
  tends to zero (squeeze with the explicit bound `C / (n+1)`);
* `tileSlackRate_tileScale` — **the Taylor slack rate**: for bounded `R` and `G → 0`,
  `(1-2ε) * (tileScale n * R n) + |t| * G n → 0`;
* `tileFixedPairClippingVanishing_of_tileScale` — the clipping correction satisfies
  `TileClippingVanishing` with the concrete-scale budget, hence tends to zero
  (combining with `tileFixedPairClippingVanishing_of_slack` of task 224).

**What remains analytic** (interface change recorded): the boundedness of the frozen
quadratic magnitude `R n = sup |frozenPhysicalCost (reference) (X i) (Y j)|` (from the
pressure-freezing/Taylor constants) and the probe decay `G n → 0` are NOT derived here;
the concrete `scale` instantiation is a *hypothesis-level* interface (the tile lane
carries `scale` abstractly, so no re-derivation is needed — only the two numerical
inputs).  The linear Palm identification remains untouched.

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

/-- **The concrete tile scale** `1 / (n + 1)`. -/
noncomputable def tileScale (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) : ℝ)

/-- The concrete tile scale is positive. -/
theorem tileScale_pos (n : ℕ) : 0 < tileScale n := by
  rw [tileScale]
  exact one_div_pos.mpr (by positivity)

/-- The concrete tile scale is at most one. -/
theorem tileScale_le_one (n : ℕ) : tileScale n ≤ 1 := by
  rw [tileScale, div_le_one (by positivity)]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- **The concrete tile scale vanishes.** -/
theorem tileScale_tendsto_zero : Tendsto tileScale atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h : Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := hinv.comp hnat
  have h' : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (((n + 1 : ℕ)) : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using h
  show Tendsto (fun n : ℕ ↦ (1 : ℝ) / (((n + 1 : ℕ)) : ℝ)) atTop (𝓝 0)
  exact h'

/-- **Bounded sequence times the concrete scale tends to zero.** -/
theorem tendsto_tileScale_mul_of_bounded {R : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ n, |R n| ≤ C) :
    Tendsto (fun n ↦ tileScale n * R n) atTop (𝓝 0) := by
  have hbound : ∀ n, |tileScale n * R n| ≤ C * tileScale n := by
    intro n
    rw [abs_mul, abs_of_pos (tileScale_pos n), mul_comm C (tileScale n)]
    exact mul_le_mul_of_nonneg_left (hR n) (le_of_lt (tileScale_pos n))
  have hmajor : Tendsto (fun n ↦ C * tileScale n) atTop (𝓝 0) := by
    have h := (tileScale_tendsto_zero.const_mul C)
    simpa using h
  show Tendsto (fun n ↦ tileScale n * R n) atTop (𝓝 0)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n ↦ abs_nonneg _) hbound hmajor

/-- **The Taylor slack rate with the concrete tile scale.**  For bounded frozen
quadratic magnitude `R` and probe bound `G → 0`, the frozen absolute entry budget
vanishes:

```(1 - 2ε) * (tileScale n * R n) + |t| * G n → 0.``` -/
theorem tileSlackRate_tileScale (ε t : ℝ) {R G : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ n, |R n| ≤ C) (hG : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * R n) + |t| * G n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n * R n)) atTop (𝓝 0) := by
    have h := (tendsto_tileScale_mul_of_bounded hC hR).const_mul (1 - 2 * ε)
    simpa using h
  have h2 : Tendsto (fun n ↦ |t| * G n) atTop (𝓝 0) := by
    have h := hG.const_mul |t|
    simpa using h
  simpa using h1.add h2

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

/-- **Clipping vanishing from the concrete Taylor slack rate.**  With the concrete
tile scale `1/(n+1)` and the numerical inputs (bounded frozen quadratic magnitude
`R`, probe bound `G → 0`), the fixed-pair clipping correction vanishes.  This closes
gap (a) of `FinslerOriginalClippingBudget.lean` at the hypothesis level. -/
theorem tileFixedPairClipping_tendsto_zero_of_tileScale
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (hε : ε ≤ 1 / 2)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : T.Index)
    (R G : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hRbound : ∀ n, R n ≤ C) (hRnonneg : ∀ n, 0 ≤ R n)
    (hR : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤ R n)
    (hGnonneg : ∀ n, 0 ≤ G n)
    (hG : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |hprobe f t n s c i j| ≤ G n)
    (hGtend : Tendsto G atTop (𝓝 0))
    (hint : ∀ n, Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y tileScale hprobe n c) (sample n)) :
    Tendsto (fun n ↦
      T.tileFixedPairClippingCorrection f t sample X Y tileScale hprobe n c)
      atTop (𝓝 0) := by
  have hRabs : ∀ n, |R n| ≤ C := fun n ↦ abs_le.mpr ⟨by linarith [hRnonneg n], hRbound n⟩
  have hslack : Tendsto
      (fun n ↦ (1 - 2 * ε) * (tileScale n * R n) + |t| * G n) atTop (𝓝 0) :=
    tileSlackRate_tileScale ε t hC hRabs hGtend
  have hvan := tileFixedPairClippingVanishing_of_slack (T := T) sample hε f t X Y
    tileScale hprobe c R G hR hG (fun n ↦ le_of_lt (tileScale_pos n)) hint hslack
  exact tileFixedPairClipping_tendsto_zero_of_budget _ _ hvan

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
