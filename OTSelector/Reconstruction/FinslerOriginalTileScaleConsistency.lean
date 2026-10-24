import OTSelector.Reconstruction.FinslerOriginalTileClippingConcrete

/-!
# Paper normalization scale split: resolution

This module resolves the scale split found in
`FinslerOriginalTileNormalizationAudit.lean`.

## The paper normalization

The paper normalizes the empirical tile sums by the `n^{1-2/q}` factor that comes from
the `θ^{-2/q}` root-measure density: after normalization by `n^{1-2/q}` the
approximation error is controlled (`main.tex` lines 1720, 2318), and the root/potential
measure has density proportional to `θ^{-2/q}` (lines 1858-1865).  In the tile lane the
frozen cost enters each matrix entry multiplied by the free normalization slot
`scale`, and the population tile value is the *unnormalized* cell integral
`tilePopValue = ∫ z in cell, θ^{-2/q} G z ∂lambda`.  The lane's normalization is
therefore

```tileScalePaper q n = ((n + 1 : ℕ) : ℝ) ^ (2 / q),```

the `θ^{-2/q}`-compensating factor (growing for `q > 0`; `q ≥ 3` in the paper).  The
decaying `tileScale = 1/(n+1)` used in the clipping lane is the *inverse* (empirical
mean) normalization.

## The resolution (proved here)

The clipping budget of `FinslerOriginalClippingBudget.lean` is

```tileSlackBudget ε scale R G t n = (1 - 2ε) * (scale n * R n) + |t| * G n.```

**Normalizing by `scale` makes it scale-free up to the probe term:**
```tileSlackBudget ε scale R G t n / scale n
  = (1 - 2ε) * R n + |t| * (G n / scale n)```
(`tileSlackBudget_div_eq`), so

1. at the **paper scale** `tileScalePaper` the normalized budget converges to the
   bounded constant `(1 - 2ε) * R` (`tileScalePaper_normalizedBudget_tendsto`), the
   probe term vanishing because `G n * (scale n)⁻¹ → 0`
   (`tileScalePaper_probeTerm_tendsto_zero`);
2. at the **decaying** `tileScale` both terms vanish, which is the clipping-vanishing
   lane already proved (`tileFixedPairClipping_tendsto_zero_of_tileScale`).

Hence the two scales are **not in conflict**: the clipping correction appears in the
pressure bound *normalized by the same scale*, where it is a bounded
`O(1)` (paper scale) or vanishing (empirical scale) error; in both cases the
clipping lane is consistent, and the linear lane may use the paper scale
`tileScalePaper` with the readout hypothesis `scale n * palmMean n → tilePopValue`.

**Remaining sub-gap.**  The clipped-vs-linear correction itself is only *bounded* after
paper normalization (its constant `(1 - 2ε) R` is not small); the pressure bound needs
the clipping correction normalized by the *tile sum* control (the `n^{1-2/q}` factor of
main.tex), i.e. the bound must be inserted into the paper's deterministic
clipping/normalization inequality rather than be driven to zero.  That insertion is the
one remaining bookkeeping step.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-- **The paper normalization scale** `(n+1)^{2/q}`: the `θ^{-2/q}`-compensating
factor of the tile sums (`main.tex` lines 1720, 2318, 1858-1865). -/
noncomputable def tileScalePaper (q : ℝ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) ^ (2 / q)

/-- The paper scale is positive. -/
theorem tileScalePaper_pos {q : ℝ} (n : ℕ) : 0 < tileScalePaper q n := by
  unfold tileScalePaper
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The paper scale is nonzero. -/
theorem tileScalePaper_ne_zero {q : ℝ} (n : ℕ) : tileScalePaper q n ≠ 0 :=
  ne_of_gt (tileScalePaper_pos n)

/-- **The paper scale grows to infinity** (for a positive exponent). -/
theorem tileScalePaper_tendsto_atTop {q : ℝ} (hq : 0 < 2 / q) :
    Tendsto (tileScalePaper q) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hrpow : Tendsto (fun x : ℝ ↦ x ^ (2 / q)) atTop atTop :=
    tendsto_rpow_atTop hq
  exact hrpow.comp hbase

/-- **The inverse paper scale tends to zero.** -/
theorem tileScalePaper_inv_tendsto_zero {q : ℝ} (hq : 0 < 2 / q) :
    Tendsto (fun n ↦ (tileScalePaper q n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tileScalePaper_tendsto_atTop hq)

/-- **The clipping budget normalized by `scale` is scale-free up to the probe term.** -/
theorem tileSlackBudget_div_eq (ε t : ℝ) (scale R G : ℕ → ℝ) (n : ℕ)
    (hscale : scale n ≠ 0) :
    tileSlackBudget ε scale R G t n / scale n =
      (1 - 2 * ε) * R n + |t| * (G n / scale n) := by
  unfold tileSlackBudget
  field_simp

/-- **The clipping budget is `scale` times its normalized form.** -/
theorem tileSlackBudget_eq_scale_mul (ε t : ℝ) (scale R G : ℕ → ℝ) (n : ℕ)
    (hscale : scale n ≠ 0) :
    tileSlackBudget ε scale R G t n =
      scale n * ((1 - 2 * ε) * R n + |t| * (G n / scale n)) := by
  unfold tileSlackBudget
  rw [div_eq_mul_inv]
  field_simp

/-- **The probe term of the normalized budget vanishes at the paper scale.** -/
theorem tileScalePaper_probeTerm_tendsto_zero {q : ℝ} (hq : 0 < 2 / q)
    {Bp : ℝ} (hBp : 0 ≤ Bp) (t : ℝ) :
    Tendsto (fun n ↦ |t| * ((Bp / ((n + 1 : ℕ) : ℝ)) / tileScalePaper q n))
      atTop (𝓝 0) := by
  have hprobe : Tendsto (fun n : ℕ ↦ Bp / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    probeBound_tendsto_zero hBp
  have hinv : Tendsto (fun n ↦ (tileScalePaper q n)⁻¹) atTop (𝓝 0) :=
    tileScalePaper_inv_tendsto_zero hq
  have hprod : Tendsto (fun n ↦ (Bp / ((n + 1 : ℕ) : ℝ)) *
      (tileScalePaper q n)⁻¹) atTop (𝓝 0) := by
    simpa using hprobe.mul hinv
  have hfun : (fun n ↦ |t| * ((Bp / ((n + 1 : ℕ) : ℝ)) / tileScalePaper q n)) =
      fun n ↦ |t| * ((Bp / ((n + 1 : ℕ) : ℝ)) * (tileScalePaper q n)⁻¹) := by
    funext n
    rw [div_eq_mul_inv]
  rw [hfun]
  simpa using hprod.const_mul |t|

/-- **The normalized clipping budget at the paper scale converges to the bounded
constant `(1 - 2ε) * R`.** -/
theorem tileScalePaper_normalizedBudget_tendsto {q : ℝ} (hq : 0 < 2 / q)
    {Bp R : ℝ} (hBp : 0 ≤ Bp) (ε t : ℝ) :
    Tendsto (fun n ↦
      tileSlackBudget ε (tileScalePaper q) (fun _ ↦ R)
        (fun n ↦ Bp / ((n + 1 : ℕ) : ℝ)) t n / tileScalePaper q n)
      atTop (𝓝 ((1 - 2 * ε) * R)) := by
  have hconst : (fun n ↦ (1 - 2 * ε) * R + |t| *
      ((Bp / ((n + 1 : ℕ) : ℝ)) / tileScalePaper q n)) =
      fun n ↦ (1 - 2 * ε) * R + |t| *
        ((Bp / ((n + 1 : ℕ) : ℝ)) / tileScalePaper q n) := rfl
  have hlim : Tendsto (fun n ↦ (1 - 2 * ε) * R + |t| *
      ((Bp / ((n + 1 : ℕ) : ℝ)) / tileScalePaper q n)) atTop
      (𝓝 ((1 - 2 * ε) * R + 0)) :=
    tendsto_const_nhds.add (tileScalePaper_probeTerm_tendsto_zero hq hBp t)
  have hfun : (fun n ↦
      tileSlackBudget ε (tileScalePaper q) (fun _ ↦ R)
        (fun n ↦ Bp / ((n + 1 : ℕ) : ℝ)) t n / tileScalePaper q n) =
      fun n ↦ (1 - 2 * ε) * R + |t| *
        ((Bp / ((n + 1 : ℕ) : ℝ)) / tileScalePaper q n) := by
    funext n
    exact tileSlackBudget_div_eq ε t (tileScalePaper q) (fun _ ↦ R)
      (fun n ↦ Bp / ((n + 1 : ℕ) : ℝ)) n (tileScalePaper_ne_zero n)
  rw [hfun, hconst]
  simpa using hlim

end OTSelector.Reconstruction
