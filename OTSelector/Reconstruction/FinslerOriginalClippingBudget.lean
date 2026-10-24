import OTSelector.Reconstruction.FinslerOriginalTileIntegralSplit

/-!
# Taylor slack clipping budget

This module closes gap (2) of `FinslerOriginalTileIntegralSplit.lean` as far as the
available formalization allows: it proves the **clipping budget bound** from pointwise
bounds on the frozen physical cost and on the probe, and states the *sole* remaining
input as an explicit `Tendsto` hypothesis on the Taylor slack sequence.

**Proved (pointwise bound of the linear term).**  If
`|frozenPhysicalCost (reference) (X i) (Y j)| ≤ R` and `|probe i j| ≤ G` and
`ε ≤ 1/2`, then

```|tileLinearTerm ... s i j| ≤ (1 - 2ε) * (scale n * R) + |t| * G.```

**Proved (clipping is bounded by the linear term).**  `max (-x) 0 ≤ |x|`, hence the
masked clipping integrand is pointwise bounded by the same budget.

**Proved (clipping vanishing from the slack).**  `TileClippingVanishing` holds for the
clipping correction with the explicit budget sequence

```budget n = (1 - 2ε) * (scale n * R n) + |t| * G n,```

whenever `budget n → 0`.  The latter is the Taylor slack rate `ε · scale · R → 0`:
it is the ONLY statement not supplied here (the concrete `scale` definition and the
Taylor remainder rate are not available as a `Tendsto` statement in the current
reconstruction lane).

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

/-- `max (-x) 0 ≤ |x|`. -/
theorem max_neg_zero_le_abs (x : ℝ) : max (-x) 0 ≤ |x| := by
  rcases le_total 0 x with h | h
  · have hz : max (-x) 0 = 0 := max_eq_right (by linarith)
    rw [hz]
    exact abs_nonneg x
  · have hz : max (-x) 0 = -x := max_eq_left (by linarith)
    rw [hz, abs_of_nonpos h]

/-- **The Taylor slack budget sequence.**  The frozen absolute entry budget:
`(1 - 2ε) * (scale n * R n) + |t| * G n`. -/
def tileSlackBudget (ε : ℝ) (scale R G : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  (1 - 2 * ε) * (scale n * R n) + |t| * G n

/-- **The slack budget tends to zero** from the two Taylor-slack vanishing statements
(`(1-2ε) · scale · R → 0` and `G → 0`). -/
theorem tileSlackBudget_tendsto_zero (ε : ℝ) (scale R G : ℕ → ℝ) (t : ℝ)
    (hslack : Tendsto (fun n ↦ (1 - 2 * ε) * (scale n * R n)) atTop (𝓝 0))
    (hG : Tendsto G atTop (𝓝 0)) :
    Tendsto (tileSlackBudget ε scale R G t) atTop (𝓝 0) := by
  have h' : Tendsto (fun n ↦ (1 - 2 * ε) * (scale n * R n) + |t| * G n) atTop (𝓝 0) := by
    simpa using hslack.add (hG.const_mul |t|)
  exact h'

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

/-- **Pointwise bound of the linear term by the Taylor slack budget.** -/
theorem abs_tileLinearTerm_le (hε : ε ≤ 1 / 2)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1))
    (R G : ℝ)
    (hR : |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤ R)
    (hG : |hprobe f t n s c i j| ≤ G)
    (hscale : 0 ≤ scale n) :
    |T.tileLinearTerm (ε := ε) f t X Y scale hprobe n c s i j| ≤
      (1 - 2 * ε) * (scale n * R) + |t| * G := by
  have hcoef : 0 ≤ 1 - 2 * ε := by linarith
  have hfirst : |(1 - 2 * ε) * (scale n *
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s))| ≤
      (1 - 2 * ε) * (scale n * R) := by
    rw [abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left
      (by rw [abs_mul, abs_of_nonneg hscale]; exact mul_le_mul_of_nonneg_left hR hscale)
      hcoef
  have hsecond : |t * hprobe f t n s c i j| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hG (abs_nonneg t)
  calc |T.tileLinearTerm (ε := ε) f t X Y scale hprobe n c s i j|
      = |(1 - 2 * ε) * (scale n *
            (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)) +
          t * hprobe f t n s c i j| := rfl
    _ ≤ |(1 - 2 * ε) * (scale n *
            (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s))| +
          |t * hprobe f t n s c i j| := abs_add_le _ _
    _ ≤ (1 - 2 * ε) * (scale n * R) + |t| * G := add_le_add hfirst hsecond

/-- **Clipping is bounded by the slack budget**: the masked clipping integrand is
pointwise at most the frozen absolute entry budget. -/
theorem tileClippingIntegrand_le_budget (hε : ε ≤ 1 / 2)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n)
    (R G : ℝ)
    (hR : ∀ i j : Fin (n + 1),
      |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤ R)
    (hG : ∀ i j : Fin (n + 1), |hprobe f t n s c i j| ≤ G)
    (hscale : 0 ≤ scale n) :
    T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s ≤
      (1 - 2 * ε) * (scale n * R) + |t| * G := by
  simp only [tileClippingIntegrand]
  by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
      T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
  · rw [Set.indicator_of_mem h]
    refine le_trans (max_neg_zero_le_abs _) ?_
    exact abs_tileLinearTerm_le (T := T) hε f t X Y scale hprobe n c s _ _ R G
      (hR _ _) (hG _ _) hscale
  · rw [Set.indicator_of_notMem h]
    have hpos : 0 ≤ (1 - 2 * ε) * (scale n * R) + |t| * G := by
      have : 0 ≤ 1 - 2 * ε := by linarith
      have h1 : 0 ≤ (1 - 2 * ε) * (scale n * R) :=
        mul_nonneg this (mul_nonneg hscale (le_trans (abs_nonneg _) (hR 0 0)))
      have h2 : 0 ≤ |t| * G :=
        mul_nonneg (abs_nonneg t) (le_trans (abs_nonneg _) (hG 0 0))
      linarith
    exact hpos

/-- **Clipping vanishing from the Taylor slack budget.**  The clipping correction of
the fixed-pair masked expectation is squeezed between `0` and the slack budget; hence
it tends to zero whenever the Taylor slack budget does.  This is the `TileClippingVanishing`
instantiation for the tile clipping correction, with the sole remaining input being the
slack rate `(1-2ε)·scale·R → 0`. -/
theorem tileFixedPairClippingVanishing_of_slack
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (hε : ε ≤ 1 / 2)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : T.Index)
    (R G : ℕ → ℝ)
    (hR : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤ R n)
    (hG : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |hprobe f t n s c i j| ≤ G n)
    (hscale : ∀ n, 0 ≤ scale n)
    (hint : ∀ n, Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c) (sample n))
    (hslack : Tendsto
      (fun n ↦ (1 - 2 * ε) * (scale n * R n) + |t| * G n) atTop (𝓝 0)) :
    TileClippingVanishing
      (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale hprobe n c)
      (fun n ↦ (1 - 2 * ε) * (scale n * R n) + |t| * G n) := by
  refine ⟨fun n ↦ ⟨?_, ?_⟩, hslack⟩
  · exact integral_nonneg fun s ↦ by
      simp only [tileClippingIntegrand]
      by_cases h : (⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩) ∈
          T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c
      · rw [Set.indicator_of_mem h]
        exact le_max_right _ _
      · rw [Set.indicator_of_notMem h]
        exact le_refl 0
  · simp only [tileFixedPairClippingCorrection]
    calc ∫ s, T.tileClippingIntegrand (ε := ε) f t X Y scale hprobe n c s ∂sample n
        ≤ ∫ _s : Ω n, ((1 - 2 * ε) * (scale n * R n) + |t| * G n) ∂sample n :=
          integral_mono_ae (hint n) (integrable_const _)
            (Eventually.of_forall fun s ↦
              tileClippingIntegrand_le_budget (T := T) hε f t X Y scale hprobe n c s
                (R n) (G n) (hR n s) (hG n s) (hscale n))
      _ = (1 - 2 * ε) * (scale n * R n) + |t| * G n := by simp

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
