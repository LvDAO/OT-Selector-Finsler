import OTSelector.Reconstruction.FinslerOriginalDualSlackVanishing

/-!
# Uniform O(1) bound on the integrated average dual slack

This module closes the remaining gap of FinslerOriginalDualSlackVanishing.lean:
a uniform O(1) bound on the integrated average dual slack, hence
T.TilePlanResidualVanishing.

## The canonical dual certificate

Dual feasibility is an inequality, so the canonical certificate is available with
no model data: the zero pair dualF = 0, dualG = 0 is dual feasible exactly because
the masked frozen tile entries are nonnegative.  With this pair the average dual
slack is

  (1/(n+1)) * sum i sum j (E_ij - 0 - 0) = (1/(n+1)) * sum i sum j E_ij,

the plan-free uniform tile cost, which is pointwise nonnegative and is bounded by

  (1/(n+1)) * sum i sum j E_ij <= (1/(n+1)) * (n+1)^2 * (C0/(n+1)) = C0

whenever 0 <= E_ij <= C0/(n+1) pointwise.  Hence the integrated average slack is
bounded by the same constant C0, which is exactly the input of
normalized_dualSlack_tendsto_zero_of_bounded.

## Contents

* dualSlack_integral_le_of_entryBound: the integrated average dual slack of the
  zero dual pair is at most C0 from the pointwise entry bound
  0 <= E_ij <= C0/(n+1) and integrability of the uniform tile cost.

* tilePlanResidualVanishing_of_entryBound: T.TilePlanResidualVanishing from the
  pointwise entry bound on the masked frozen tile cost (nonnegativity and a uniform
  C0/(n+1) upper bound), the optimal doubly stochastic plan structure for the tile
  cost, and integrability of the uniform tile cost and of the plan residual.

## Exact remaining gap

The pointwise entry bound 0 <= tileCostMatrix <= C0/(n+1): from the frozen core
formula this follows from a uniform bound on the frozen physical cost and on the
probe entry together with scale n = O(1/(n+1)), a property of the concrete
normalization.  Everything else in the plan-residual lane is now proved.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

/-- **The integrated average dual slack of the zero dual pair is O(1).**  From the
pointwise entry bound 0 <= E_ij <= C0/(n+1), the plan-free uniform tile cost per
row normalizes to at most C0. -/
theorem dualSlack_integral_le_of_entryBound
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : T.Index) {C₀ : ℝ}
    (hentry : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      T.tileCostMatrix f t X Y scale hprobe n c s i j ≤ C₀ / ((n + 1 : ℕ) : ℝ))
    (hintCost : ∀ n, Integrable (fun s ↦ ∑ i, ∑ j,
      T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n)) :
    ∀ n, (∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
      (T.tileCostMatrix f t X Y scale hprobe n c s i j - (0 + 0)) ∂sample n) ≤ C₀ := by
  intro n
  have hpt : ∀ s : Ω n, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
      (T.tileCostMatrix f t X Y scale hprobe n c s i j - (0 + 0)) ≤ C₀ := by
    intro s
    simp only [add_zero, sub_zero]
    have hsum : (∑ i, ∑ j, T.tileCostMatrix f t X Y scale hprobe n c s i j) ≤
        ((n + 1 : ℕ) : ℝ) * C₀ := by
      calc (∑ i, ∑ j, T.tileCostMatrix f t X Y scale hprobe n c s i j)
          ≤ ∑ i, ∑ j, C₀ / ((n + 1 : ℕ) : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hentry n s i j
        _ = ((n + 1 : ℕ) : ℝ) * C₀ := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have h0 : (((n + 1 : ℕ)) : ℝ) ≠ 0 := by positivity
            field_simp
            try simp
            try ring
    have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    calc (1 / ((n + 1 : ℕ) : ℝ)) *
          (∑ i, ∑ j, T.tileCostMatrix f t X Y scale hprobe n c s i j)
        ≤ (1 / ((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) * C₀) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = C₀ := by field_simp
  have hint : Integrable (fun s => (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
      (T.tileCostMatrix f t X Y scale hprobe n c s i j - (0 + 0))) (sample n) := by
    simpa only [add_zero, sub_zero] using
      (hintCost n).const_mul (1 / ((n + 1 : ℕ) : ℝ))
  have hconst : (∫ _ : Ω n, C₀ ∂sample n) = C₀ := by
    rw [integral_const]
    simp
  calc (∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j - (0 + 0)) ∂sample n)
      ≤ (∫ _ : Ω n, C₀ ∂sample n) :=
        integral_mono hint (integrable_const C₀) hpt
    _ = C₀ := hconst

/-- **Plan-residual vanishing from a pointwise entry bound on the tile cost.**

The zero dual pair is dual feasible by nonnegativity of the masked frozen entries,
so the average dual slack is the plan-free uniform tile cost, which the entry bound
0 <= E_ij <= C0/(n+1) bounds by C0 after normalization. -/
theorem tilePlanResidualVanishing_of_entryBound
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hE0 : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)), 0 ≤ T.tileCostMatrix f t X Y scale hprobe n c s i j)
    (hentry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)),
      T.tileCostMatrix f t X Y scale hprobe n c s i j ≤ C₀ / ((n + 1 : ℕ) : ℝ))
    (hAnonneg : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)), 0 ≤ A n s i j)
    (hrow : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)), ∑ j, A n s i j = 1)
    (hcol : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)), ∑ i, A n s i j = 1)
    (hopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n),
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s) (A n s) ≤
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n)) :
    T.TilePlanResidualVanishing sample A X Y scale hprobe := by
  refine tilePlanResidualVanishing_of_boundedDualSlack (T := T) sample A X Y scale hprobe
    (fun _ _ _ _ _ _ ↦ 0) (fun _ _ _ _ _ _ ↦ 0) hAnonneg hrow hcol hopt ?_ hintRes ?_
    ⟨C₀, hC₀, ?_⟩
  · intro f t n c s i j
    simpa using hE0 f t n c s i j
  · intro f t n c
    simpa only [add_zero, sub_zero] using
      (hintCost f t n c).const_mul (1 / ((n + 1 : ℕ) : ℝ))
  · intro f t c n
    simpa only [add_zero, sub_zero] using
      (dualSlack_integral_le_of_entryBound (T := T) sample f t X Y scale hprobe c
        (fun n s i j ↦ hentry f t n c s i j) (fun n ↦ hintCost f t n c)) n

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction