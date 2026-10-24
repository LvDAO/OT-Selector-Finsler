import OTSelector.Reconstruction.FinslerOriginalPlanResidualVanishingProof

/-!
# Normalized dual slack vanishing from a bounded integrated average slack

This module closes the single remaining analytic input of
FinslerOriginalPlanResidualVanishingProof.lean: hslack, the normalized vanishing

  (1/(n+1)) * int s, (1/(n+1)) * sum_ij (E_s ij - dualF_s i - dualG_s j) -> 0.

## The reduction, proved

The normalized vanishing is NOT an extra analytic fact: it is equivalent to a
uniform O(1) bound on the integrated average dual slack.  Indeed, the average dual
slack is pointwise nonnegative by dual feasibility (E_ij >= f_i + g_j), so

  0 <= (1/(n+1)) * int s, slack_s  <= C/(n+1) -> 0

whenever int s, slack_s <= C for all n.  This is proved in
normalized_dualSlack_tendsto_zero_of_bounded (squeeze between 0 and C/(n+1)).

## Consequence

tilePlanResidualVanishing_of_boundedDualSlack: T.TilePlanResidualVanishing from the
bounded integrated average dual slack plus the structural data of the optimal tile
plan and a dual-feasible pair.  The remaining gap is therefore exactly

  exists C >= 0, forall f t c n,
    int s, (1/(n+1)) * sum_ij (E_s ij - dualF_s i - dualG_s j) <= C,

i.e. the optimal tile plan has average dual slack O(1) (not vanishing); the
inverse (n+1) normalization converts this boundedness into the required vanishing.
Equivalently, by optimalityAdvantage_le_averageDualSlack, this is the statement that
the duality gap of the optimal tile plan is O(n+1), i.e. the optimal plan is
asymptotically the uniform plan up to o(1) in normalized cost.

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

/-- **Normalized average dual slack vanishes once the integrated average slack is
bounded.**  This is the exact reduction of the analytic input: boundedness of the
integrated average slack (uniformly in n) implies its normalized vanishing. -/
theorem normalized_dualSlack_tendsto_zero_of_bounded
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : T.Index)
    (dualF dualG : ∀ n, Ω n → Fin (n + 1) → ℝ)
    (hdual : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      dualF n s i + dualG n s j ≤ T.tileCostMatrix f t X Y scale hprobe n c s i j)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ n, (∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
      (T.tileCostMatrix f t X Y scale hprobe n c s i j -
        (dualF n s i + dualG n s j)) ∂sample n) ≤ C) :
    Tendsto (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
      (∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j -
          (dualF n s i + dualG n s j)) ∂sample n)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.div_atTop hnat
  refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hlim
  · refine mul_nonneg (by positivity) (integral_nonneg ?_)
    intro s
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by
        linarith [hdual n s i j])
  · calc (1 / ((n + 1 : ℕ) : ℝ)) * (∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j -
          (dualF n s i + dualG n s j)) ∂sample n)
        ≤ (1 / ((n + 1 : ℕ) : ℝ)) * C :=
          mul_le_mul_of_nonneg_left (hbound n) (by positivity)
      _ = C / ((n + 1 : ℕ) : ℝ) := by ring

/-- **Plan-residual vanishing from a bounded integrated average dual slack.**

All structural and integrability data of the optimal tile plan and a dual-feasible
pair, plus a uniform O(1) bound on the integrated average dual slack. -/
theorem tilePlanResidualVanishing_of_boundedDualSlack
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (dualF dualG : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index → Fin (n + 1) → ℝ)
    (hAnonneg : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)), 0 ≤ A n s i j)
    (hrow : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)), ∑ j, A n s i j = 1)
    (hcol : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)), ∑ i, A n s i j = 1)
    (hopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n),
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s) (A n s) ≤
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    (hdual : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)),
      dualF f t n s c i + dualG f t n s c j ≤
        T.tileCostMatrix f t X Y scale hprobe n c s i j)
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintSlack : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j -
          (dualF f t n s c i + dualG f t n s c j))) (sample n))
    (hslackBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      (∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j -
          (dualF f t n s c i + dualG f t n s c j)) ∂sample n) ≤ C) :
    T.TilePlanResidualVanishing sample A X Y scale hprobe := by
  obtain ⟨C, hC0, hC⟩ := hslackBound
  refine tilePlanResidualVanishing_of_dualSlackControl (T := T) sample A X Y scale hprobe
    dualF dualG hAnonneg hrow hcol hopt hdual hintRes hintSlack ?_
  intro f t c
  exact normalized_dualSlack_tendsto_zero_of_bounded (T := T) sample f t X Y scale hprobe
    c (fun n s ↦ dualF f t n s c) (fun n s ↦ dualG f t n s c)
    (fun n s i j ↦ hdual f t n c s i j) hC0 (hC f t c)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction