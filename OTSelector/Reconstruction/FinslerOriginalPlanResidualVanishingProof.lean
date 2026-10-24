import OTSelector.Reconstruction.FinslerOriginalTileDecompositionIdentity
import OTSelector.Reconstruction.FinslerOriginalUniformTileAverage

/-!
# Plan-residual vanishing from average dual-slack control

This module closes the last analytic input of the readout chain concretely:
T.TilePlanResidualVanishing.  The module FinslerOriginalUniformTileAverage.lean proved
that TilePlanResidualVanishing follows from the packaged input
PlanFreeAverageCostControl R fac (|R n| <= 2 fac n and fac n / (n+1) -> 0) and that
the plan residual is at most the average dual slack of a dual-feasible certificate
(dual weak duality plus optimality).  This module performs the tile-level assembly.

## The reduction, proved

* tilePlanResidual_pointwise_le_dualSlack: for each sample outcome, the plan
  residual of the masked frozen tile cost is bounded by the average dual slack of
  any dual-feasible pair (dualF, dualG) and any optimal nonnegative doubly
  stochastic plan A.

* abs_planResidualTilePart_le_dualSlack: integrating,

  |planResidualTilePart n c| <= int s, (1/(n+1)) * sum i j (E_s ij - f_s i - g_s j),

  i.e. the plan-residual part is bounded by the integrated average dual slack.

* tilePlanResidualVanishing_of_dualSlackControl: since the dual slack is
  pointwise nonnegative, the integrated slack is at most twice itself, so
  PlanFreeAverageCostControl holds with fac the integrated dual slack; the only
  remaining analytic input is its normalized vanishing
  (1/(n+1)) * int s, (1/(n+1)) * sum i j (E_s ij - f_s i - g_s j) -> 0.

## Exact remaining gap

The control hslack (average dual slack vanishes after normalization; equivalently
the dual certificate is asymptotically tight), together with the structural data of
an optimal nonnegative doubly stochastic plan A for each masked frozen tile cost
and a dual-feasible pair, and integrability of the residual and of the dual slack.
No others: the reduction to TilePlanResidualVanishing is proved here.

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

/-- **Pointwise dual certificate for the tile plan residual.**  For an optimal
nonnegative doubly stochastic plan A and a dual-feasible pair, the plan residual of
the masked frozen tile cost is bounded by the average dual slack. -/
theorem tilePlanResidual_pointwise_le_dualSlack
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) (s : Ω n)
    (dualF dualG : Fin (n + 1) → ℝ)
    (hAnonneg : ∀ i j, 0 ≤ A n s i j)
    (hrow : ∀ i, ∑ j, A n s i j = 1)
    (hcol : ∀ j, ∑ i, A n s i j = 1)
    (hopt : fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s) (A n s) ≤
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    (hdual : ∀ i j, dualF i + dualG j ≤
      T.tileCostMatrix f t X Y scale hprobe n c s i j) :
    |∑ i, ∑ j, (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
        T.tileCostMatrix f t X Y scale hprobe n c s i j| ≤
      (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j - (dualF i + dualG j)) := by
  have hcert := optimalityAdvantage_le_averageDualSlack n
    (T.tileCostMatrix f t X Y scale hprobe n c s) (A n s) hAnonneg hrow hcol hopt
    dualF dualG hdual
  have hsplit : (∑ i, ∑ j, (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
      T.tileCostMatrix f t X Y scale hprobe n c s i j) =
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s) (A n s) -
        fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s)
          (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)) := by
    rw [fractionalAssignmentCost, fractionalAssignmentCost, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsplit, abs_of_nonpos (sub_nonpos.mpr hopt)]
  linarith [hcert]

/-- **The plan-residual part is bounded by the integrated average dual slack.** -/
theorem abs_planResidualTilePart_le_dualSlack
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (dualF dualG : Ω n → Fin (n + 1) → ℝ)
    (hAnonneg : ∀ s i j, 0 ≤ A n s i j)
    (hrow : ∀ s i, ∑ j, A n s i j = 1)
    (hcol : ∀ s j, ∑ i, A n s i j = 1)
    (hopt : ∀ s,
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s) (A n s) ≤
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    (hdual : ∀ s i j, dualF s i + dualG s j ≤
      T.tileCostMatrix f t X Y scale hprobe n c s i j)
    (hintRes : Integrable (fun s ↦ ∑ i, ∑ j,
      (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintSlack : Integrable (fun s ↦ (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
      (T.tileCostMatrix f t X Y scale hprobe n c s i j -
        (dualF s i + dualG s j))) (sample n)) :
    |T.planResidualTilePart sample A f t X Y scale hprobe n c| ≤
      ∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j -
          (dualF s i + dualG s j)) ∂sample n := by
  have hpt : ∀ s : Ω n,
      |∑ i, ∑ j, (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
        T.tileCostMatrix f t X Y scale hprobe n c s i j| ≤
      (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
        (T.tileCostMatrix f t X Y scale hprobe n c s i j -
          (dualF s i + dualG s j)) :=
    fun s ↦ tilePlanResidual_pointwise_le_dualSlack (T := T) f t X Y scale hprobe A n c s
      (dualF s) (dualG s) (hAnonneg s) (hrow s) (hcol s) (hopt s) (hdual s)
  have hrepr : T.planResidualTilePart sample A f t X Y scale hprobe n c =
      ∫ s, ∑ i, ∑ j, (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
        T.tileCostMatrix f t X Y scale hprobe n c s i j ∂sample n := rfl
  rw [hrepr]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono ?_ hintSlack hpt
  simpa only [Real.norm_eq_abs] using hintRes.norm

/-- **Plan-residual vanishing from average dual-slack control.**

All structural and integrability data plus the normalized vanishing of the average
dual slack; the reduction to T.TilePlanResidualVanishing is proved. -/
theorem tilePlanResidualVanishing_of_dualSlackControl
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
    (hslack : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
        (∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
          (T.tileCostMatrix f t X Y scale hprobe n c s i j -
            (dualF f t n s c i + dualG f t n s c j)) ∂sample n)) atTop (𝓝 0)) :
    T.TilePlanResidualVanishing sample A X Y scale hprobe := by
  intro f t c
  let R : ℕ → ℝ := fun n ↦ T.planResidualTilePart sample A f t X Y scale hprobe n c
  let fac : ℕ → ℝ := fun n ↦ ∫ s, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, ∑ j,
    (T.tileCostMatrix f t X Y scale hprobe n c s i j -
      (dualF f t n s c i + dualG f t n s c j)) ∂sample n
  have hbound : ∀ n, |R n| ≤ 2 * fac n := by
    intro n
    have hb := abs_planResidualTilePart_le_dualSlack (T := T) sample f t X Y scale hprobe
      A n c (fun s ↦ dualF f t n s c) (fun s ↦ dualG f t n s c)
      (hAnonneg n) (hrow n) (hcol n) (hopt f t n c) (hdual f t n c)
      (hintRes f t n c) (hintSlack f t n c)
    have hfac0 : 0 ≤ fac n := by
      refine integral_nonneg ?_
      intro s
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by
          linarith [hdual f t n c s i j])
    have hR : R n = T.planResidualTilePart sample A f t X Y scale hprobe n c := rfl
    rw [hR]
    linarith
  have hfaclim : Tendsto (fun n ↦ fac n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    refine (hslack f t c).congr' (Eventually.of_forall fun n ↦ ?_)
    show (1 / ((n + 1 : ℕ) : ℝ)) * fac n = fac n / ((n + 1 : ℕ) : ℝ)
    ring
  have hmain : Tendsto (fun n ↦ R n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_normalized_residual_zero_of_planFreeControl R fac ⟨hbound, hfaclim⟩
  refine hmain.congr' (Eventually.of_forall fun n ↦ ?_)
  show R n / ((n + 1 : ℕ) : ℝ) = (1 / ((n + 1 : ℕ) : ℝ)) * R n
  ring

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction