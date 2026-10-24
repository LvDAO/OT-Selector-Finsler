import OTSelector.Reconstruction.FinslerOriginalTileCountingLaw

/-!
# Per-tile mean convergence: uniform-plan decomposition and the exchangeability of plan weights

This module attacks `TileMeanConvergence` (the per-tile iid LLN of the
plan-weighted frozen tile mean, the remaining mean-convergence sub-gap of
`FinslerOriginalTileSingleConvergence.lean` / `FinslerOriginalTileConcentration.lean`).

The empirical frozen tile mean of a retained tile is the expectation of the
plan-weighted frozen cost

  `E[ tileValue ] = (1/(n+1)) ∫ s, ∑ i ∑ j, A(s)_{ij} E(s)_{ij}`,

where `A(s)` is the optimal fractional plan and `E(s)` the masked frozen cost
matrix on the tile event.  Two structural facts are proved here:

* `integral_matrixEntry_eq_inv_card`: **exchangeability of the plan weights** --
  if all entries of a row-stochastic matrix-valued random variable have equal
  expectation (which holds for the optimal plan of an iid sample by permutation
  invariance) then every expected entry equals `1/(n+1)`.  Hence the uniform plan
  `(1/(n+1))` is the correct leading term of the plan weighting;
* `integral_fractionalAssignmentCost_eq_uniform_add_residual`: **the exact
  decomposition** of the tile mean into the *uniform-plan* (plan-free) tile
  average plus a *plan-residual* term measuring the covariance of the optimal
  plan weights with the frozen entries.

The plan-free tile average is the quantity governed by the repo iid counting laws
(`FinslerOriginalFrozenCoreLLN`) together with the population normalization of
the scale `(n+1)^{2/q}`; the plan-residual is the remaining optimal-plan stability
sub-gap (it vanishes when the optimal plan weights concentrate uniformly on the
rooted cells at the population scale).

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-! ## The exchangeability of plan weights -/

/-- **Exchangeability forces the expected plan weights to be uniform.**

If all entries of a row-stochastic matrix-valued random variable have equal
expectation (the permutation invariance of the optimal plan of an iid sample) and
each row sums to one, then every expected entry equals `1/m`.  The proof is the
row-sum identity `∑ j E[A_ij] = E[∑ j A_ij] = 1`: all `m` summands are equal, so
each equals `1/m`. -/
theorem integral_matrixEntry_eq_inv_card
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (A : Ω → Matrix (Fin m) (Fin m) ℝ)
    (hrow : ∀ s (i : Fin m), ∑ j, A s i j = 1)
    (hint : ∀ i j, Integrable (fun s ↦ A s i j) μ)
    (heq : ∀ (i j i' j' : Fin m),
      ∫ s, A s i j ∂μ = ∫ s, A s i' j' ∂μ) :
    ∀ i j : Fin m, ∫ s, A s i j ∂μ = 1 / (m : ℝ) := by
  intro i j
  rcases m with _ | m
  · exact Fin.elim0 i
  · have hsum : ∑ j' : Fin (m + 1), ∫ s, A s i j' ∂μ = 1 := by
      have hrowInt : ∫ s, (∑ j' : Fin (m + 1), A s i j') ∂μ
          = ∑ j' : Fin (m + 1), ∫ s, A s i j' ∂μ :=
        integral_finsetSum Finset.univ (fun j' _ ↦ hint i j')
      have hone : ∫ s, (∑ j' : Fin (m + 1), A s i j') ∂μ = ∫ _s : Ω, (1 : ℝ) ∂μ := by
        congr 1
        ext s
        exact hrow s i
      rw [hone, integral_const, probReal_univ, smul_eq_mul, one_mul] at hrowInt
      exact hrowInt.symm
    have hall : ∀ j' : Fin (m + 1), ∫ s, A s i j' ∂μ = ∫ s, A s i j ∂μ :=
      fun j' ↦ heq i j' i j
    rw [Finset.sum_congr rfl (fun j' _ ↦ hall j')] at hsum
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hm : (((m + 1 : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [eq_div_iff hm, mul_comm]
    exact hsum

/-! ## The uniform-plan decomposition -/

/-- **Exact decomposition of a matrix-weighted cost into its uniform-plan part
and its plan-residual part.**  For any cost matrix and any plan matrix, the
plan-weighted cost integral equals the uniform-plan cost integral plus the
integral of the residual weights `(A_ij - 1/m)` against the cost. -/
theorem integral_fractionalAssignmentCost_eq_uniform_add_residual
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (cost : Ω → Matrix (Fin m) (Fin m) ℝ)
    (P : Ω → Matrix (Fin m) (Fin m) ℝ)
    (hcost : Integrable (fun s ↦ ∑ i, ∑ j, cost s i j) μ)
    (hres : Integrable (fun s ↦ ∑ i, ∑ j, (P s i j - 1 / (m : ℝ)) * cost s i j) μ) :
    ∫ s, fractionalAssignmentCost (cost s) (P s) ∂μ
      = (1 / (m : ℝ)) * ∫ s, (∑ i, ∑ j, cost s i j) ∂μ
        + ∫ s, (∑ i, ∑ j, (P s i j - 1 / (m : ℝ)) * cost s i j) ∂μ := by
  have hpt : ∀ s, (1 / (m : ℝ)) * (∑ i, ∑ j, cost s i j)
        + ∑ i, ∑ j, (P s i j - 1 / (m : ℝ)) * cost s i j
      = ∑ i, ∑ j, P s i j * cost s i j := by
    intro s
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hleft : Integrable (fun s ↦ (1 / (m : ℝ)) * (∑ i, ∑ j, cost s i j)) μ :=
    hcost.const_mul _
  calc ∫ s, fractionalAssignmentCost (cost s) (P s) ∂μ
      = ∫ s, ((1 / (m : ℝ)) * (∑ i, ∑ j, cost s i j)
          + ∑ i, ∑ j, (P s i j - 1 / (m : ℝ)) * cost s i j) ∂μ := by
        congr 1
        ext s
        simp only [fractionalAssignmentCost]
        exact (hpt s).symm
    _ = (1 / (m : ℝ)) * ∫ s, (∑ i, ∑ j, cost s i j) ∂μ
          + ∫ s, (∑ i, ∑ j, (P s i j - 1 / (m : ℝ)) * cost s i j) ∂μ := by
        rw [integral_add hleft hres, integral_const_mul]


/-! ## Instantiation at the frozen tile cost -/

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore Seed a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

/-- The masked frozen cost matrix of a retained tile, as a function of the sample
outcome. -/
noncomputable def tileCostMatrix
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) : Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun s ↦ maskedFrozenCost (T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c)
    (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
      (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t (hprobe f t n s c))

/-- **The uniform-plan part of the per-tile mean**: the plan-free tile average. -/
noncomputable def uniformTilePart
    (T : D.TaylorTiles ε)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) : ℝ :=
  ∫ s, (∑ i, ∑ j, T.tileCostMatrix f t X Y scale hprobe n c s i j) ∂sample n

/-- **The plan-residual part of the per-tile mean**: the covariance of the optimal
plan weights with the frozen tile entries. -/
noncomputable def planResidualTilePart
    (T : D.TaylorTiles ε)
    (sample : ∀ n, Measure (Ω n))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) : ℝ :=
  ∫ s, (∑ i, ∑ j, (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
    T.tileCostMatrix f t X Y scale hprobe n c s i j) ∂sample n

/-- **Exact decomposition of the per-tile empirical mean** into its uniform-plan
part and its plan-residual part. -/
theorem tileEmpiricalMean_eq_uniformPlan_add_planResidual
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (hcost : Integrable (fun s ↦ ∑ i, ∑ j,
      T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hres : Integrable (fun s ↦ ∑ i, ∑ j,
      (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n)) :
    T.tileEmpiricalMean f t sample X Y scale hprobe A n c =
      (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
          T.uniformTilePart f t sample X Y scale hprobe n c +
        T.planResidualTilePart sample A f t X Y scale hprobe n c) := by
  have htil : (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
      (hprobe f t n) (A n) (scale n) t c s ∂sample n)
      = ∫ s, fractionalAssignmentCost (T.tileCostMatrix f t X Y scale hprobe n c s)
          (A n s) ∂sample n := rfl
  have hdec := integral_fractionalAssignmentCost_eq_uniform_add_residual
    (μ := sample n) (m := n + 1)
    (cost := T.tileCostMatrix f t X Y scale hprobe n c) (P := A n) hcost hres
  simp only [tileEmpiricalMean, uniformTilePart, planResidualTilePart]
  rw [htil, hdec]
  ring


/-- **Uniform-plan tile average convergence** (the plan-free per-tile iid LLN
content): the plan-free tile average, normalized by the tile scale, converges to
the population Campbell value.  This is the per-tile iid counting law. -/
def UniformTileAverageConvergence
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
    Tendsto (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
      ((1 / ((n + 1 : ℕ) : ℝ)) *
        uniformTilePart (T := T) f t sample X Y scale hprobe n c))
      atTop (𝓝 (popVal f t c))

/-- **Plan-residual vanishing** (the optimal-plan stability content): the
covariance of the optimal plan weights with the frozen tile entries, normalized
by the tile scale, vanishes. -/
def TilePlanResidualVanishing
    (sample : ∀ n, Measure (Ω n))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
    Tendsto (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) *
      planResidualTilePart (T := T) sample A f t X Y scale hprobe n c)
      atTop (𝓝 0)

/-- **Per-tile mean convergence from the uniform-plan average and the
plan-residual vanishing.**  This is the exact reduction of `TileMeanConvergence`
(target of this lane): the two remaining analytic inputs are the plan-free
per-tile iid counting law and the optimal-plan stability estimate. -/
theorem tendsto_tileEmpiricalMean_of_uniform_and_residual
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        tileCostMatrix (T := T) f t X Y scale hprobe n c s i j) (sample n))
    (hres : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          tileCostMatrix (T := T) f t X Y scale hprobe n c s i j) (sample n))
    (huni : T.UniformTileAverageConvergence popVal sample X Y scale hprobe)
    (hresv : T.TilePlanResidualVanishing sample A X Y scale hprobe) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileEmpiricalMean f t sample X Y scale hprobe A n c)
        atTop (𝓝 (popVal f t c)) := by
  intro f t c
  have hdecomp : ∀ n : ℕ, T.tileEmpiricalMean f t sample X Y scale hprobe A n c =
      (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
          uniformTilePart (T := T) f t sample X Y scale hprobe n c) +
        (1 / ((n + 1 : ℕ) : ℝ)) *
          planResidualTilePart (T := T) sample A f t X Y scale hprobe n c := by
    intro n
    rw [tileEmpiricalMean_eq_uniformPlan_add_planResidual (T := T) sample f t
      X Y scale hprobe A n c (hint f t n c) (hres f t n c)]
    ring
  have hsum : Tendsto (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
        uniformTilePart (T := T) f t sample X Y scale hprobe n c) +
      (1 / ((n + 1 : ℕ) : ℝ)) *
        planResidualTilePart (T := T) sample A f t X Y scale hprobe n c)
      atTop (𝓝 (popVal f t c)) := by
    have := (huni f t c).add (hresv f t c)
    simpa using this
  exact hsum.congr' (Eventually.of_forall fun n ↦ (hdecomp n).symm)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
