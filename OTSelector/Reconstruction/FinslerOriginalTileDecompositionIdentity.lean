import OTSelector.Reconstruction.FinslerOriginalTileMeanConvergence
import OTSelector.Reconstruction.FinslerOriginalTileSingleConvergenceProof

/-!
# Exact per-tile decomposition identity

Task-167 isolated the exact per-tile decomposition identity of the plan-weighted
frozen tile mean as the remaining algebraic input of the per-tile iid LLN.  This
module proves it from the frozen tile matrix definition, using the exact
decomposition already established in FinslerOriginalTileMeanConvergence.lean:

  fractionalAssignmentCost (tileCostMatrix) (A s)
    = (1/(n+1)) * ((1/(n+1)) * sum tileCostMatrix + sum (A - 1/(n+1)) * tileCostMatrix)

(the fractional assignment cost splits into the uniform-plan part and the
covariance of the optimal plan weights with the frozen tile entries).

## Contents

* integral_tileValue_eq_uniform_add_residual: the EXACT per-tile decomposition
  identity for the random tile value of the concentration module:
    ∫ s, tileValue s = (1/(n+1)) * ((1/(n+1)) * uniformTilePart + planResidualTilePart).

* tileMeanConvergence_of_uniform_and_residual: the per-tile iid LLN
  T.TileMeanConvergence, PROVED from the two named analytic inputs
  T.UniformTileAverageConvergence and T.TilePlanResidualVanishing.

* rootedTileSingleConvergenceInProbability_of_uniform_and_residual: the
  probabilistic single-tile counting law from the same two inputs.

* camFrozenMeanUpperBound_of_uniform_and_residual: the matching upper population
  mean bound from the same two inputs.

* pressureLower_eq_sceneReadout_of_uniform_and_residual: THE TWO-SIDED
  IDENTIFICATION pressureLower = Psi, with the per-tile iid LLN discharged to the
  plan-free uniform tile average convergence and the plan-residual vanishing.

## Exact remaining sub-gap

Only the two named analytic inputs of the tile lane remain: the plan-free
per-tile iid counting law T.UniformTileAverageConvergence (the plan-free uniform
tile average normalized by (n+1) converges to the population tile value) and the
optimal-plan stability estimate T.TilePlanResidualVanishing.  No decomposition or
algebraic identity remains open.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
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

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **The exact per-tile decomposition identity.**

The expectation of the per-tile random frozen mean splits exactly into the
plan-free uniform tile average and the covariance of the optimal plan weights
with the frozen tile entries, both normalized by the tile scale. -/
theorem integral_tileValue_eq_uniform_add_residual
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
    ∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n =
      (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
          T.uniformTilePart f t sample X Y scale hprobe n c +
        T.planResidualTilePart sample A f t X Y scale hprobe n c) := by
  rw [← tileEmpiricalMeanProb_eq_integral_tileValue (T := T) f t sample X Y scale
    hprobe A n c]
  exact tileEmpiricalMean_eq_uniformPlan_add_planResidual (T := T) sample f t X Y
    scale hprobe A n c hcost hres

/-- **The per-tile iid LLN is PROVED from the two named analytic inputs.**

The per-tile mean convergence T.TileMeanConvergence follows from the plan-free
uniform tile average convergence and the plan-residual vanishing (with the two
integrability inputs): no decomposition or algebraic identity remains open. -/
theorem tileMeanConvergence_of_uniform_and_residual
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (huni : T.UniformTileAverageConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe)
    (hresv : T.TilePlanResidualVanishing sample A X Y scale hprobe) :
    T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A := by
  intro f t c
  have h := tendsto_tileEmpiricalMean_of_uniform_and_residual (T := T) sample X Y
    scale hprobe A
    (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) G c) hintCost hintRes huni hresv
  exact (h f t c).congr' (Eventually.of_forall fun n ↦
    tileEmpiricalMeanProb_eq_integral_tileValue (T := T) f t sample X Y scale
      hprobe A n c)

/-- **The probabilistic single-tile counting law from the two analytic inputs.** -/
theorem rootedTileSingleConvergenceInProbability_of_uniform_and_residual
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (huni : T.UniformTileAverageConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe)
    (hresv : T.TilePlanResidualVanishing sample A X Y scale hprobe) :
    T.RootedTileSingleConvergenceInProbability
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A :=
  rootedTileSingleConvergenceInProbability_of_tileMeanConvergence (T := T)
    (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) G c) sample X Y scale hprobe A
    (tileMeanConvergence_of_uniform_and_residual (T := T) sample G X Y scale
      hprobe A hintCost hintRes huni hresv)

/-- **The matching upper population mean bound from the two analytic inputs.** -/
theorem camFrozenMeanUpperBound_of_uniform_and_residual
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (huni : T.UniformTileAverageConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe)
    (hresv : T.TilePlanResidualVanishing sample A X Y scale hprobe)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileDecompMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n ≤
        campbellAveragedFrozenCost P a κ lambda (g f t) q + ε :=
  camFrozenMeanUpperBound_of_tileMeanConvergence (T := T) sample G g X Y scale
    hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (tileMeanConvergence_of_uniform_and_residual (T := T) sample G X Y scale
      hprobe A hintCost hintRes huni hresv)

/-- **The two-sided identification of the pressure lower readout from the two
named analytic inputs.**

The entire tile lane is reduced to the plan-free per-tile iid counting law and the
optimal-plan stability estimate; the per-tile mean convergence, the single-tile
counting law, the upper and lower mean bounds and the limit-law identification are
all proved. -/
theorem pressureLower_eq_sceneReadout_of_uniform_and_residual
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (huni : T.UniformTileAverageConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe)
    (hresv : T.TilePlanResidualVanishing sample A X Y scale hprobe)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileDecompMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n) atTop
        (𝓝 (pressureLower f t)))
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    pressureLower = Ψ :=
  pressureLower_eq_sceneReadout_of_tileMeanConvergence (T := T) sample G g X Y
    scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (tileMeanConvergence_of_uniform_and_residual (T := T) sample G X Y scale
      hprobe A hintCost hintRes huni hresv)
    pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
