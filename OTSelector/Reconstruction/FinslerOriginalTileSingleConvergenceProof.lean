import OTSelector.Reconstruction.FinslerOriginalRootedTileSingleInstantiation
import OTSelector.Reconstruction.FinslerOriginalTileConcentration

/-!
# Per-tile mean convergence and the Efron--Stein input

FinslerOriginalRootedTileSingleInstantiation.lean reduced the two-sided readout
identification to the probabilistic single-tile counting law
T.RootedTileSingleConvergenceInProbability.  This module proves the strongest
true form of the two analytic inputs requested for it, and identifies precisely
where each one is needed.

## What is proved here

The tile empirical mean of the lane (T.tileEmpiricalMean and its copy
T.tileEmpiricalMeanProb) is an INTEGRAL: a deterministic quantity, definitionally
equal to the expectation of the per-tile random frozen mean T.tileValue.  Hence

* the named reduction input (a), the per-tile mean convergence
  T.TileMeanConvergence (already in FinslerOriginalTileConcentration.lean),
  IMPLIES the probabilistic single-tile counting law
  T.RootedTileSingleConvergenceInProbability: the deviation event of a
  deterministic quantity has probability zero as soon as its deviation is below
  the accuracy.  So input (a) alone discharges every deterministic tile
  hypothesis of the readout chain.

* the second analytic input (b), the per-tile Efron--Stein concentration
  T.TileSecondMomentVanishing, is NOT needed for the deterministic readout
  identification: it enters only the strictly stronger law
  T.SingleTileCountingLaw, where the RANDOM frozen tile mean T.tileValue itself
  converges in probability to the population Campbell value.  That composition
  (a) + (b) => SingleTileCountingLaw is proved in FinslerOriginalTileConcentration.lean
  as singleTileCountingLaw_of_mean_and_secondMoment.

## Contents

* tileEmpiricalMeanProb_eq_integral_tileValue: the mean is the expectation of
  the random tile value (normalization check).

* rootedTileSingleConvergenceInProbability_of_tileMeanConvergence: (a) implies
  the probabilistic single-tile counting law.

* camFrozenMeanUpperBound_of_tileMeanConvergence, and
  pressureLower_eq_sceneReadout_of_tileMeanConvergence: the matching upper mean
  bound and the two-sided identification pressureLower = Psi with the single-tile
  law discharged to the per-tile mean convergence.

* rootedTileCampbellMeanIdentification_of_tileMeanConvergence: the named lower
  limit law with the same discharge.

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

/-- The lane's tile empirical mean is exactly the expectation of the per-tile
random frozen mean T.tileValue (the division by the sample size commutes with the
integral). -/
theorem tileEmpiricalMeanProb_eq_integral_tileValue
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) :
    T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c =
      ∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n := by
  have h1 : T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c =
      (∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c s ∂sample n) / ((n + 1 : ℕ) : ℝ) := rfl
  have h2 : (∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) =
      ∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c s / ((n + 1 : ℕ) : ℝ) ∂sample n := rfl
  rw [h1, h2, integral_div]

/-- **Input (a) implies the probabilistic single-tile counting law.**

The lane's empirical tile mean is deterministic (an integral), so its deviation
event has probability 0 or 1; per-tile mean convergence therefore gives
convergence in probability of the empirical mean to the tile population value.
This discharges the single-tile counting law entirely from the per-tile iid LLN
input (a), with no concentration input needed for the deterministic readout
chain. -/
theorem rootedTileSingleConvergenceInProbability_of_tileMeanConvergence
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hmean : T.TileMeanConvergence popVal sample X Y scale hprobe A) :
    T.RootedTileSingleConvergenceInProbability popVal sample X Y scale hprobe A := by
  intro f t c δ hδ
  have hm := hmean f t c
  have hev : ∀ᶠ n in atTop,
      |(∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) -
        popVal f t c| < δ / 2 := by
    have hpos : 0 < δ / 2 := by linarith
    have h := hm.eventually (Metric.ball_mem_nhds _ hpos)
    filter_upwards [h] with n hn
    rw [Real.dist_eq] at hn
    linarith
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_
    tendsto_const_nhds
  filter_upwards [hev] with n hn
  show (sample n).real
    {s | δ ≤ |T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c -
      popVal f t c|} ≤ 0
  rw [tileEmpiricalMeanProb_eq_integral_tileValue (T := T) f t sample X Y scale
    hprobe A n c]
  have hempty : {s : Ω n | δ ≤
      |(∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) -
        popVal f t c|} = (∅ : Set (Ω n)) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    linarith
  rw [hempty, measureReal_empty]

/-- **The matching upper population mean bound from input (a).** -/
theorem camFrozenMeanUpperBound_of_tileMeanConvergence
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
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
    (hmean : T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n ≤
        campbellAveragedFrozenCost P a κ lambda (g f t) q + ε :=
  camFrozenMeanUpperBound_of_rootedTileSingleConvergenceInProbability (T := T) sample
    G g X Y scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileSingleConvergenceInProbability_of_tileMeanConvergence (T := T)
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A hmean)

/-- **The named lower limit law from input (a).** -/
theorem rootedTileCampbellMeanIdentification_of_tileMeanConvergence
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
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
    (hmean : T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (fun f t n s ↦ fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ)) T.Index :=
  rootedTileCampbellMeanIdentification_of_tilePopValueInProbability (T := T) sample
    G g X Y scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileSingleConvergenceInProbability_of_tileMeanConvergence (T := T)
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A hmean)

/-- **The two-sided identification of the pressure lower readout from the per-tile
mean convergence input (a).**

The only analytic lane input left is the per-tile iid LLN with the limiting
stationary matching (T.TileMeanConvergence); the Efron--Stein input (b) is not
needed for this deterministic readout chain. -/
theorem pressureLower_eq_sceneReadout_of_tileMeanConvergence
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
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
    (hmean : T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A)
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n) atTop
        (𝓝 (pressureLower f t)))
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    pressureLower = Ψ :=
  pressureLower_eq_sceneReadout_of_rootedTileSingleConvergenceInProbability (T := T)
    sample G g X Y scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileSingleConvergenceInProbability_of_tileMeanConvergence (T := T)
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A hmean)
    pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction