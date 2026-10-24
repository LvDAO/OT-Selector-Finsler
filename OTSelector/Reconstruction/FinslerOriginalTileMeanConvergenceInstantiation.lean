import OTSelector.Reconstruction.FinslerOriginalUpperMeanInstantiation
import OTSelector.Reconstruction.FinslerOriginalTileCountingLaw

/-!
# Instantiation of the per-tile counting convergence

FinslerOriginalUpperMeanInstantiation.lean left as its last lane input the
per-tile counting convergence
hconv : T.RootedTileMeanConvergence (fun _ _ c => T.tilePopValue G c) sample X Y scale hprobe A.

The lane already contains the single-tile counting law
T.RootedTileSingleConvergence and the reduction
rootedTileMeanConvergence_of_single (FinslerOriginalTileCountingLaw.lean): the
finite retained tile family makes per-tile convergence eventually uniform in the
tile, and the uniform per-tile errors sum to a vanishing total error.  Hence the
instantiation of hconv is DIRECT.

## Contents

* rootedTileMeanConvergence_of_tilePopValue: hconv for the tile population
  values, discharged from the single-tile counting law.

* camFrozenMeanUpperBound_of_rootedTileSingleConvergence: the deep-context
  matching upper population mean bound with hconv discharged.

* rootedTileCampbellMeanIdentification_of_tilePopValue: the named lower
  limit-law content RootedTileCampbellMeanIdentification for the actual frozen
  core functional, with hconv discharged.

* pressureLower_eq_sceneReadout_of_rootedTileSingleConvergence: the two-sided
  identification pressureLower = Psi with hconv discharged; its only remaining
  lane inputs are the single-tile counting law, tile integrability, the frozen
  gluing/decomposition, the empirical mean limit hlim and the assembled readout
  identity hread.

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

/-- **The per-tile counting convergence, instantiated.**

The single-tile counting law for the retained Taylor tiles implies the per-tile
mean convergence of the empirical frozen tile means to the tile population
values: this discharges the hconv input directly from
rootedTileMeanConvergence_of_single. -/
theorem rootedTileMeanConvergence_of_tilePopValue
    (G : ℕ → (ℚ → M) → ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsingle : T.RootedTileSingleConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    T.RootedTileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A :=
  rootedTileMeanConvergence_of_single (T := T)
    (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) G c) sample X Y scale hprobe A hsingle

/-- **The deep-context upper population mean bound with hconv discharged.**

Same conclusion as camFrozenMeanUpperBound_of_rootedTileMeanConvergence, with the
per-tile counting convergence produced from the single-tile counting law. -/
theorem camFrozenMeanUpperBound_of_rootedTileSingleConvergence
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
    (hu : let _instTileMeanInstMetric : MetricSpace M := F.metricSpace;
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
    (hsingle : T.RootedTileSingleConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n ≤
        campbellAveragedFrozenCost P a κ lambda (g f t) q + ε :=
  camFrozenMeanUpperBound_of_rootedTileMeanConvergence (T := T) sample G g X Y
    scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileMeanConvergence_of_tilePopValue (T := T) G sample X Y scale hprobe A
      hsingle)

/-- **The named lower limit-law content with hconv discharged.**

RootedTileCampbellMeanIdentification for the actual frozen core functional,
obtained from the single-tile counting law via the tile Campbell values and the
per-tile Campbell decomposition. -/
theorem rootedTileCampbellMeanIdentification_of_tilePopValue
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
    (hu : let _instTileMeanIdMetric : MetricSpace M := F.metricSpace;
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
    (hsingle : T.RootedTileSingleConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (fun f t n s ↦ fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ)) T.Index := by
  have hconv := rootedTileMeanConvergence_of_tilePopValue (T := T) G sample X Y
    scale hprobe A hsingle
  have hvalues := rootedTileMeanCampbellValues_of_tile_decomposition (T := T) G g
    sample X Y scale hprobe A hF hcomplete hu ha hinj hgt hdecomp hconv
  exact rootedTileCampbellMeanIdentification_of_tile_means (T := T) sample hint hvalues

/-- **The two-sided identification of the pressure lower readout with hconv
discharged.**

Same conclusion as pressureLower_eq_sceneReadout_of_rootedTileMeanConvergence,
with the per-tile counting convergence produced from the single-tile counting
law.  Remaining lane inputs: hsingle, hint, hgt, hdecomp, hlim, hread. -/
theorem pressureLower_eq_sceneReadout_of_rootedTileSingleConvergence
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
    (hu : let _instTileMeanReadoutMetric : MetricSpace M := F.metricSpace;
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
    (hsingle : T.RootedTileSingleConvergence
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
  pressureLower_eq_sceneReadout_of_rootedTileMeanConvergence (T := T) sample G g
    X Y scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileMeanConvergence_of_tilePopValue (T := T) G sample X Y scale hprobe A
      hsingle) pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction