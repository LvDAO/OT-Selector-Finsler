import OTSelector.Reconstruction.FinslerOriginalTileMeanConvergenceInstantiation
import OTSelector.Reconstruction.FinslerOriginalTileSingleConvergence

/-!
# RootedTileSingleConvergence from the single-tile convergence module

FinslerOriginalTileMeanConvergenceInstantiation.lean left as its last named lane
input the deterministic per-tile counting law T.RootedTileSingleConvergence of
FinslerOriginalTileCountingLaw.lean.

## The exact mismatch and why there is none

FinslerOriginalTileSingleConvergence.lean states the single-tile law in
probabilistic form, T.RootedTileSingleConvergenceInProbability, and remarks that
the deterministic form is not attainable.  However, the tile empirical mean
T.tileEmpiricalMean (and its copy T.tileEmpiricalMeanProb) is an INTEGRAL
(∫ tileFrozenCost)/(n+1): a quantity that is constant in the sample point s.
Hence the event
  {s | delta <= |tileEmpiricalMeanProb ... n c - popVal f t c|}
is either empty or all of the sample space, its probability is 0 or 1, and
convergence in probability of this deterministic quantity to popVal is exactly
eventual deterministic convergence to popVal.  The two forms of the single-tile
law are therefore EQUIVALENT, with no change of kernel, mask, probe or
normalization.

## Contents

* rootedTileSingleConvergence_of_inProbability: the bridge, deriving the
  deterministic single-tile law from the in-probability form.

* camFrozenMeanUpperBound_of_rootedTileSingleConvergenceInProbability: the
  deep-context matching upper population mean bound with the single-tile law in
  its probabilistic form.

* rootedTileCampbellMeanIdentification_of_tilePopValueInProbability: the named
  lower limit-law content with the single-tile law in probabilistic form.

* pressureLower_eq_sceneReadout_of_rootedTileSingleConvergenceInProbability: the
  two-sided identification pressureLower = Psi with the single-tile law in
  probabilistic form.

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

/-- **The bridge: in-probability single-tile convergence implies the
deterministic single-tile counting law.**

The tile empirical mean is an integral, hence constant in the sample point, so
the deviation event has probability 0 or 1; convergence in probability of this
deterministic quantity is exactly its eventual convergence.  No kernel, mask,
probe or normalization changes are involved: the two tile functionals
tileEmpiricalMean and tileEmpiricalMeanProb are definitionally equal. -/
theorem rootedTileSingleConvergence_of_inProbability
    (popVal : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℝ)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsingle : T.RootedTileSingleConvergenceInProbability popVal sample X Y scale hprobe A) :
    T.RootedTileSingleConvergence popVal sample X Y scale hprobe A := by
  intro f t c δ hδ
  have hδ2 : 0 < δ / 2 := by linarith
  have h := hsingle f t c (δ / 2) hδ2
  have hlt : ∀ᶠ n in atTop,
      (sample n).real
        {s | δ / 2 ≤ |T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c -
          popVal f t c|} < 1 / 2 :=
    (tendsto_order.1 h).2 (1 / 2) (by norm_num)
  filter_upwards [hlt] with n hn
  show |T.tileEmpiricalMean f t sample X Y scale hprobe A n c - popVal f t c| ≤ δ
  have hdef : T.tileEmpiricalMean f t sample X Y scale hprobe A n c =
      T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c := rfl
  rw [hdef]
  by_contra hcon
  have hge : δ / 2 ≤ |T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c -
      popVal f t c| := by
    have := not_le.mp hcon
    linarith
  have hset : {s : Ω n | δ / 2 ≤ |T.tileEmpiricalMeanProb f t sample X Y scale hprobe A n c -
      popVal f t c|} = (Set.univ : Set (Ω n)) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hge
  rw [hset] at hn
  have hmuniv : (sample n).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ]
    norm_num
  linarith

/-- **The deep-context upper population mean bound with the single-tile law in
probabilistic form.** -/
theorem camFrozenMeanUpperBound_of_rootedTileSingleConvergenceInProbability
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
    (hu : let _instSingleProbMetric : MetricSpace M := F.metricSpace;
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
    (hsingle : T.RootedTileSingleConvergenceInProbability
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n ≤
        campbellAveragedFrozenCost P a κ lambda (g f t) q + ε :=
  camFrozenMeanUpperBound_of_rootedTileSingleConvergence (T := T) sample G g X Y
    scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileSingleConvergence_of_inProbability (T := T) (fun _ _ c ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      sample X Y scale hprobe A hsingle)

/-- **The named lower limit-law content with the single-tile law in
probabilistic form.** -/
theorem rootedTileCampbellMeanIdentification_of_tilePopValueInProbability
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
    (hu : let _instSingleProbIdMetric : MetricSpace M := F.metricSpace;
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
    (hsingle : T.RootedTileSingleConvergenceInProbability
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (fun f t n s ↦ fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ)) T.Index :=
  rootedTileCampbellMeanIdentification_of_tilePopValue (T := T) sample G g X Y
    scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileSingleConvergence_of_inProbability (T := T) (fun _ _ c ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      sample X Y scale hprobe A hsingle)

/-- **The two-sided identification of the pressure lower readout with the
single-tile law in probabilistic form.**

All deterministic tile hypotheses of the readout identification are now
discharged: the only remaining lane inputs are the probabilistic single-tile
counting law hsingle, tile integrability hint, the frozen gluing/decomposition
hgt/hdecomp, the empirical mean limit hlim and the assembled readout identity
hread. -/
theorem pressureLower_eq_sceneReadout_of_rootedTileSingleConvergenceInProbability
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
    (hu : let _instSingleProbReadoutMetric : MetricSpace M := F.metricSpace;
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
    (hsingle : T.RootedTileSingleConvergenceInProbability
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
  pressureLower_eq_sceneReadout_of_rootedTileSingleConvergence (T := T) sample G g
    X Y scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp
    (rootedTileSingleConvergence_of_inProbability (T := T) (fun _ _ c ↦
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      sample X Y scale hprobe A hsingle) pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction