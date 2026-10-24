import OTSelector.Reconstruction.FinslerOriginalTileDecompositionIdentity
import OTSelector.Reconstruction.FinslerOriginalFixedPairIdentification

/-!
# Population identification of the scaled masked pair integral

The remaining source of the plan-free tile lane was the population identification of
the scaled masked pair integral: the normalized plan-free tile mean must converge to
T.tilePopValue.  This module proves the strongest true form of that identification
and identifies the exact remaining sub-gap.

## The identification

* The mask-coupling law (FinslerOriginalMaskCouplingLaw.planFreeTileMean_eq_fixedPair)
  says: under masked-entry exchangeability, the normalized plan-free tile mean
  (1/(n+1)^2) * uniformTilePart is EXACTLY the fixed-pair masked expectation
  E[tileCostMatrix s i0 j0].  This module instantiates it for the deep TaylorTiles
  context as uniformTilePart_eq_fixedPair.

* The remaining input is therefore the fixed-pair linear identification
  PlanFreeTileMeanIdentification (the Palm/stationary identification of the
  single-edge conditional law given mask membership, including the clipping
  correction): the fixed-pair expectation minus tilePopValue tends to zero under the
  (n+1)^(2/q) scale normalization.

* Given exchangeability and that fixed-pair identification, the population
  identification of the scaled masked pair integral is PROVED: it closes
  UniformTileAverageConvergence, hence TileMeanConvergence (via the plan residual
  vanishing), hence the two-sided readout identification.

## Contents

* tileFixedPair: the fixed-pair masked expectation E[tileCostMatrix s i0 j0].

* uniformTilePart_eq_fixedPair: the scaled masked pair integral equals the
  fixed-pair masked expectation (mask-coupling law instantiation).

* uniformTileAverageConvergence_of_fixedPairIdentification: the POPULATION
  IDENTIFICATION: the normalized plan-free tile mean converges to tilePopValue.

* tileMeanConvergence_of_fixedPair_and_residual: the per-tile iid LLN from the
  population identification, integrability and plan-residual vanishing.

* pressureLower_eq_sceneReadout_of_fixedPair_and_residual: THE TWO-SIDED
  IDENTIFICATION pressureLower = Psi, with the tile lane reduced to
  exchangeability, the fixed-pair linear identification and plan-residual
  vanishing.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
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

/-- **The fixed-pair masked expectation**: the expected masked frozen tile entry at
the distinguished pair (0,0), normalized by nothing (so that the scaled masked
pair integral equals it by exchangeability). -/
noncomputable def tileFixedPair
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index) : ℝ :=
  ∫ s, T.tileCostMatrix f t X Y scale hprobe n c s ⟨0, Nat.succ_pos n⟩
    ⟨0, Nat.succ_pos n⟩ ∂sample n

/-- **The population identification of the scaled masked pair integral.**

Under masked-entry exchangeability the normalized plan-free tile mean is the
fixed-pair masked expectation: this is the mask-coupling law
planFreeTileMean_eq_fixedPair instantiated for the deep TaylorTiles context. -/
theorem uniformTilePart_eq_fixedPair
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    (hint : ∀ i j : Fin (n + 1),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hExch : MaskedEntryExchangeability (sample n)
      (T.tileCostMatrix f t X Y scale hprobe n c)) :
    (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
        T.uniformTilePart f t sample X Y scale hprobe n c) =
      T.tileFixedPair f t sample X Y scale hprobe n c :=
  planFreeTileMean_eq_fixedPair (sample n) (Nat.succ_pos n)
    (T.tileCostMatrix f t X Y scale hprobe n c) hint hExch

/-- **The population identification closes the plan-free tile average
convergence.**

Given masked-entry exchangeability and the fixed-pair linear identification
(the Palm/stationary identification of the single-edge conditional law given mask
membership), the normalized plan-free tile mean converges to the tile population
value: UniformTileAverageConvergence is PROVED from these two named inputs. -/
theorem uniformTileAverageConvergence_of_fixedPairIdentification
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale hprobe n c))
    (hid : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileMeanIdentification
        (fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c)
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c)) :
    T.UniformTileAverageConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe := by
  intro f t c
  have hmean : ∀ n, (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
      T.uniformTilePart f t sample X Y scale hprobe n c) =
      T.tileFixedPair f t sample X Y scale hprobe n c :=
    fun n ↦ uniformTilePart_eq_fixedPair (T := T) sample f t X Y scale hprobe n c
      (hintEntry f t n c) (hExch f t n c)
  have hpp : PlanFreeTileLLN (fun n ↦
      (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
        T.uniformTilePart f t sample X Y scale hprobe n c) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
    planFreeTileLLN_of_fixedPairIdentification
      (fun n ↦ (1 / ((n + 1 : ℕ) : ℝ)) * ((1 / ((n + 1 : ℕ) : ℝ)) *
        T.uniformTilePart f t sample X Y scale hprobe n c))
      (fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c)
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) hmean (hid f t c)
  have hconst : Tendsto (fun _ : ℕ ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) G c) atTop
      (𝓝 (T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :=
    tendsto_const_nhds
  have hadd := hpp.add hconst
  simpa [sub_add_cancel, zero_add] using hadd

/-- **The per-tile iid LLN from the population identification.**

Combining the population identification of the scaled masked pair integral with the
plan-residual vanishing and integrability gives T.TileMeanConvergence. -/
theorem tileMeanConvergence_of_fixedPair_and_residual
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale hprobe n c))
    (hid : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileMeanIdentification
        (fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c)
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hresv : T.TilePlanResidualVanishing sample A X Y scale hprobe) :
    T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A :=
  tileMeanConvergence_of_uniform_and_residual (T := T) sample G X Y scale hprobe A
    hintCost hintRes
    (uniformTileAverageConvergence_of_fixedPairIdentification (T := T) sample G X Y
      scale hprobe hintEntry hExch hid)
    hresv

/-- **The two-sided identification of the pressure lower readout from the
population identification of the scaled masked pair integral.**

The tile lane is now reduced to: masked-entry exchangeability, the fixed-pair
linear identification (Palm/stationary identification of the single-edge
conditional law given mask membership, including the clipping correction), and
plan-residual vanishing.  All per-tile mean, single-tile counting, upper/lower
mean bounds and identification steps are PROVED. -/
theorem pressureLower_eq_sceneReadout_of_fixedPair_and_residual
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale hprobe n c))
    (hid : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileMeanIdentification
        (fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c)
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (A n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hresv : T.TilePlanResidualVanishing sample A X Y scale hprobe)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTilePopIdentMetric : MetricSpace M := F.metricSpace;
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
  pressureLower_eq_sceneReadout_of_uniform_and_residual (T := T) sample G X Y scale
    hprobe A hintCost hintRes
    (uniformTileAverageConvergence_of_fixedPairIdentification (T := T) sample G X Y
      scale hprobe hintEntry hExch hid)
    hresv g hF hcomplete hu ha hinj hint hgt hdecomp pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
