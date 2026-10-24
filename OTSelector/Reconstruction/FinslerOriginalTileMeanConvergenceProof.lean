import OTSelector.Reconstruction.FinslerOriginalTileSingleConvergenceProof
import OTSelector.Reconstruction.FinslerOriginalPlanFreeTileLLN
import OTSelector.Reconstruction.FinslerOriginalUniformTileAverage

/-!
# Per-tile iid law of large numbers: TileMeanConvergence from the plan-free LLN

FinslerOriginalTileSingleConvergenceProof.lean reduced the two-sided readout
identification to the per-tile mean convergence input (a)
T.TileMeanConvergence: for each fixed retained Taylor tile,
  (∫ s, T.tileValue ... n c s ∂sample n) -> T.tilePopValue G c.

This module proves the exact ASSEMBLY of that input and isolates precisely what
remains analytic.

## The decomposition

The repo isolates the per-tile iid LLN in plan-free form, PlanFreeTileLLN
(FinslerOriginalPlanFreeTileLLN.lean: a named vanishing sequence), and the
plan-residual vanishing is reduced to plan-free average-cost control
PlanFreeAverageCostControl via tendsto_normalized_residual_zero_of_planFreeControl
(FinslerOriginalUniformTileAverage.lean).  Given the exact per-tile decomposition

  ∫ tileValue = tilePopValue + free n + residual n,

with free a plan-free LLN sequence and residual vanishing, the per-tile iid LLN
TileMeanConvergence follows by the assembly lemma
tileMeanConvergence_of_planFreeLLN_and_residual.

## Contents

* tileMeanConvergence_of_planFree: (a) from the exact per-tile plan-free
  decomposition with a vanishing residual.

* tileMeanConvergence_of_planFreeControl: the same with the residual vanishing
  DERIVED from plan-free average-cost control
  (PlanFreeAverageCostControl).

* rootedTileSingleConvergenceInProbability_of_planFree: the probabilistic
  single-tile counting law from the plan-free decomposition.

* pressureLower_eq_sceneReadout_of_planFreeControl: THE TWO-SIDED IDENTIFICATION
  pressureLower = Psi with the per-tile iid LLN discharged to the plan-free
  decomposition and plan-free average-cost control.

## Exact remaining sub-gap

The single remaining analytic statement is the plan-free per-tile LLN itself,
i.e. PlanFreeTileLLN (free f t c) for the plan-free uniform tile average of the
masked frozen kernel with random probe and the (n+1)^(2/q) normalization (named
input of FinslerOriginalPlanFreeTileLLN.lean), together with the exact per-tile
decomposition identity above.  Everything else in the readout chain is proved.

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

/-- **The per-tile iid LLN from the plan-free decomposition.**

If the expected plan-weighted frozen tile mean decomposes exactly as the tile
population value plus a plan-free LLN sequence plus a vanishing residual, then
the per-tile mean converges to the tile population value: this proves the named
input (a) T.TileMeanConvergence. -/
theorem tileMeanConvergence_of_planFree
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (free residual : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hplandec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      |(∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c -
        (free f t c n + residual f t c n)| ≤ 0)
    (hfree : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileLLN (free f t c))
    (hres : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ residual f t c n) atTop (𝓝 0)) :
    T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A := by
  intro f t c
  have h := tileMeanConvergence_of_planFreeLLN_and_residual
    (fun n ↦ ∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n)
    (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
    (free f t c) (residual f t c) (hplandec f t c) (hfree f t c) (hres f t c)
  have hconst : Tendsto (fun _ : ℕ ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) G c) atTop
      (𝓝 (T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)) :=
    tendsto_const_nhds
  have hadd := h.add hconst
  simpa [sub_add_cancel] using hadd

/-- **The per-tile iid LLN from plan-free average-cost control.**

Same as tileMeanConvergence_of_planFree, but the vanishing residual is DERIVED
from plan-free average-cost control: residual n = R n / (n+1), vanishing by
tendsto_normalized_residual_zero_of_planFreeControl. -/
theorem tileMeanConvergence_of_planFreeControl
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (free : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (R fac : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hplandec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      |(∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c -
        (free f t c n + R f t c n / ((n + 1 : ℕ) : ℝ))| ≤ 0)
    (hfree : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileLLN (free f t c))
    (hcontrol : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeAverageCostControl (R f t c) (fac f t c)) :
    T.TileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A :=
  tileMeanConvergence_of_planFree (T := T) sample G X Y scale hprobe A
    free (fun f t c n ↦ R f t c n / ((n + 1 : ℕ) : ℝ)) hplandec hfree
    (fun f t c ↦ tendsto_normalized_residual_zero_of_planFreeControl (R f t c)
      (fac f t c) (hcontrol f t c))

/-- **The probabilistic single-tile counting law from the plan-free
decomposition.** -/
theorem rootedTileSingleConvergenceInProbability_of_planFree
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (free residual : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hplandec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      |(∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c -
        (free f t c n + residual f t c n)| ≤ 0)
    (hfree : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileLLN (free f t c))
    (hres : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ residual f t c n) atTop (𝓝 0)) :
    T.RootedTileSingleConvergenceInProbability
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
        (q := q) G c) sample X Y scale hprobe A :=
  rootedTileSingleConvergenceInProbability_of_tileMeanConvergence (T := T)
    (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
      (q := q) G c) sample X Y scale hprobe A
    (tileMeanConvergence_of_planFree (T := T) sample G X Y scale hprobe A
      free residual hplandec hfree hres)

/-- **The two-sided identification of the pressure lower readout from the
plan-free per-tile LLN decomposition.**

The per-tile iid LLN input (a) is discharged to the plan-free decomposition: the
only remaining analytic statement is the plan-free per-tile LLN
PlanFreeTileLLN (free) plus the exact decomposition identity. -/
theorem pressureLower_eq_sceneReadout_of_planFreeControl
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (free residual : ((K × K) →ᵇ ℝ) → ℝ → T.Index → ℕ → ℝ)
    (hplandec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      |(∫ s, T.tileValue f t sample X Y scale hprobe A n c s ∂sample n) -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c -
        (free f t c n + residual f t c n)| ≤ 0)
    (hfree : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileLLN (free f t c))
    (hres : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ residual f t c n) atTop (𝓝 0))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileLLNMetric : MetricSpace M := F.metricSpace;
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
    (tileMeanConvergence_of_planFree (T := T) sample G X Y scale hprobe A
      free residual hplandec hfree hres)
    pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction