import OTSelector.Reconstruction.FinslerOriginalTilePopValueIdentification
import OTSelector.Reconstruction.FinslerOriginalProbeSymmetry

/-!
# Concrete masked exchangeability for the tile matrix

This module closes input (a) of FinslerOriginalTilePopValueIdentification.lean:
MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale hprobe n c).

## The concrete pair functionals

The tile mask is a pair functional: the tile edgeEvent of the retained tile c is

  (i, j) in edgeEvent  iff  a (X i) in cell c  and  a (Y j) in cell c
    and  (u (X i), u (Y j)) in window.region,

and the tile reference (fun _ _ => T.reference c) is index-independent, so the
whole condition depends on the pair (X i, Y j) only.  It is packaged here as
tileMaskPair c : M x M -> Prop.

The frozen core entry is a pair functional once the probe matrix is: the frozen
core matrix entry is

  max ((1 - 2eps) * (k * frozenPhysicalCost (T.reference c) (X i) (Y j)) + t * h i j) 0,

so if the probe entry h i j is the value of a pair kernel at (X i s, Y j s), the
whole entry is a pair kernel too.  It is packaged here as tileCostPair and
tilePairKernel (the mask indicator of the pair entry).

## Contents

* tileMaskPair, tileCostPair, tilePairKernel: the concrete mask predicate and
  pair kernels.

* maskedEntryExchangeability_tileCostMatrix: THE CONCRETE EXCHANGEABILITY
  INSTANCE, instantiated from the repo theorem
  maskedEntryExchangeability_of_pairFunctional with the explicit pair
  functionality of the mask and of the probe.

* pressureLower_eq_sceneReadout_of_pairFunctional: the two-sided readout
  identification with the masked exchangeability discharged to the pair-functional
  structure of the concrete tile matrix.

## Exact remaining structural conditions

(i) the probe matrix of the retained tile is a pair functional,
    hprobe f t n s c i j = probeKernel f t n c (X n i s, Y n j s);
(ii) the pair kernel tilePairKernel is measurable and bounded on M x M.
Everything else is proved.

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

/-- **The tile mask as a pair predicate.**  The tile reference is
index-independent, so the edgeEvent condition depends on the pair only. -/
def tileMaskPair (c : T.Index) : Set (M × M) :=
  {p | a p.1 ∈ (T.partition c.1).cell c.2 ∧
    a p.2 ∈ (T.partition c.1).cell c.2 ∧
    (u p.1, u p.2) ∈ (T.core c).window.region}

/-- **The masked tile entry as a pair kernel.**  Given a pair functional probe,
the frozen core tile entry is the max of a clipped linear expression in the pair,
hence a pair kernel. -/
def tileCostPair (c : T.Index) (scale t : ℝ) (probeKernel : M × M → ℝ)
    (p : M × M) : ℝ :=
  max ((1 - 2 * ε) * (scale * (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2) +
    t * probeKernel p) 0

/-- **The masked pair kernel of the tile**: the indicator of the mask times the
pair entry. -/
def tilePairKernel (c : T.Index) (scale t : ℝ) (probeKernel : M × M → ℝ) :
    M × M → ℝ :=
  (T.tileMaskPair c).indicator (fun p => T.tileCostPair c scale t probeKernel p)

/-- **The concrete masked exchangeability instance for the tile matrix.**

This closes input (a) of the population identification: under the probability
structure of the iid sample (marginal laws and pairwise independence) and the pair
functionality of the probe, all masked frozen tile entries have equal
expectations. -/
theorem maskedEntryExchangeability_tileCostMatrix
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (n : ℕ) (c : T.Index)
    {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX : ∀ i, Measurable (X n i)) (hY : ∀ j, Measurable (Y n j))
    (hXlaw : ∀ i, (sample n).map (X n i) = μ)
    (hYlaw : ∀ j, (sample n).map (Y n j) = ν)
    (hpair : ∀ i j, IndepFun (X n i) (Y n j) (sample n))
    (probeKernel : M × M → ℝ)
    (hprobePair : ∀ (s : Ω n) (i j : Fin (n + 1)),
      hprobe f t n s c i j = probeKernel (X n i s, Y n j s))
    (hΨ : Measurable (T.tilePairKernel c (scale n) t probeKernel))
    {B : ℝ} (hΨb : ∀ p : M × M, |T.tilePairKernel c (scale n) t probeKernel p| ≤ B) :
    MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale hprobe n c) := by
  have hE : ∀ (s : Ω n) (i j : Fin (n + 1)),
      T.tileCostMatrix f t X Y scale hprobe n c s i j =
        T.tilePairKernel c (scale n) t probeKernel (X n i s, Y n j s) := by
    intro s i j
    have hd : frozenCoreMatrix (T.core c) ε (fun _ _ => T.reference c)
        (fun i => X n i s) (fun i => Y n i s) (scale n) t (hprobe f t n s c) i j =
        T.tileCostPair c (scale n) t probeKernel (X n i s, Y n j s) := by
      show max ((1 - 2 * ε) * ((scale n) * (T.core c).frozenPhysicalCost
          ((fun _ _ => T.reference c) i j) (X n i s) (Y n j s)) +
          t * hprobe f t n s c i j) 0 = _
      rw [hprobePair s i j]
      rfl
    show (T.edgeEvent (fun i => X n i s) (fun i => Y n i s) c).indicator
        (fun p => frozenCoreMatrix (T.core c) ε (fun _ _ => T.reference c)
          (fun i => X n i s) (fun i => Y n i s) (scale n) t (hprobe f t n s c) p.1 p.2)
        (i, j) = (T.tileMaskPair c).indicator
        (fun p => T.tileCostPair c (scale n) t probeKernel p) (X n i s, Y n j s)
    by_cases h : (i, j) ∈ T.edgeEvent (fun i => X n i s) (fun i => Y n i s) c
    · have hmem : (X n i s, Y n j s) ∈ T.tileMaskPair c := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem hmem]
      exact hd
    · have hmem : (X n i s, Y n j s) ∉ T.tileMaskPair c := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hmem]
  exact maskedEntryExchangeability_of_pairFunctional (X := X n) (Y := Y n)
    hX hY hXlaw hYlaw hpair _ _ hΨ hΨb hE

/-- **The concrete masked exchangeability instance, uniformly in the probe, the
tilt and the tile.** -/
theorem maskedEntryExchangeability_tileCostMatrix_forall
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {μ ν : ℕ → Measure M} [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)]
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)), Measurable (Y n j))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (sample n).map (X n i) = μ n)
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (sample n).map (Y n j) = ν n)
    (hpair : ∀ (n : ℕ) (i j : Fin (n + 1)), IndepFun (X n i) (Y n j) (sample n))
    (probeKernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobePair : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Ω n) (i j : Fin (n + 1)),
      hprobe f t n s c i j = probeKernel f t n c (X n i s, Y n j s))
    (hΨ : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (scale n) t (probeKernel f t n c)))
    (hΨb : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ B : ℝ, ∀ p : M × M, |T.tilePairKernel c (scale n) t (probeKernel f t n c) p| ≤ B) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale hprobe n c) := by
  intro f t n c
  obtain ⟨B, hB⟩ := hΨb f t n c
  exact maskedEntryExchangeability_tileCostMatrix (T := T) sample f t X Y scale
    hprobe n c (hX n) (hY n) (hXlaw n) (hYlaw n) (hpair n)
    (probeKernel f t n c) (hprobePair f t n c) (hΨ f t n c) hB

/-- **The two-sided readout identification with the masked exchangeability
discharged to the pair-functional structure of the concrete tile matrix.**

This closes input (a) of the population identification; the remaining analytic
inputs are the fixed-pair linear identification (Palm/stationary identification of
the single-edge conditional law given mask membership) and plan-residual
vanishing. -/
theorem pressureLower_eq_sceneReadout_of_pairFunctional
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {μ ν : ℕ → Measure M} [∀ n, IsProbabilityMeasure (μ n)]
    [∀ n, IsProbabilityMeasure (ν n)]
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)), Measurable (Y n j))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (sample n).map (X n i) = μ n)
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (sample n).map (Y n j) = ν n)
    (hpair : ∀ (n : ℕ) (i j : Fin (n + 1)), IndepFun (X n i) (Y n j) (sample n))
    (probeKernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobePair : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (s : Ω n) (i j : Fin (n + 1)),
      hprobe f t n s c i j = probeKernel f t n c (X n i s, Y n j s))
    (hΨ : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (scale n) t (probeKernel f t n c)))
    (hΨb : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ B : ℝ, ∀ p : M × M, |T.tilePairKernel c (scale n) t (probeKernel f t n c) p| ≤ B)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale hprobe n c s i j) (sample n))
    (hid : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      PlanFreeTileMeanIdentification
        (fun n ↦ T.tileFixedPair f t sample X Y scale hprobe n c)
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
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
    (hu : let _instTileMaskExchMetric : MetricSpace M := F.metricSpace;
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
  pressureLower_eq_sceneReadout_of_fixedPair_and_residual (T := T) sample G X Y scale
    hprobe hintEntry
    (maskedEntryExchangeability_tileCostMatrix_forall (T := T) sample X Y scale hprobe
      hX hY hXlaw hYlaw hpair probeKernel hprobePair hΨ hΨb)
    hid A hintCost hintRes hresv g hF hcomplete hu ha hinj hint hgt hdecomp
    pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction