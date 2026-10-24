import OTSelector.Reconstruction.FinslerOriginalTileMaskedExchangeabilityInstance

/-!
# Concrete probe pair-functionality and pair-kernel regularity for the tile matrix

This module closes structural conditions (i) and (ii) of
FinslerOriginalTileMaskedExchangeabilityInstance.lean.

## What is concrete

The deep tile lane treats the probe as an abstract function
hprobe : ((K x K) ->b R) -> R -> forall n, Omega n -> T.Index -> Matrix (Fin (n+1)) (Fin (n+1)) R.
The concrete probe of the tile matrix is built from the original clock-pair model:
its (i, j) entry is the value of a pair kernel at the two sample points, so the
probe matrix is pair functional by construction.  The canonical such probe is
probeOfPairKernel below; condition (i) is its defining equation
probeOfPairKernel_apply (true by rfl).

Condition (ii) is PROVED from concrete regularity data:
* measurableSet_tileMaskPair: the tile mask is measurable from Measurable a,
  Measurable u and measurability of the cell and the pair window region;
* measurable_tileCostPair: the pair cost entry is measurable from measurability
  of the frozen physical cost as a function of the pair and of the probe kernel;
* measurable_tilePairKernel: condition (ii) measurability;
* tilePairKernel_abs_le: condition (ii) uniform bound from a bound on the pair
  cost entry.

## Contents

* probeOfPairKernel, probeOfPairKernel_apply: the concrete pair-functional tile
  probe and its defining identity (condition (i)).
* measurableSet_tileMaskPair, measurable_tileCostPair, measurable_tilePairKernel,
  tilePairKernel_abs_le: condition (ii), proved.
* pressureLower_eq_sceneReadout_of_concreteProbe: the two-sided readout
  identification with (ii) discharged and (i) only through the defining equation
  of the concrete probe.

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

/-- **The concrete pair-functional tile probe.**  The (i, j) entry of the probe
matrix of the retained tile is the value of the model pair kernel at the two
sample points.  This is the canonical concrete probe of the tile matrix, and it is
pair functional by construction. -/
def probeOfPairKernel
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (kernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ) :
    ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun f t n s c i j ↦ kernel f t n c (X n i s, Y n j s)

/-- **Condition (i) for the concrete probe**: its (i, j) entry is the value of
the pair kernel at the two sample points, by definition. -/
theorem probeOfPairKernel_apply
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (kernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) (c : T.Index)
    (i j : Fin (n + 1)) :
    T.probeOfPairKernel X Y kernel f t n s c i j =
      kernel f t n c (X n i s, Y n j s) := rfl

/-- **Condition (ii), mask part**: the tile mask is measurable from measurability
of a and u and measurability of the cell and of the pair window region. -/
theorem measurableSet_tileMaskPair (c : T.Index)
    (hcell : MeasurableSet ((T.partition c.1).cell c.2))
    (hregion : MeasurableSet ((T.core c).window.region))
    (ha : Measurable a) (hu : Measurable u) :
    MeasurableSet (T.tileMaskPair c) := by
  show MeasurableSet {p : M × M |
    a p.1 ∈ (T.partition c.1).cell c.2 ∧
      a p.2 ∈ (T.partition c.1).cell c.2 ∧
      (u p.1, u p.2) ∈ (T.core c).window.region}
  exact (hcell.preimage (ha.comp measurable_fst)).inter
    ((hcell.preimage (ha.comp measurable_snd)).inter
      (hregion.preimage ((hu.comp measurable_fst).prodMk (hu.comp measurable_snd))))

/-- **Condition (ii), cost part**: the pair cost entry is measurable from
measurability of the frozen physical cost (as a function of the pair) and of the
probe kernel. -/
theorem measurable_tileCostPair (c : T.Index) (scale t : ℝ)
    (probeKernel : M × M → ℝ)
    (hcost : Measurable (fun p : M × M ↦
      (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2))
    (hprobe : Measurable probeKernel) :
    Measurable (T.tileCostPair c scale t probeKernel) := by
  have hlin : Measurable (fun p : M × M ↦
      (1 - 2 * ε) * (scale * (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2) +
        t * probeKernel p) :=
    (((hcost.const_mul scale).const_mul (1 - 2 * ε)).add (hprobe.const_mul t))
  exact hlin.max measurable_const

/-- **Condition (ii), measurability**: the masked pair kernel of the tile is
measurable. -/
theorem measurable_tilePairKernel (c : T.Index) (scale t : ℝ)
    (probeKernel : M × M → ℝ)
    (hcell : MeasurableSet ((T.partition c.1).cell c.2))
    (hregion : MeasurableSet ((T.core c).window.region))
    (ha : Measurable a) (hu : Measurable u)
    (hcost : Measurable (fun p : M × M ↦
      (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2))
    (hprobe : Measurable probeKernel) :
    Measurable (T.tilePairKernel c scale t probeKernel) := by
  show Measurable ((T.tileMaskPair c).indicator
    (fun p ↦ T.tileCostPair c scale t probeKernel p))
  exact (measurable_tileCostPair (T := T) c scale t probeKernel hcost hprobe).indicator
    (measurableSet_tileMaskPair (T := T) c hcell hregion ha hu)

/-- **Condition (ii), bound**: a uniform bound on the pair cost entry gives a
uniform bound on the masked pair kernel. -/
theorem tilePairKernel_abs_le (c : T.Index) (scale t : ℝ)
    (probeKernel : M × M → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hcost : ∀ p : M × M, |T.tileCostPair c scale t probeKernel p| ≤ B) :
    ∀ p : M × M, |T.tilePairKernel c scale t probeKernel p| ≤ B := by
  intro p
  show |(T.tileMaskPair c).indicator
    (fun q ↦ T.tileCostPair c scale t probeKernel q) p| ≤ B
  by_cases h : p ∈ T.tileMaskPair c
  · rw [Set.indicator_of_mem h]
    exact hcost p
  · rw [Set.indicator_of_notMem h, abs_zero]
    exact hB0

/-- **The two-sided readout identification with condition (ii) discharged.**

All regularity of the masked pair kernel (measurability and uniform bound) is
PROVED here from concrete data: measurability of a, of u, of the tile cells and
pair windows, of the frozen physical cost as a pair function and of the probe
kernel, plus a uniform bound on the pair cost entry.  Condition (i) enters only
through the defining equation of the concrete probe probeOfPairKernel (or, more
generally, through the probe pair-functionality hypothesis hprobePair). -/
theorem pressureLower_eq_sceneReadout_of_concreteProbe
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
    (hcell : ∀ c : T.Index, MeasurableSet ((T.partition c.1).cell c.2))
    (hregion : ∀ c : T.Index, MeasurableSet ((T.core c).window.region))
    (hu_meas : Measurable u)
    (hcost_meas : ∀ (n : ℕ) (c : T.Index), Measurable (fun p : M × M ↦
      (T.core c).frozenPhysicalCost (T.reference c) p.1 p.2))
    (hprobe_meas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (probeKernel f t n c))
    (hcostBound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
        |T.tileCostPair c (scale n) t (probeKernel f t n c) p| ≤ B)
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
    (hu : let _instTileProbeConcreteMetric : MetricSpace M := F.metricSpace;
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
  pressureLower_eq_sceneReadout_of_pairFunctional (T := T) sample G X Y scale hprobe
    hX hY hXlaw hYlaw hpair probeKernel hprobePair
    (fun f t n c ↦ measurable_tilePairKernel (T := T) c (scale n) t
      (probeKernel f t n c) (hcell c) (hregion c) ha hu_meas
      (hcost_meas n c) (hprobe_meas f t n c))
    (fun f t n c ↦ by
      obtain ⟨B, hB0, hB⟩ := hcostBound f t n c
      exact ⟨B, tilePairKernel_abs_le (T := T) c (scale n) t
        (probeKernel f t n c) hB0 hB⟩)
    A hintEntry hid hintCost hintRes hresv g hF hcomplete hu ha hinj hint hgt hdecomp
    pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction