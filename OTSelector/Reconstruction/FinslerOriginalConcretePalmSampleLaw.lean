import OTSelector.Probability.EmpiricalMeasure
import OTSelector.Reconstruction.FinslerOriginalTilePalmSampleLaw

/-!
# The concrete scene sample lane for the tile Palm sample law

## What is built here

The tile lane carries its sample law abstractly (`sample : ∀ n, Measure (Ω n)`).
This module instantiates the lane with the CONCRETE empirical sample law of a scene
cloud, and computes the two paper-data fields of `TilePalmSampleLaw` for it.

* Sample space: `Ω n = Fin (n+1)`, the cloud slots.
* Sample law: `sceneCloudSample n = empiricalMeasure id`, the uniform measure on the
  `n+1` cloud slots — i.e. the empirical measure of the cloud (the scene's sampling
  law at sample level).
* Position arrays: `sceneCloudX p n i s = p n s` and `sceneCloudY q n j s = q n s`, so
  the distinguished pair `(0,0)` reads the cloud point at slot `s`.  A sample
  `s : Fin (n+1)` is therefore one edge of the cloud, and the sample law is
  exactly the empirical law of the cloud edges.

## Field (a) is COMPUTED, not assumed

For the empirical sample law the masked frozen cost sample mean is an explicit
finite average over the cloud edges:

```tileMaskedFrozenCostMean sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) n c
  = ((n+1 : ℕ) : ℝ)⁻¹ * ∑ s, tileMaskedFrozenCostIntegrand ... s```

(`tileMaskedFrozenCostMean_sceneCloud`), so field (a) of `TilePalmSampleLaw` holds
with the cloud readout
`palmCostMean n := ((n+1 : ℕ) : ℝ)⁻¹ * ∑ s, ...`, i.e. the paper's empirical tile
value.  Both fields are produced in `tilePalmSampleLaw_sceneCloud` from the single
scalar convergence `palm_readout`.

## The exact remaining paper input

Field (b), the population readout of the empirical tile value,
`(1 - 2ε) * (scale n * cloudReadout n) → tilePopValue`, is the sample-level Campbell
bridge: it is the *limit* statement relating the empirical tile mean to the
population Campbell value `tilePopValue` (paper identity, cf.
`campbellAveragedFrozenCost_eq_tileSum_add_tail` in
`FinslerOriginalTileCountingConvergence.lean`).  For the alternative iid product law
of positions this readout additionally carries the Palm density `θ^(-2/q)`, which
the repo constructs only abstractly for stationary point processes
(`OTSelector/PointProcess/StationaryForwardMatching.lean`); the empirical lane keeps
it as the explicit empirical tile value instead.  No `sorry`, `admit` or added
axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
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
namespace PopulationLocalPressureCore.TaylorTiles

/-! ## The concrete empirical scene sample lane -/

/-- The measurable space on the cloud slots (the discrete `⊤` σ-algebra). -/
instance sceneCloudMeasurableSpace : ∀ n, MeasurableSpace (Fin (n + 1)) :=
  fun n ↦ Fin.instMeasurableSpace (n + 1)

/-- **The concrete empirical sample law of the scene cloud**: the uniform empirical
measure on the `n+1` cloud slots. -/
noncomputable def sceneCloudSample (n : ℕ) : Measure (Fin (n + 1)) :=
  OTSelector.empiricalMeasure (fun i : Fin (n + 1) ↦ i)

instance sceneCloudSample_isProbability : ∀ n, IsProbabilityMeasure (sceneCloudSample n) :=
  fun n ↦ OTSelector.empiricalMeasure.instIsProbabilityMeasure (fun i : Fin (n + 1) ↦ i)

/-- The source position array of the cloud: slot `i` reads the cloud source at the
sample slot. -/
def sceneCloudX (p : ∀ n, Fin (n + 1) → M) :
    ∀ n, Fin (n + 1) → Fin (n + 1) → M :=
  fun n _ s ↦ p n s

/-- The target position array of the cloud. -/
def sceneCloudY (q : ∀ n, Fin (n + 1) → M) :
    ∀ n, Fin (n + 1) → Fin (n + 1) → M :=
  fun n _ s ↦ q n s

/-- **Field (a) computed for the concrete empirical lane**: the masked frozen cost
sample mean is the finite average of the masked cost over the cloud edges. -/
theorem tileMaskedFrozenCostMean_sceneCloud
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (n : ℕ) (c : T.Index) :
    T.tileMaskedFrozenCostMean sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) n c =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ s : Fin (n + 1),
          T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s := by
  rw [tileMaskedFrozenCostMean]
  exact OTSelector.integral_empiricalMeasure (fun i : Fin (n + 1) ↦ i)
    (f := fun s ↦ T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s)
    (Measurable.stronglyMeasurable (measurable_of_finite _))

/-- **The tile Palm sample law for the concrete empirical scene lane.**  Field (a) is
proved outright (the cloud average readout), and field (b) is the single scalar
sample-level Campbell convergence supplied by the caller. -/
noncomputable def tilePalmSampleLaw_sceneCloud
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (scale : ℕ → ℝ) (c : T.Index)
    (popVal : ℕ → ℝ)
    (hreadout : Tendsto (fun n ↦ (1 - 2 * ε) * (scale n *
      (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ s : Fin (n + 1),
        T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s)) -
      popVal n) atTop (𝓝 0)) :
    T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
      scale c popVal where
  palmCostMean := fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
    ∑ s : Fin (n + 1),
      T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s
  maskedMean_eq := fun n ↦ T.tileMaskedFrozenCostMean_sceneCloud pcloud qcloud n c
  palm_readout := hreadout

/-- **Field (a) in the paper's shape**: for any cloud readout sequence equal to the
empirical masked average, the sample mean of the masked frozen cost IS that
readout.  This is the content of the Palm-sample-law field (a) for the concrete
lane. -/
theorem tileMaskedFrozenCostMean_sceneCloud_eq_cloudReadout
    (pcloud qcloud : ∀ n, Fin (n + 1) → M) (n : ℕ) (c : T.Index)
    (cloudReadout : ℕ → ℝ)
    (hcloud : cloudReadout n = ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ s : Fin (n + 1),
        T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s) :
    T.tileMaskedFrozenCostMean sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) n c =
      cloudReadout n := by
  rw [T.tileMaskedFrozenCostMean_sceneCloud, ← hcloud]

/-- **The pressure-lower readout consumption for the concrete empirical lane**: the
linear Palm identification of the fixed-pair masked expectation at the paper's
`tileScale`, produced from the concrete sample law and the scalar Campbell readout. -/
theorem tileLinearPalmIdentification_sceneCloud
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ n, Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud)
        tileScale n c) (sceneCloudSample n))
    (hintP : ∀ n, Integrable (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud) (sceneCloudY qcloud)
      (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      (sceneCloudSample n))
    (G : ℕ → (ℚ → M) → ℝ)
    (hreadout : Tendsto (fun n ↦ (1 - 2 * ε) * (tileScale n *
      (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ s : Fin (n + 1),
        T.tileMaskedFrozenCostIntegrand (sceneCloudX pcloud) (sceneCloudY qcloud) n c s)) -
      T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) atTop (𝓝 0)) :
    Tendsto (fun n ↦
      T.tileFixedPairLinearPart f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud)
        tileScale (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c -
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      atTop (𝓝 0) :=
  T.tileLinearPalmIdentification_of_palmSampleLaw sceneCloudSample f t
    (sceneCloudX pcloud) (sceneCloudY qcloud) c base hBp hbase hintC hintP G
    (T.tilePalmSampleLaw_sceneCloud f t pcloud qcloud tileScale c
      (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      hreadout)

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
