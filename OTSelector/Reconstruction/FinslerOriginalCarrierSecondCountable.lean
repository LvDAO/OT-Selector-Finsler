import OTSelector.Reconstruction.FinslerOriginalSceneProbeData
import OTSelector.Geometry.Finsler.HopfRinow

/-!
# Second countability of the carrier in the population lane

FinslerOriginalSceneProbeData.lean proves the probe data of the physical scene
probe family under the structural hypothesis [SecondCountableTopology M]:
pointwise measurability of the probe kernel is obtained from measurability of the
bounded continuous carrier probe g : (K x K) ->b R, and that in turn is
automatic once the ambient space is second countable.

This module closes that structural gap.  It records the correct hypotheses for
second countability of the ambient manifold and of the compact carrier, derives
them from the data the population lane already assumes, and wires the probe data
of the physical scene probe family for the concrete carrier.

## Ambient second countability

The abstract lane context only contains TopologicalSpace M, ChartedSpace E M,
IsManifold, T2Space M and PreconnectedSpace M.  These alone do **not** imply
second countability: a charted Hausdorff preconnected manifold need not be
paracompact (the long line is a one-dimensional Hausdorff manifold with charts to
R that is not second countable).  So second countability is *not* silently
derivable; it is installed here from the following explicit named hypotheses.

* secondCountableTopology_of_sigmaCompact: the explicit structural hypothesis
  [SigmaCompactSpace M], together with a charted space over a second countable
  model space, gives SecondCountableTopology M
  (ChartedSpace.secondCountable_of_sigmaCompact).  For the population lane the
  model space is the finite dimensional E, which is second countable, so this is
  exactly the named structural hypothesis "M is sigma compact".
* secondCountableTopology_of_complete: completeness of the length metric
  (hcomplete : CompleteSpace M, an existing hypothesis of the population lane,
  used e.g. by the scene readout theorem) makes the length metric proper
  (ContinuousFinslerNorm.properSpace_of_complete), and a proper (pseudo)metric
  space is second countable.  Since F.metricSpace induces the given manifold
  topology definitionally (ContinuousFinslerNorm.metricSpace_topology), this
  gives SecondCountableTopology M for the ambient topology.  **In the actual
  physical scene this closes the gap without any new assumption.**

## The compact carrier

For the actual compact carrier K (a finite union of supports, compact in the
physical scene) second countability is available unconditionally:
secondCountableTopology_carrier_of_isCompact derives SecondCountableTopology K
from IsCompact K through compactness of the subtype metric space.  This is enough
for measurability of the carrier probe:
measurable_probe_of_carrier_secondCountable, measurable_probe_of_isCompact,
measurable_probe_of_complete.

## Wiring for the physical scene probe family

* measurable_physicalSceneProbeKernel_of_carrier_secondCountable,
  measurable_physicalSceneTileProbeKernel_of_carrier_secondCountable and their
  _of_complete versions: pointwise measurability of the physical probe pair
  kernels from the carrier or ambient second countability hypotheses.
* physicalSceneProbe_tilePairKernel_measurable_of_carrier_secondCountable: the
  measurability part of condition (ii) of the deep tile lane for the physical
  scene probe family, with carrier second countability instead of ambient second
  countability.
* physicalSceneProbe_tilePairKernel_data_of_carrier_secondCountable,
  physicalSceneProbe_tilePairKernel_data_of_complete,
  physicalSceneProbe_tilePairKernel_data_of_sigmaCompact,
  physicalSceneProbe_tilePairKernel_data_of_isCompact: the condition (ii) data
  (measurability and uniform bound of the masked tile pair kernel) for the
  physical probe family, under the corresponding second countability hypothesis.

## Exact remaining sub-gap

None for the actual physical scene: the lane already assumes completeness of the
length metric (and the actual carrier is compact), which supplies second
countability here.  The only irreducible statement is conditional: second
countability of the ambient manifold is not derivable from the abstract
charted-space fields alone (non-paracompact manifolds), so whenever the lane is
used without completeness or sigma compactness the hypotheses
[SigmaCompactSpace M] or [SecondCountableTopology ↥K] must be assumed
explicitly; they are named here, not hidden.

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
set_option linter.style.haveILetI false

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

/-! ## Ambient second countability -/

/-- **Ambient second countability from sigma compactness.**  If the ambient space
is a charted space over a second countable model space and is sigma compact
(equivalently, for manifolds, paracompact), then it is second countable.  For the
population lane the model space is the finite dimensional E, which is second
countable. -/
theorem secondCountableTopology_of_sigmaCompact {H : Type*} [TopologicalSpace H]
    [ChartedSpace H M] [SecondCountableTopology H] [SigmaCompactSpace M] :
    SecondCountableTopology M :=
  ChartedSpace.secondCountable_of_sigmaCompact H M

/-- **Ambient second countability from completeness of the length metric.**
Completeness of the Finsler length metric makes that metric proper, and a proper
metric space is second countable.  The constructed metric induces the given
manifold topology definitionally, so the ambient manifold is second countable.

This is the form that matches the actual population lane: hcomplete is an
existing hypothesis there (e.g. of the scene readout theorem), so this closes the
structural gap of FinslerOriginalSceneProbeData.lean without a new assumption. -/
theorem secondCountableTopology_of_complete
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) :
    SecondCountableTopology M := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  exact secondCountable_of_proper

/-! ## Second countability of the compact carrier -/

include E F in
/-- **Second countability of the compact carrier.**  A compact carrier K in the
physical scene is second countable as a topological space: the subtype metric
space is compact, hence proper, hence second countable. -/
theorem secondCountableTopology_carrier_of_isCompact {K : Set M}
    (hK : IsCompact K) : SecondCountableTopology ↥K := by
  letI : MetricSpace M := F.metricSpace
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  exact secondCountable_of_proper

/-! ## Measurability of the physical carrier probe -/

/-- **The carrier probe is measurable from carrier second countability.**  A
bounded continuous probe on the carrier K is measurable as soon as the carrier
itself is second countable. -/
theorem measurable_probe_of_carrier_secondCountable {K : Set M}
    [SecondCountableTopology ↥K] (g : (K × K) →ᵇ ℝ) : Measurable g :=
  g.continuous.measurable

include E F in
/-- **The carrier probe is measurable for the actual compact carrier.**  The
second countability of the carrier is derived from IsCompact K, so this needs no
assumption beyond compactness of the physical carrier. -/
theorem measurable_probe_of_isCompact {K : Set M} (hK : IsCompact K)
    (g : (K × K) →ᵇ ℝ) : Measurable g := by
  haveI : SecondCountableTopology ↥K :=
    secondCountableTopology_carrier_of_isCompact (F := F) hK
  exact measurable_probe_of_carrier_secondCountable g

/-- **The carrier probe is measurable from completeness of the length metric.**
This is the form used in the actual population lane, where hcomplete is already
assumed. -/
theorem measurable_probe_of_complete
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {K : Set M} (g : (K × K) →ᵇ ℝ) : Measurable g := by
  haveI : SecondCountableTopology M := secondCountableTopology_of_complete hcomplete
  exact measurable_probe_of_carrier_secondCountable g

include E F in
/-- **The carrier probe is measurable from sigma compactness.** -/
theorem measurable_probe_of_sigmaCompact [SigmaCompactSpace M] {K : Set M}
    (g : (K × K) →ᵇ ℝ) : Measurable g := by
  haveI : SecondCountableTopology M :=
    secondCountableTopology_of_sigmaCompact (H := E)
  exact measurable_probe_of_carrier_secondCountable g

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-! ## Pointwise measurability of the physical scene probe pair kernels -/

/-- **Pointwise measurability of the physical scene probe pair kernel** from
carrier second countability. -/
theorem measurable_physicalSceneProbeKernel_of_carrier_secondCountable
    {K : Set M} [SecondCountableTopology ↥K] (hK : MeasurableSet K)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) : ∀ c : T.Index,
    Measurable (physicalSceneProbeKernel g t n c) :=
  fun c ↦ measurable_physicalSceneProbeKernel hK g
    (measurable_probe_of_carrier_secondCountable g) t n c

/-- **Pointwise measurability of the physical scene probe pair kernel** from
completeness of the length metric. -/
theorem measurable_physicalSceneProbeKernel_of_complete
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {K : Set M} (hK : MeasurableSet K) (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) :
    ∀ c : T.Index, Measurable (physicalSceneProbeKernel g t n c) :=
  fun c ↦ measurable_physicalSceneProbeKernel hK g
    (measurable_probe_of_complete hcomplete g) t n c

/-- **Pointwise measurability of the normalized physical scene probe pair
kernel** from carrier second countability. -/
theorem measurable_physicalSceneTileProbeKernel_of_carrier_secondCountable
    {K : Set M} [SecondCountableTopology ↥K] (hK : MeasurableSet K)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) : ∀ c : T.Index,
    Measurable (physicalSceneTileProbeKernel g t n c) :=
  fun c ↦ measurable_physicalSceneTileProbeKernel hK g
    (measurable_probe_of_carrier_secondCountable g) t n c

/-- **Pointwise measurability of the normalized physical scene probe pair
kernel** from completeness of the length metric. -/
theorem measurable_physicalSceneTileProbeKernel_of_complete
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {K : Set M} (hK : MeasurableSet K) (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) :
    ∀ c : T.Index, Measurable (physicalSceneTileProbeKernel g t n c) :=
  fun c ↦ measurable_physicalSceneTileProbeKernel hK g
    (measurable_probe_of_complete hcomplete g) t n c

/-! ## Condition (ii) of the deep lane for the physical probe family -/

/-- **Condition (ii), measurability part, for the physical scene probe family,
from carrier second countability.**  The masked tile pair kernel of every tile
and every physical probe is measurable. -/
theorem physicalSceneProbe_tilePairKernel_measurable_of_carrier_secondCountable
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    [SecondCountableTopology ↥K]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCarrierSecondCountableMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hK : MeasurableSet K) (scale : ℕ → ℝ) :
    ∀ (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (scale n) t
        (physicalSceneTileProbeKernel g t n c)) := by
  intro g t n c
  exact tilePairKernel_measurable_of_probe (T := T) hF hcomplete hu ha hinj scale
    (physicalSceneTileProbeKernel (ι := T.Index))
    (fun g' t' n' c' ↦ measurable_physicalSceneTileProbeKernel hK g'
      (measurable_probe_of_carrier_secondCountable g') t' n' c') g t n c

/-- **Condition (ii) of the deep lane, packaged for the physical scene probe
family, from carrier second countability**: for every physical probe, tile and
tilt, the masked tile pair kernel is measurable and uniformly bounded. -/
theorem physicalSceneProbe_tilePairKernel_data_of_carrier_secondCountable
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    [SecondCountableTopology ↥K]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCarrierSecondCountableDataMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hK : MeasurableSet K) (scale : ℕ → ℝ)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (T.tilePairKernel c (scale n) t
        (physicalSceneTileProbeKernel g t n c)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
        |T.tilePairKernel c (scale n) t
          (physicalSceneTileProbeKernel g t n c) p| ≤ B :=
  ⟨physicalSceneProbe_tilePairKernel_measurable_of_carrier_secondCountable
      (T := T) hF hcomplete hu ha hinj hK scale g t n c,
    physicalSceneProbe_tilePairKernel_bound (T := T) scale g t n c⟩

/-- **Condition (ii) data for the physical scene probe family from completeness
of the length metric**: the form matching the actual population lane, where
hcomplete is already assumed. -/
theorem physicalSceneProbe_tilePairKernel_data_of_complete
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCompleteDataMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hK : MeasurableSet K) (scale : ℕ → ℝ)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (T.tilePairKernel c (scale n) t
        (physicalSceneTileProbeKernel g t n c)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
        |T.tilePairKernel c (scale n) t
          (physicalSceneTileProbeKernel g t n c) p| ≤ B := by
  haveI : SecondCountableTopology M := secondCountableTopology_of_complete hcomplete
  exact physicalSceneProbe_tilePairKernel_data (T := T) hF hcomplete hu ha hinj
    hK scale g t n c

/-- **Condition (ii) data for the physical scene probe family from sigma
compactness of the ambient manifold.** -/
theorem physicalSceneProbe_tilePairKernel_data_of_sigmaCompact
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    [SigmaCompactSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSigmaCompactDataMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hK : MeasurableSet K) (scale : ℕ → ℝ)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (T.tilePairKernel c (scale n) t
        (physicalSceneTileProbeKernel g t n c)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
        |T.tilePairKernel c (scale n) t
          (physicalSceneTileProbeKernel g t n c) p| ≤ B := by
  haveI : SecondCountableTopology M :=
    secondCountableTopology_of_sigmaCompact (H := E)
  exact physicalSceneProbe_tilePairKernel_data (T := T) hF hcomplete hu ha hinj
    hK scale g t n c

/-- **Condition (ii) data for the physical scene probe family for the actual
compact carrier**: K compact (a finite union of compact supports in the physical
scene) supplies second countability of the carrier, so the masked tile pair
kernel is measurable and uniformly bounded for every physical probe.  The
carrier measurability MeasurableSet K is derived from compactness. -/
theorem physicalSceneProbe_tilePairKernel_data_of_isCompact
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCompactCarrierDataMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hKc : IsCompact K) (scale : ℕ → ℝ)
    (g : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) :
    Measurable (T.tilePairKernel c (scale n) t
        (physicalSceneTileProbeKernel g t n c)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : M × M,
        |T.tilePairKernel c (scale n) t
          (physicalSceneTileProbeKernel g t n c) p| ≤ B := by
  haveI : SecondCountableTopology ↥K :=
    secondCountableTopology_carrier_of_isCompact (F := F) hKc
  have hK : MeasurableSet K := hKc.isClosed.measurableSet
  exact physicalSceneProbe_tilePairKernel_data_of_carrier_secondCountable
    (T := T) hF hcomplete hu ha hinj hK scale g t n c

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction

