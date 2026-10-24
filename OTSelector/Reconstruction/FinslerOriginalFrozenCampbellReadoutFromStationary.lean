import OTSelector.Reconstruction.FinslerOriginalGlobalPressureReadout
import OTSelector.Reconstruction.FinslerOriginalFrozenAttainment

/-!
# Frozen Campbell readout from the population stationary readout identification

The last residual of the population gluing lane, isolated in
FinslerOriginalGlobalPressureReadout, is the frozen Campbell pressure
identification: the global weighted stationary pressure is the Campbell average
of the atlas frozen rooted cost readout.  This module closes that residual from
the two paper-level inputs of the frozen lane and the repository datum:

* N1, the population stationary readout identification
  AtlasStationaryPressureIdentification: the weighted readout of the stationary
  datum family is the Campbell averaged per-root stationary pressure;
* N2, the per-root frozen stationary readout identification
  FrozenStationaryPressureIdentification: at almost every root of every piece
  the weighted stationary pressure at the scaled tilt is the frozen cost;
* the datum readout link, which for the canonical stationary datum family is the
  repository theorem stationaryDatumFamily_Iw.

What is proved here:

1. P1 is exactly N1 once the datum readout link is granted
   (populationFocalValueLimit_iff_atlasStationaryPressureIdentification_of_datum),
   hence P1 follows from N1 (populationFocalValueLimit_of_atlasStationaryPressureIdentification).
2. N1 plus N2 give the frozen Campbell readout
   (frozenCampbellReadout_of_atlasStationaryPressureIdentification), hence the
   frozen Campbell pressure identification and the global pressure-readout
   identification with the frozen scene data.
3. N2 is the repository consequence of the frozen matching minimality
   (frozenStationaryPressureIdentification_atlasFrozenRootedCost_of_frozenMatchingMinimality);
   composing it with 2 closes the FrozenCampbellReadout residual of the atlas
   frozen rooted cost readout
   (frozenCampbellReadout_atlasFrozenRootedCost_of_atlasStationaryPressureIdentification).

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  [Fintype ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M}

/-! ## The recoded mark laws of the limiting rooted scene -/

/-- The first recoded mark law of the limiting rooted scene. -/
noncomputable def rootedSceneRecodedFirstMark
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure OTSelector.UnitMark :=
  (rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2)

/-- The second recoded mark law of the limiting rooted scene. -/
noncomputable def rootedSceneRecodedSecondMark
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    Measure OTSelector.UnitMark :=
  (rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2)

/-! ## P1 from the population stationary readout identification -/

/-- **P1 is exactly the population stationary readout identification N1** once
the datum readout link is granted. -/
theorem populationFocalValueLimit_iff_atlasStationaryPressureIdentification_of_datum
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q := by
  constructor
  · intro h φ t
    rw [hDatum φ t]
    exact h φ t
  · intro h φ t
    exact (hDatum φ t).symm.trans (h φ t)

/-- **P1 from the population stationary readout identification N1.** -/
theorem populationFocalValueLimit_of_atlasStationaryPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hN1 : AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q := by
  intro φ t
  exact (hDatum φ t).symm.trans (hN1 φ t)

/-! ## The frozen Campbell readout from N1 and N2 -/

/-- **N1 and N2 give the frozen Campbell readout.**  The datum readout is the
Campbell averaged stationary pressure by N1; the Campbell integration transfer
of N2 identifies that average with the Campbell averaged frozen cost. -/
theorem frozenCampbellReadout_of_atlasStationaryPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hN1 : AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q)
    (hN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g α β coef probeFam q) :
    FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      g q datum := by
  intro φ t
  have htransfer := campbellAveragedStationaryPressure_eq_campbellAveragedFrozenCost_of_ae
    (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) α β (coef φ) (probeFam φ)
    (g φ t) (hN2 φ t)
  exact htransfer.symm.trans (hN1 φ t).symm

/-- **The frozen Campbell pressure identification from the frozen Campbell
readout and the datum link.** -/
theorem atlasFrozenCampbellPressureIdentification_of_frozenCampbellReadout_of_datum
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (h : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      g q datum) :
    AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg g q := by
  intro φ t
  rw [h φ t, hDatum φ t]

/-- **The frozen Campbell pressure identification from N1, N2 and the datum
link.**  This is the single equality: the global weighted stationary pressure
is the Campbell average of the frozen root readout. -/
theorem atlasFrozenCampbellPressureIdentification_of_atlasStationaryPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hN1 : AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q)
    (hN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g α β coef probeFam q) :
    AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg g q :=
  atlasFrozenCampbellPressureIdentification_of_frozenCampbellReadout_of_datum
    Seed a κ lambda α β Ag fg g q datum hDatum
    (frozenCampbellReadout_of_atlasStationaryPressureIdentification Seed a κ lambda
      α β coef probeFam g q datum hN1 hN2)

/-! ## The frozen matching minimality supplies N2 -/

/-- **N2 for the atlas frozen rooted cost readout from the frozen matching
minimality.**  This is the repository theorem
frozenStationaryPressureIdentification_of_frozenMatchingMinimality instantiated
at the scene root carrier, with the frozen readout family read through the
atlas frozen rooted cost readout. -/
theorem frozenStationaryPressureIdentification_atlasFrozenRootedCost_of_frozenMatchingMinimality
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [hpalm : IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenMinimalityMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) (rootedSceneRootCarrier Q hforward))
    (hA : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hf : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ probeFam φ j z p.1 p.2))
    (hG : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hmin : FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (rootedSceneRecodedFirstMark Q)
      (rootedSceneRecodedSecondMark Q) coef probeFam
      (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q) :
    FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda)
      (g := atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam Q
        (hpalm := hpalm) hforward q)
      (rootedSceneRecodedFirstMark Q) (rootedSceneRecodedSecondMark Q)
      coef probeFam q :=
  frozenStationaryPressureIdentification_of_frozenMatchingMinimality
    (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
    hF hcomplete hu ha hinj (rootedSceneRecodedFirstMark Q)
    (rootedSceneRecodedSecondMark Q) coef probeFam
    (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q hM hA hf hG hmin

/-! ## The closed residual -/

/-- **The frozen Campbell readout of the atlas frozen rooted cost readout from
N1 and the frozen matching minimality.**  This is the last P1 equality closed
from the two paper-level inputs and the repository datum. -/
theorem frozenCampbellReadout_atlasFrozenRootedCost_of_atlasStationaryPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    [hpalm : IsProbabilityMeasure (rootedScenePhysicalPalm Q)]
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenReadoutMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hM : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      FiniteWeightedKinetic (coef φ j z) (rootedSceneRootCarrier Q hforward))
    (hA : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ coef φ j z x y)
    (hf : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ probeFam φ j z p.1 p.2))
    (hG : ∃ Gc : ℝ, ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ) (z : Z)
      (x y : MarkedCloudPoint), |probeFam φ j z x y| ≤ Gc)
    (hmin : FrozenMatchingMinimality (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (rootedSceneRecodedFirstMark Q)
      (rootedSceneRecodedSecondMark Q) coef probeFam
      (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q)
    {W : Type*} {Gfinal Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W Gfinal Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure (rootedSceneRecodedFirstMark Q)
        (rootedSceneRecodedSecondMark Q) (Ag φ) (fg φ) t)
    (hN1 : AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := Gfinal) (Cb := Cb)
      (rootedSceneRecodedFirstMark Q) (rootedSceneRecodedSecondMark Q)
      datum coef probeFam q) :
    FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
      (g := atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam Q
        (hpalm := hpalm) hforward q) q datum :=
  frozenCampbellReadout_of_atlasStationaryPressureIdentification Seed a κ lambda
    (rootedSceneRecodedFirstMark Q) (rootedSceneRecodedSecondMark Q) coef probeFam
    (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam Q
      (hpalm := hpalm) hforward q) q datum hN1
    (frozenStationaryPressureIdentification_atlasFrozenRootedCost_of_frozenMatchingMinimality
      Seed a κ lambda coef probeFam q Q hforward hF hcomplete hu ha hinj hM hA hf hG hmin)

/-! ## The Psi readout and P1 from the frozen scene data -/

/-- **The global pressure-readout identification from N1, N2 and the frozen
scene data.** -/
theorem atlasGlobalPressureReadout_of_atlasStationaryPressureIdentification_of_frozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hN1 : AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q)
    (hN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda)
      (g := atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
        (hpalm := data.hpalm) data.hforward q) α β coef probeFam q) :
    AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg data.Ψ :=
  atlasGlobalPressureReadout_of_frozenCampbellPressure Seed a κ lambda α β Ag fg
    coef probeFam q data
    (atlasFrozenCampbellPressureIdentification_of_atlasStationaryPressureIdentification
      Seed a κ lambda α β Ag fg coef probeFam
      (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
        (hpalm := data.hpalm) data.hforward q) q datum hDatum hN1 hN2)

/-- **P1 from N1, N2 and the frozen scene data.** -/
theorem populationFocalValueLimit_of_atlasStationaryPressureIdentification_of_frozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hN1 : AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q)
    (hN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda)
      (g := atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
        (hpalm := data.hpalm) data.hforward q) α β coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_frozenCampbellPressure_of_frozenSceneData Seed a κ
    lambda α β Ag fg coef probeFam q data
    (atlasFrozenCampbellPressureIdentification_of_atlasStationaryPressureIdentification
      Seed a κ lambda α β Ag fg coef probeFam
      (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
        (hpalm := data.hpalm) data.hforward q) q datum hDatum hN1 hN2)

end OTSelector.Reconstruction
