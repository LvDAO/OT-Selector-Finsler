import OTSelector.Reconstruction.FinslerOriginalAtlasCampbellIdentification
import OTSelector.Reconstruction.FinslerOriginalFrozenCampbellReadoutReduction
import OTSelector.Reconstruction.FinslerOriginalFrozenStationaryPressureIdentification

/-!
# The global pressure-readout identification from the frozen Campbell readout

The last residual of the population gluing lane is
AtlasGlobalPressureReadoutIdentification: the weighted stationary pressure of the
global probe equals the assembled limiting Palm readout Psi at every probe and
tilt.  This module gives the exact definitional chain from the weighted
stationary pressure to Psi and reduces the residual to one equality with the
frozen rooted cost readout of the limiting rooted scene.

The chain, with the cost of each link:

* weightedStationaryPressure alpha beta (Ag f) (fg f) t is the infimum of the
  Palm kinetic plus tilt times Palm probe readout over the weighted class
  (weightedStationaryPressure_eq_sInf, definitional);
* it equals the weighted readout (datum f).Iw t of the canonical stationary
  datum family (stationaryDatumFamily_Iw, proved in FinslerOriginalFocalValueLimit);
* the readout equals the Campbell averaged per-root stationary pressure by the
  population stationary readout identification N1 (the paper input, the
  residual of that module);
* that Campbell average equals the Campbell averaged frozen cost of the
  per-root frozen readout family by N2, the per-root frozen stationary readout
  identification, through the Campbell integration transfer
  campbellAveragedStationaryPressure_eq_campbellAveragedFrozenCost_of_ae;
* the frozen lower pressure of the frozen family is definitionally the
  Campbell averaged frozen cost (frozenPressureLower), and the frozen scene
  collapse of FinslerOriginalAtlasCampbellIdentification identifies that
  frozen lower pressure with the assembled Palm readout Psi, here proved at the
  atlas frozen rooted cost readout of the scene (atlasFrozenRootedCostReadout).

Consequently the global readout identification is equivalent to the frozen
Campbell pressure identification: the global weighted stationary pressure is
the Campbell average of the atlas frozen rooted cost readout.  This is exactly
the frozen Campbell readout FrozenCampbellReadout of the frozen lane once the
datum readout link is granted, and it splits into N1 + N2 by the repository
reduction frozenCampbellReadout_of_identifications.  The frozen scene data of
this module supplies the frozen collapse, N2 is supplied by the repository from
FrozenMatchingMinimality
(frozenStationaryPressureIdentification_of_frozenMatchingMinimality), and the
legal pressure-value equality of FinslerOriginalLegalPressureValueEquality
identifies the weighted and second-moment legal values but never involves Psi,
so it does not close the readout equality by itself: the residual below is the
sharpest single equality reachable from the existing modules.

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

/-! ## The frozen Campbell pressure identification -/

/-- **The atlas frozen Campbell pressure identification.**  The weighted
stationary pressure of the global probe is the Campbell averaged frozen cost of
the frozen rooted cost readout of the limiting rooted scene.  This is the
frozen Campbell readout of the lane with the datum readout link inlined: it is
the single equality to which the global pressure-readout identification
reduces. -/
def AtlasFrozenCampbellPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    weightedStationaryPressure α β (Ag φ) (fg φ) t =
      campbellAveragedFrozenCost Seed a κ lambda (g φ t) q

/-- **The atlas frozen rooted cost readout.**  The piecewise frozen cost of the
limiting rooted scene: on every selected population seed piece it is the Palm
frozen integrand of the scene root carrier.  This is the family whose Campbell
average the frozen scene collapse identifies with Psi. -/
noncomputable def atlasFrozenRootedCostReadout
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {hpalm : IsProbabilityMeasure (rootedScenePhysicalPalm Q)}
    (hforward : ∀ᵐ m ∂rootedScenePhysicalPalm Q, m.1.1 < m.1.2)
    (q : ℝ) : FinalProbeSpace A B → ℝ → Z → ℝ := by
  letI : IsProbabilityMeasure (rootedScenePhysicalPalm Q) := hpalm
  exact frozenRootedCostReadout (F := F) (u := u) (A := A) (B := B)
    (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
    ((rootedSceneRecodedPalm Q).map (fun p ↦ p.1.2))
    ((rootedSceneRecodedPalm Q).map (fun p ↦ p.2.2))
    coef probeFam (fun _ _ _ _ ↦ rootedSceneRootCarrier Q hforward) q

/-! ## The frozen scene collapse at the frozen rooted cost readout -/

/-- **The frozen lower pressure of the atlas frozen rooted cost readout is the
assembled Palm readout Psi.**  This is the frozen scene collapse of
FinslerOriginalAtlasCampbellIdentification instantiated at the frozen rooted
cost family instead of the atlas-glued stationary pressure family: all data
fields are shared, and the frozen gluing hypothesis is now proved from the
repository piecewise Palm identification frozenRootedCostReadout_of_mem. -/
theorem frozenPressureLower_atlasFrozenRootedCost_eq_sceneReadout
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q) :
    frozenPressureLower (K := A ∪ B) Seed a κ lambda
      (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
        (hpalm := data.hpalm) data.hforward q) q = data.Ψ := by
  haveI : IsProbabilityMeasure lambda := data.hprob
  haveI : ∀ j, SigmaFinite (κ j) := data.hsigma
  haveI : IsProbabilityMeasure (rootedScenePhysicalPalm data.Q) := data.hpalm
  exact frozenPressureLower_eq_sceneReadout_of_frozenData (K := A ∪ B) Seed a κ lambda
    (fun f _ j z ↦ coef f j z) (fun f _ j z ↦ probeFam f j z)
    (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
      (hpalm := data.hpalm) data.hforward q) (q := q) data.hq data.hF data.hcomplete
    data.hu data.ha data.hinj data.Q data.hforward data.hData (G := data.G) data.hG
    data.hMK
    (hglue := by
      intro f t j
      filter_upwards [frozenRootedCostReadout_ae_identification (Seed := Seed) (a := a)
        (κ := κ) (lambda := lambda) (hF := data.hF) (hcomplete := data.hcomplete)
        (hu := data.hu) (ha := data.ha) (hinj := data.hinj)
        ((rootedSceneRecodedPalm data.Q).map (fun p ↦ p.1.2))
        ((rootedSceneRecodedPalm data.Q).map (fun p ↦ p.2.2))
        coef probeFam (fun _ _ _ _ ↦ rootedSceneRootCarrier data.Q data.hforward) q f t j]
        with z hz
      show frozenRootedCostReadout (F := F) (u := u) (A := A) (B := B)
        (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        ((rootedSceneRecodedPalm data.Q).map (fun p ↦ p.1.2))
        ((rootedSceneRecodedPalm data.Q).map (fun p ↦ p.2.2))
        coef probeFam (fun _ _ _ _ ↦ rootedSceneRootCarrier data.Q data.hforward) q f t z =
        atlasRootFrozenIntegrand
          ((rootedSceneRecodedPalm data.Q).map (fun p ↦ p.1.2))
          ((rootedSceneRecodedPalm data.Q).map (fun p ↦ p.2.2))
          Seed a κ lambda (fun f' _ j z ↦ coef f' j z)
          (fun f' _ j z ↦ probeFam f' j z)
          (fun _ _ _ _ ↦ rootedSceneRootCarrier data.Q data.hforward) q t f j z
      rw [hz]
      rfl)
    data.hcover data.hunithaar data.Ψ data.hconst

/-! ## The reduction of the global readout identification -/

/-- **The global pressure-readout identification is the frozen Campbell
pressure identification.**  Once the frozen scene collapse gives the Palm
readout Psi as the frozen lower pressure of the atlas frozen rooted cost
readout, the two pointwise equalities differ only by this identification: no
analytic content is used. -/
theorem atlasGlobalPressureReadout_iff_frozenCampbellPressure
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q) :
    AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg data.Ψ ↔
      AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg
        (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
          (hpalm := data.hpalm) data.hforward q) q := by
  have hC : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      campbellAveragedFrozenCost Seed a κ lambda
        (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
          (hpalm := data.hpalm) data.hforward q φ t) q = data.Ψ φ t :=
    fun φ t ↦ congrFun (congrFun
      (frozenPressureLower_atlasFrozenRootedCost_eq_sceneReadout Seed a κ lambda α β
        coef probeFam q data) φ) t
  constructor
  · intro h φ t
    rw [h φ t, hC φ t]
  · intro h φ t
    rw [h φ t, hC φ t]

/-- **The frozen Campbell pressure identification is the frozen Campbell
readout of the frozen lane.**  Given the datum readout link, which for the
canonical stationary datum family is the repository theorem
stationaryDatumFamily_Iw, the two residual formulations coincide. -/
theorem frozenCampbellPressure_iff_frozenCampbellReadout_of_datum
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t) :
    AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg g q ↔
      FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
        g q datum := by
  constructor
  · intro h φ t
    rw [hDatum φ t]
    exact (h φ t).symm
  · intro h φ t
    exact (hDatum φ t).symm.trans (h φ t).symm

/-- **The frozen Campbell pressure identification splits into the two paper
identities of the frozen lane.**  Given the per-root frozen stationary readout
identification N2, the residual is exactly the population stationary readout
identification N1: the datum readout is the Campbell averaged stationary
pressure.  The Campbell integration transfer is proved in the repository. -/
theorem frozenCampbellPressure_iff_atlasStationaryPressureIdentification
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g α β coef probeFam q) :
    AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg g q ↔
      AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q := by
  constructor
  · intro h φ t
    rw [hDatum φ t, h φ t]
    exact (campbellAveragedStationaryPressure_eq_campbellAveragedFrozenCost_of_ae
      (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) α β (coef φ) (probeFam φ)
      (g φ t) (hN2 φ t)).symm
  · intro h φ t
    rw [← hDatum φ t, h φ t]
    exact campbellAveragedStationaryPressure_eq_campbellAveragedFrozenCost_of_ae
      (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) α β (coef φ) (probeFam φ)
      (g φ t) (hN2 φ t)

/-- **The chain: the frozen Campbell pressure identification implies the global
pressure-readout identification.**  This is the exact definitional chain from
the weighted stationary pressure to Psi: weighted stationary pressure, datum
readout, Campbell average of the frozen rooted cost readout, frozen lower
pressure, assembled Palm readout. -/
theorem atlasGlobalPressureReadout_of_frozenCampbellPressure
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q)
    (h : AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg
      (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
        (hpalm := data.hpalm) data.hforward q) q) :
    AtlasGlobalPressureReadoutIdentification Seed a κ lambda α β Ag fg data.Ψ :=
  (atlasGlobalPressureReadout_iff_frozenCampbellPressure Seed a κ lambda α β Ag fg
    coef probeFam q data).mpr h

/-- **P1 is equivalent to the frozen Campbell pressure identification.**  Given
the paper frozen scene data, the population gluing identity is exactly the
statement that the global weighted stationary pressure is the Campbell average
of the atlas frozen rooted cost readout of the limiting rooted scene. -/
theorem populationFocalValueLimit_iff_frozenCampbellPressure_of_frozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg
        (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
          (hpalm := data.hpalm) data.hforward q) q := by
  rw [populationFocalValueLimit_iff_globalPressureReadout_of_frozenSceneData
    Seed a κ lambda α β Ag fg coef probeFam q data]
  exact atlasGlobalPressureReadout_iff_frozenCampbellPressure Seed a κ lambda α β Ag fg
    coef probeFam q data

/-- **P1 from the frozen Campbell pressure identification.** -/
theorem populationFocalValueLimit_of_frozenCampbellPressure_of_frozenSceneData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (data : AtlasFrozenSceneData (ι := ι) Seed a κ lambda α β coef probeFam q)
    (h : AtlasFrozenCampbellPressureIdentification Seed a κ lambda α β Ag fg
      (atlasFrozenRootedCostReadout Seed a κ lambda coef probeFam data.Q
        (hpalm := data.hpalm) data.hforward q) q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  (populationFocalValueLimit_iff_frozenCampbellPressure_of_frozenSceneData Seed a κ
    lambda α β Ag fg coef probeFam q data).mpr h

end OTSelector.Reconstruction
