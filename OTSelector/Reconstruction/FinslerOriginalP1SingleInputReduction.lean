import OTSelector.Reconstruction.FinslerOriginalMeasurablePressureLimitReduction
import OTSelector.Reconstruction.FinslerOriginalEllipticRootwiseGluingBridge

/-!
# P1 with a single pA-free measured-pressure input

This module eliminates the dummy function binder `pA` from the P1 block of
FinslerOriginalPaperTheoremFinalV8/V9.  In V8/V9 the block is

  `(pA : FinalProbeSpace A B → ℝ → ℝ)`
  `(hFocal : FocalValueEquality pA Ag fg α β)`
  `(hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)`
  `(hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)`

and `pA` occurs ONLY in `hFocal` (the paper step `I_w = pA`) and `hLimit`
(the paper step `pA = P_2`); the only consumer is
`populationFocalValueLimit_of_measurablePressureLimit`, which composes them into
P1 (`I_w = P_w`).  Hence the pair (`hFocal`, `hLimit`) is the single
pA-free identity `I_w = P_2`, and `pA` can be taken to be the measured
population pressure itself.

The pA-free identity is recorded as `AtlasMeasuredFocalPressure` (the name
`AtlasMeasuredPressureLimit` is already occupied by the finite-pressure
convergence statement in FinslerOriginalMeasurablePressureLimitReduction; the
relation between the two is proved below as
`exists_pA_measurablePressureLimit_iff_atlasMeasuredPressureLimit`).

Main declarations:

* `exists_pA_focal_and_limit_iff_atlasMeasuredPressureLimit` — the pair
  `(hFocal, hLimit)` is equivalent to the single pA-free input;
* `populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_root` — P1 from
  the single input plus the rootwise gluing;
* `populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_ellipticRayData`
  — the same with the rootwise gluing discharged by `UniformEllipticRayData`
  (FinslerOriginalEllipticRootwiseGluingBridge);
* `atlasMeasuredFocalPressure_iff_populationFocalValueLimit_of_root` — the
  single input is equivalent to P1 given the rootwise gluing (no loss);
* `exists_pA_measurablePressureLimit_iff_atlasMeasuredPressureLimit` and
  `exists_pA_focal_and_limit_iff_atlasMeasuredPressureLimit_of_pressure` — the
  same elimination for the literal `AtlasMeasuredPressureLimit` of the lane,
  which additionally takes the finite-pressure family.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.PointProcess
  OTSelector.PointProcess.StationaryForwardMatching OTSelector.Probability
open scoped Topology NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M}

/-! ## The pA-free single measured-pressure input -/

/-- **The pA-free form of the P1 block.**  The atlas weighted stationary
pressure equals the measured population second-moment pressure at every probe
and tilt.  This is the identity `I_w = P_2`, i.e. the pair `hFocal`
(`I_w = pA`) and `hLimit` (`pA = P_2`) after eliminating the dummy function
`pA`, which is simply the measured population pressure itself. -/
def AtlasMeasuredFocalPressure
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    weightedStationaryPressure α β (Ag φ) (fg φ) t =
      populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t

/-- **The P1 block with pA eliminated.**  There exists a function `pA` making
the focal-value equality `I_w = pA` and the measured pressure limit
`pA = P_2` both hold if and only if the pA-free measured identity
`I_w = P_2` holds.  The forward direction composes the two equalities; the
converse takes the measured population pressure itself as `pA`. -/
theorem exists_pA_focal_and_limit_iff_atlasMeasuredPressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    (∃ pA : FinalProbeSpace A B → ℝ → ℝ,
        FocalValueEquality pA Ag fg α β ∧
          MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) ↔
      AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q := by
  constructor
  · rintro ⟨pA, hFocal, hLimit⟩ φ t
    rw [hFocal φ t, hLimit φ t]
  · intro h
    exact
      ⟨fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t,
        fun φ t => h φ t, fun φ t => rfl⟩

/-! ## P1 from the single input and the rootwise gluing -/

/-- **P1 from the pA-free single input and the rootwise gluing.**  This replaces
the four binders `pA`, `hFocal`, `hLimit`, `hRoot` of V8/V9 by the single
pA-free input `hAtlasLimit` plus `hRoot`: the identity `I_w = P_2` and the
rootwise gluing `P_2 = P_w` compose to P1 `I_w = P_w`. -/
theorem populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_root
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hAtlasLimit : AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q := by
  intro φ t
  exact (hAtlasLimit φ t).trans
    (campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe
      hRoot φ t).symm

/-- **The single input is equivalent to P1 given the rootwise gluing.**  The
reduction to the pA-free input loses nothing: with `hRoot` proved (e.g. by the
elliptic ray data), the single measured identity and P1 are the same input. -/
theorem atlasMeasuredFocalPressure_iff_populationFocalValueLimit_of_root
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q ↔
      PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  ⟨fun hAtlasLimit =>
      populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_root
        Seed a κ lambda α β Ag fg coef probeFam q hAtlasLimit hRoot,
    fun hP1 φ t =>
      (hP1 φ t).trans
        (campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe
          hRoot φ t)⟩

/-! ## P1 from the single input and the elliptic ray data -/

/-- **P1 from the single measured input and `UniformEllipticRayData`.**  The
rootwise gluing `hRoot` is discharged by the ray data
(`perRootFocalValueEqualityAe_of_uniformEllipticRayData`), so P1 follows from
the single pA-free input, the ray data and the coefficient identification.  In
V8/V9 this replaces `pA`, `hFocal`, `hLimit`, `hRoot` by
`hAtlasLimit` plus the ray datum. -/
theorem populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_ellipticRayData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1))
    (hAtlasLimit : AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_root
    Seed a κ lambda α β Ag fg coef probeFam q hAtlasLimit
    (perRootFocalValueEqualityAe_of_uniformEllipticRayData Seed a κ lambda α β
      R idx coef probeFam hcoef hR_meas)

/-! ## Relation to the literal `AtlasMeasuredPressureLimit` of the lane -/

/-- **The literal lane form with pA eliminated.**  Given the finite-pressure
family `pressure`, the pair "pA is the finite-pressure limit and
`MeasurablePressureLimit` holds" is equivalent to the lane convergence
statement `AtlasMeasuredPressureLimit` of
FinslerOriginalMeasurablePressureLimitReduction (whose definition needs the
family explicitly).  The forward direction is the repo bridge; the converse
takes `pA` to be the measured population pressure. -/
theorem exists_pA_measurablePressureLimit_iff_atlasMeasuredPressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ) :
    (∃ pA : FinalProbeSpace A B → ℝ → ℝ,
        FinitePressureLimitAt pressure pA ∧
          MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) ↔
      AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q := by
  constructor
  · rintro ⟨pA, hPA, hLimit⟩
    exact atlasMeasuredPressureLimit_of_measurablePressureLimit Seed a κ lambda pA α β
      pressure coef probeFam q hPA hLimit
  · intro hAtlas
    exact
      ⟨fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t,
        hAtlas, fun φ t => rfl⟩

/-- **The full P1 block with pA eliminated in the literal lane form.**  The
existential over `pA` of the lane identification, the focal-value equality and
the measured pressure limit is equivalent to the lane convergence statement
`AtlasMeasuredPressureLimit` together with the pA-free measured identity. -/
theorem exists_pA_focal_and_limit_iff_atlasMeasuredPressureLimit_of_pressure
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ) :
    (∃ pA : FinalProbeSpace A B → ℝ → ℝ,
        FinitePressureLimitAt pressure pA ∧
          FocalValueEquality pA Ag fg α β ∧
            MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) ↔
      (AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q ∧
        AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q) := by
  constructor
  · rintro ⟨pA, hPA, hFocal, hLimit⟩
    exact
      ⟨(exists_pA_measurablePressureLimit_iff_atlasMeasuredPressureLimit
          Seed a κ lambda α β coef probeFam q pressure).mp ⟨pA, hPA, hLimit⟩,
        (exists_pA_focal_and_limit_iff_atlasMeasuredPressureLimit
          Seed a κ lambda α β Ag fg coef probeFam q).mp ⟨pA, hFocal, hLimit⟩⟩
  · rintro ⟨hAtlas, hMerged⟩
    obtain ⟨pA, hPA, hLimit⟩ :=
      (exists_pA_measurablePressureLimit_iff_atlasMeasuredPressureLimit
        Seed a κ lambda α β coef probeFam q pressure).mpr hAtlas
    exact
      ⟨pA, hPA, fun φ t => (hMerged φ t).trans (hLimit φ t).symm, hLimit⟩

end OTSelector.Reconstruction
