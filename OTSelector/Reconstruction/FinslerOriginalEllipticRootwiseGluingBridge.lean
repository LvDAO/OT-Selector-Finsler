import OTSelector.Reconstruction.FinslerOriginalEllipticSeedProducer
import OTSelector.Reconstruction.FinslerOriginalAtlasStationaryIdentificationFromPressureLimit

/-!
# The elliptic rootwise-gluing bridge

This module bridges the geometric ellipticity datum `UniformEllipticRayData`
(FinslerOriginalEllipticSeedProducer) to the two downstream residuals of the
population focal-value chain,

* `hRoot` = `PerRootFocalValueEqualityAe` (rootwise gluing P_2 = P_w), and
* `hFocal` = `FocalValueEquality` (the paper step I_w = pA),

as they occur in FinslerOriginalAtlasStationaryIdentificationFromPressureLimit
and FinslerOriginalPaperTheoremFinalV8.  In V8 the residual list contains, among
others, `pA`, `hFocal`, `hLimit` and `hRoot`; the results below show that
`hRoot` is not an independent paper input in the uniformly elliptic regime, and
that, given the measured pressure limit `hLimit`, `hFocal` and the population
identity P1 are interchangeable.

The starting point is the repository identification
`weightedClass_eq_secondMomentClass_of_rayData`: the coefficient
`R.ellipticCoefficient phi` built from the ray data is globally sandwiched
between the uniform constants `c = lam/(right-left)` and
`C = Lambda/delta`, so the weighted and second-moment stationary classes
coincide.  Since the per-root pressures are the stationary values of those two
classes, the equality identifies them rootwise, at every root and tilt.

The declarations are:

1. `weightedClass_eq_secondMomentClass_of_rayData_at` — the class equality at a
   single ray-data index;
2. `weightedStationaryPressure_eq_secondMoment_of_rayData` — the corresponding
   per-coefficient pressure equality;
3. `perRootFocalValueEquality_of_uniformEllipticRayData` — the pointwise
   rootwise focal-value equality from ray data;
4. `perRootFocalValueEqualityAe_of_uniformEllipticRayData` — `hRoot` from ray
   data (the main deliverable);
5. `populationSecondMomentPressure_eq_campbellAveraged_of_uniformEllipticRayData`
   — the integrated gluing identity P_2 = P_w from ray data;
6. `populationFocalValueLimit_of_measurablePressureLimit_of_uniformEllipticRayData`
   — P1 from `hFocal` and `hLimit` with `hRoot` discharged by the ray data;
7. `focalValueEquality_of_populationFocalValueLimit_of_uniformEllipticRayData`
   — conversely, `hFocal` from P1 and `hLimit` plus the ray data, i.e. the
   focal-value identity is not an independent input once the measured pressure
   limit is known;
8. `populationFocalValueLimit_iff_focalValueEquality_of_uniformEllipticRayData`
   — the equivalence of the two global inputs.

The bridge hypotheses are: the index map `idx` assigning a ray-data parameter
to each (probe, root, population point), the coefficient identification
`hcoef : coef phi j z = R.ellipticCoefficient (idx phi j z)`, and joint
measurability `hR_meas` of the coefficient constructed from the ray data (the
paper obtains this from continuity of the collapsed stiffness field).

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

/-! ## 1. Ray data identify the weighted and second-moment classes rootwise -/

/-- **The class equality at a single ray-data index.**  The ray data produce a
coefficient uniformly sandwiched between the positive constants
`lam/(right-left)` and `Lambda/delta`, hence the weighted and second-moment
stationary classes coincide.  This is the repository theorem
`weightedClass_eq_secondMomentClass_of_rayData` read at one index. -/
theorem weightedClass_eq_secondMomentClass_of_rayData_at
    {ι : Type*} (R : UniformEllipticRayData ι) (idx : ι)
    (α β : Measure OTSelector.UnitMark)
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1)) :
    weightedClass α β (R.ellipticCoefficient idx) = secondMomentClass α β :=
  weightedClass_eq_secondMomentClass_of_rayData R α β hR_meas idx

/-- **The rootwise pressure identification from ray data.**  At a single
ray-data index the weighted stationary pressure equals the second-moment
stationary pressure at every probe and tilt: both are the stationary values of
the coinciding classes. -/
theorem weightedStationaryPressure_eq_secondMoment_of_rayData
    {ι : Type*} (R : UniformEllipticRayData ι) (idx : ι)
    (α β : Measure OTSelector.UnitMark)
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1))
    (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) (v : ℝ) :
    weightedStationaryPressure α β (R.ellipticCoefficient idx) f v =
      secondMomentStationaryPressure α β (R.ellipticCoefficient idx) f v := by
  simp only [weightedStationaryPressure, secondMomentStationaryPressure]
  rw [weightedClass_eq_secondMomentClass_of_rayData_at R idx α β hR_meas]

/-- **The pointwise rootwise focal-value equality from ray data.**  A coefficient
family identified pointwise with the ray-data coefficient satisfies the rootwise
gluing at every root and every tilt. -/
theorem perRootFocalValueEquality_of_uniformEllipticRayData
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1)) :
    PerRootFocalValueEquality (α := α) (β := β) coef probeFam := by
  intro φ j z v
  rw [hcoef φ j z]
  exact weightedStationaryPressure_eq_secondMoment_of_rayData R (idx φ j z) α β
    hR_meas (probeFam φ j z) v

/-! ## 2. hRoot is discharged by the ray data -/

/-- **`hRoot` from `UniformEllipticRayData`.**  In the uniformly elliptic
regime the a.e. rootwise focal-value equality `PerRootFocalValueEqualityAe`
(the paper's rootwise gluing residual of V8 and of
FinslerOriginalAtlasStationaryIdentificationFromPressureLimit) is proved from
the ray data: no rootwise analytic input remains. -/
theorem perRootFocalValueEqualityAe_of_uniformEllipticRayData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1)) :
    PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam :=
  perRootFocalValueEqualityAe_of_perRootFocalValueEquality
    (perRootFocalValueEquality_of_uniformEllipticRayData R idx coef probeFam hcoef hR_meas)

/-! ## 3. The integrated gluing identity from ray data -/

/-- **The integrated gluing identity P_2 = P_w from ray data.**  The measured
population second-moment pressure equals the Campbell-averaged weighted
stationary pressure, with the rootwise input supplied by the ray data rather
than assumed. -/
theorem populationSecondMomentPressure_eq_campbellAveraged_of_uniformEllipticRayData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1))
    (φ : FinalProbeSpace A B) (t : ℝ) :
    populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t =
      campbellAveragedStationaryPressure α β Seed a κ lambda
        (coef φ) (probeFam φ) q t :=
  populationSecondMomentPressure_eq_campbellAveraged_of_uniform_elliptic
    (R.lam / (R.right - R.left)) (R.Lambda / R.delta) R.c_pos
    (fun φ j z => by
      rw [hcoef φ j z]
      exact hR_meas (idx φ j z))
    (fun φ j z x y => by
      rw [hcoef φ j z]
      exact R.ellipticCoefficient_lower (idx φ j z) x y)
    (fun φ j z x y => by
      rw [hcoef φ j z]
      exact R.ellipticCoefficient_upper (idx φ j z) x y)
    φ t

/-! ## 4. P1 with hRoot discharged -/

/-- **P1 from `hFocal` and `hLimit`, with `hRoot` discharged by ray data.**
This is `populationFocalValueLimit_of_measurablePressureLimit`
(FinslerOriginalAtlasStationaryIdentificationFromPressureLimit) with its
rootwise hypothesis replaced by the geometric ellipticity datum. -/
theorem populationFocalValueLimit_of_measurablePressureLimit_of_uniformEllipticRayData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1))
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_measurablePressureLimit Seed a κ lambda pA Ag fg
    coef probeFam q α β hFocal hLimit
    (perRootFocalValueEqualityAe_of_uniformEllipticRayData Seed a κ lambda α β
      R idx coef probeFam hcoef hR_meas)

/-- **`hFocal` from P1 and `hLimit`, with the rootwise input supplied by ray
data.**  Thus, given the measured pressure limit, the global focal-value
identity I_w = pA is a consequence of P1 in the uniformly elliptic regime. -/
theorem focalValueEquality_of_populationFocalValueLimit_of_uniformEllipticRayData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1))
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    FocalValueEquality pA Ag fg α β :=
  focalValueEquality_of_populationFocalValueLimit_of_uniform_elliptic
    pA Ag fg coef probeFam q
    (R.lam / (R.right - R.left)) (R.Lambda / R.delta) R.c_pos
    (fun φ j z => by
      rw [hcoef φ j z]
      exact hR_meas (idx φ j z))
    (fun φ j z x y => by
      rw [hcoef φ j z]
      exact R.ellipticCoefficient_lower (idx φ j z) x y)
    (fun φ j z x y => by
      rw [hcoef φ j z]
      exact R.ellipticCoefficient_upper (idx φ j z) x y)
    hP1 hLimit

/-- **The two global paper inputs are interchangeable.**  Given the measured
pressure limit `hLimit` and the elliptic ray data, the population identity P1
and the focal-value equality I_w = pA are equivalent: the rootwise gluing is
discharged and the only remaining paper inputs are `hLimit` and one of
`hFocal`/`P1`. -/
theorem populationFocalValueLimit_iff_focalValueEquality_of_uniformEllipticRayData
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1))
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q ↔
      FocalValueEquality pA Ag fg α β :=
  ⟨fun hP1 =>
      focalValueEquality_of_populationFocalValueLimit_of_uniformEllipticRayData
        Seed a κ lambda α β pA Ag fg R idx coef probeFam q hcoef hR_meas hP1 hLimit,
    fun hFocal =>
      populationFocalValueLimit_of_measurablePressureLimit_of_uniformEllipticRayData
        Seed a κ lambda α β pA Ag fg R idx coef probeFam q hcoef hR_meas hFocal hLimit⟩

end OTSelector.Reconstruction
