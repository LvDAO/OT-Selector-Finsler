import OTSelector.Reconstruction.FinslerOriginalP1SingleInputReduction
import OTSelector.Reconstruction.FinslerOriginalPressureSandwichFromBounds

/-!
# The pA-free measured P1 input from the finite-scale pressure bounds

This module bridges the pA-free single P1 input

  `AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q`
  (`∀ φ t, weightedStationaryPressure α β (Ag φ) (fg φ) t =
    populationSecondMomentPressure ... φ t`, i.e. `I_w = P_2`)

of FinslerOriginalP1SingleInputReduction to the finite-scale pressure bounds of
FinslerOriginalPressureSandwichFromBounds.  The sandwich chain of that module
derives `MeasurablePressureLimit ... pA ...` for the lane readout `pA =
pressureLower`; composing it with the focal limit `I_w = pA` gives the merged
identity `I_w = P_2`, and the dummy function `pA` disappears from the chain.

Main declarations:

* `atlasMeasuredFocalPressure_of_measurablePressureLimit` — the merged identity
  from a focal-value equality and a measured pressure limit (the pA-elimination
  step);
* `atlasMeasuredFocalPressure_of_pressureSandwich` — the merged identity from
  the focal-value equality, the lane identification and the two-sided
  finite-scale pressure sandwich against the measured atlas pressure;
* `atlasMeasuredFocalPressure_of_finalPressureBounds` — the same from the
  repository F12 lower probability bound, F18 cellwise upper bound, the endgame
  value identification, the deterministic lower bound, measurability and
  integrability, the covering radius and the readout identification (no finite
  pressure limit assumed: it is produced from the two bounds);
* `populationFocalValueLimit_of_finalPressureBounds_and_ellipticRayData` — P1
  from the same bounds and the uniformly elliptic ray data, with neither `pA`
  nor the rootwise gluing `hRoot` as an input.

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

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## 1. The pA-elimination step -/

/-- **The merged pA-free input from the focal limit and the measured pressure
limit.**  The focal-value equality `I_w = pA` and the measured pressure limit
`pA = P_2` compose to `I_w = P_2`, which mentions no `pA`. -/
theorem atlasMeasuredFocalPressure_of_measurablePressureLimit
    {A B : Set M} (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q :=
  (exists_pA_focal_and_limit_iff_atlasMeasuredPressureLimit Seed a κ lambda α β
    Ag fg coef probeFam q).mp ⟨pA, hFocal, hLimit⟩

/-! ## 2. From the two-sided sandwich -/

/-- **The merged pA-free input from the finite-scale pressure sandwich.**  The
lane identification `FinitePressureLimitAt pressure pA` and the sandwich of the
finite-scale pressures against the measured atlas pressure give
`MeasurablePressureLimit ... pA ...`, which composes with the focal-value
equality `I_w = pA` into the pA-free identity `I_w = P_2`. -/
theorem atlasMeasuredFocalPressure_of_pressureSandwich
    {A B : Set M} (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hPA : FinitePressureLimitAt pressure pA)
    (hsand : PressureLimitSandwich
      (fun φ t =>
        populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)
      pressure) :
    AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q :=
  atlasMeasuredFocalPressure_of_measurablePressureLimit F u Seed a κ lambda
    α β Ag fg coef probeFam q pA hFocal
    (measurablePressureLimit_of_pressureSandwich F u Seed a κ lambda pA pressure
      α β coef probeFam q hPA hsand)

/-! ## 3. From the repository probability bounds -/

/-- **The merged pA-free input from the repository pressure bounds.**  The F12
lower probability bound and the F18 cellwise upper bound localize the expected
finite-scale pressures around the common endgame readout
(`pressureLower = pressureUpper`); the deterministic lower bound, measurability
and integrability of the supported pressure, the covering radius and the readout
identification then give the sandwich against the measured atlas pressure.  The
finite pressure limit is produced from the two bounds, not assumed.  Composing
with the focal-value equality `I_w = pressureLower` gives the pA-free identity
`I_w = P_2`. -/
theorem atlasMeasuredFocalPressure_of_finalPressureBounds
    (F : ContinuousFinslerNorm E M) (A B : Set M)
    (hA : IsCompact A) (hB : IsCompact B)
    (μ ν : ProbabilityMeasure M)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius)
    (Mbd : FinalProbeSpace A B → ℝ → ℝ) (hMbd : ∀ f t, 0 ≤ Mbd f t)
    (hvalue : ∀ f t, pressureLower f t = pressureUpper f t)
    (hbound : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      pressureLower f t - Mbd f t ≤
        supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n s)
    (hV : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Measurable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n))
    (hint : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Integrable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n) (P n))
    (hAll : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hreadout : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t =
      populationSecondMomentPressure Seed a κ lambda α β coef probeFam q f t)
    (hFocal : FocalValueEquality pressureLower Ag fg α β) :
    AtlasMeasuredFocalPressure Seed a κ lambda α β Ag fg coef probeFam q := by
  have hon := pressureLimitSandwichOnRadius_of_finalData F μ ν hA hB hμA hνB P
    X Y u pressureLower pressureUpper radius hprob hupper Mbd hMbd hvalue
    hbound hV hint
  have hfull : PressureLimitSandwich (fun f t => pressureLower f t)
      (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
        ⌊R⌋₊ f t) := pressureLimitSandwich_of_onRadius hAll hon
  have hfun : (fun (f : FinalProbeSpace A B) (t : ℝ) => pressureLower f t) =
      fun f t => populationSecondMomentPressure Seed a κ lambda α β coef
        probeFam q f t := by
    funext f t
    exact hreadout f t
  have hsand : PressureLimitSandwich
      (fun φ t =>
        populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)
      (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
        ⌊R⌋₊ f t) := by
    rw [← hfun]
    exact hfull
  have hPA : FinitePressureLimitAt
      (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
        ⌊R⌋₊ f t) (fun f t => pressureLower f t) :=
    finitePressureLimitAt_of_nat_tendsto (pA := fun f t => pressureLower f t)
      (pressure := fun f n t => expectedSupportedPressure F μ ν hA hB hμA hνB
        P X Y u n f t)
      (fun f t => tendsto_expectedSupportedPressure_of_finalData F μ ν hA hB
        hμA hνB P X Y u pressureLower pressureUpper radius hprob hupper Mbd
        hMbd hvalue hbound hV hint f t (hAll f t))
  exact atlasMeasuredFocalPressure_of_pressureSandwich F u Seed a κ lambda
    α β Ag fg coef probeFam q (fun f t => pressureLower f t)
    (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
      ⌊R⌋₊ f t) hFocal hPA hsand

/-! ## 4. P1 from the bounds and the elliptic ray data -/

/-- **P1 from the repository pressure bounds and the uniformly elliptic ray
data.**  This composes the pA-free measured input derived from the bounds with
`populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_ellipticRayData`:
P1 follows from the bounds, the readout identification, the focal-value equality
and the ray data, with neither the dummy function `pA` nor the rootwise gluing
`hRoot` as an input. -/
theorem populationFocalValueLimit_of_finalPressureBounds_and_ellipticRayData
    (F : ContinuousFinslerNorm E M) (A B : Set M)
    (hA : IsCompact A) (hB : IsCompact B)
    (μ ν : ProbabilityMeasure M)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius)
    (Mbd : FinalProbeSpace A B → ℝ → ℝ) (hMbd : ∀ f t, 0 ≤ Mbd f t)
    (hvalue : ∀ f t, pressureLower f t = pressureUpper f t)
    (hbound : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      pressureLower f t - Mbd f t ≤
        supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n s)
    (hV : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Measurable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n))
    (hint : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Integrable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n) (P n))
    (hAll : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hreadout : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t =
      populationSecondMomentPressure Seed a κ lambda α β coef probeFam q f t)
    (hFocal : FocalValueEquality pressureLower Ag fg α β)
    {ι : Type*} (R : UniformEllipticRayData ι)
    (idx : FinalProbeSpace A B → ℕ → Z → ι)
    (hcoef : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      coef φ j z = R.ellipticCoefficient (idx φ j z))
    (hR_meas : ∀ (phi : ι), Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1)) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_atlasMeasuredPressureLimit_and_ellipticRayData
    Seed a κ lambda α β Ag fg coef probeFam q R idx hcoef hR_meas
    (atlasMeasuredFocalPressure_of_finalPressureBounds F A B hA hB μ ν hμA hνB
      P X Y u pressureLower pressureUpper radius hprob hupper Mbd hMbd hvalue
      hbound hV hint hAll Seed a κ lambda α β Ag fg coef probeFam q hreadout
      hFocal)

end OTSelector.Reconstruction
