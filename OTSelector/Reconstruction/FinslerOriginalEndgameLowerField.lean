import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit
import OTSelector.Reconstruction.FinslerOriginalHprobWiring

/-!
# Endgame lower fields: assembly of the lower half of the endgame

Bundles the lower half of the endgame paper data for the actual lane into one
structure `EndgameLowerFields`, matching the lower fields of
`FinslerConditionalEndgameHypotheses` (structure fields `pressureLower`, `radius`,
`hradius`, `hprob`):

* `pressureLower : FinalPressureField A B` — the reader interface of
  `FinslerSelectorFinalInputsWiringAudit.lean`;
* `radius : FinalRadiusField A B`;
* `hradius : FinalPositiveRadius radius`;
* `hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius`.

## What is produced

* the structure `EndgameLowerFields` and its four extractors
  (`endgameLowerPressure`, `endgameLowerRadius`, `endgameLowerHradius`,
  `endgameLowerHprob`);
* the constructor `endgameLowerFields_mk` and the nonemptiness theorem
  `endgameLowerFields_nonempty` from the four named data;
* `probeShiftedReadout`: the exact pressureLower expression produced by the
  hprob wiring lane, `fun f t ↦ Ψ f t - |t| * ‖f‖`;
* the wiring slots `endgameLowerFields_of_palmReadout` and
  `endgameLowerFields_of_palmSampleMeanLimit`: given the conclusion of
  `finalProbLowerData_of_palmSampleReadout` (resp. of its mean-limit variant)
  at the probe-shifted readout, the bundled structure is obtained immediately.

The remaining named inputs (the TilePalmSampleLaw data, the probe/amplitude
bounds, the clipping vanishing and the radius function itself) stay explicit
hypotheses: nothing not already named in the repo is assumed.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-! ## 1. The bundled lower endgame fields -/

/-- **The lower half of the endgame fields**, matching the lower fields of
`FinslerConditionalEndgameHypotheses` for the actual lane: the lower pressure
localization limit, the common tilt interval radius, its positivity, and the
original iid lower pressure localization. -/
structure EndgameLowerFields (F : ContinuousFinslerNorm E M)
    (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ) where
  /-- The lower pressure localization limit (frozen readout convention). -/
  pressureLower : FinalPressureField A B
  /-- The common tilt interval. -/
  radius : FinalRadiusField A B
  /-- The tilt interval is positive at every probe. -/
  hradius : FinalPositiveRadius radius
  /-- The original iid lower pressure localization for the intrinsic length
  cost, at the lower pressure field. -/
  hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius

/-! ## 2. Extractors -/

variable {μ ν : ProbabilityMeasure M} {A B : Set M} {hA : IsCompact A}
  {hB : IsCompact B} {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}
  {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}

/-- Extractor of the lower pressure field. -/
def endgameLowerPressure (L : EndgameLowerFields F μ ν hA hB hμA hνB P X Y u) :
    FinalPressureField A B :=
  L.pressureLower

/-- Extractor of the tilt interval radius. -/
def endgameLowerRadius (L : EndgameLowerFields F μ ν hA hB hμA hνB P X Y u) :
    FinalRadiusField A B :=
  L.radius

/-- Extractor of the positivity of the tilt interval. -/
theorem endgameLowerHradius (L : EndgameLowerFields F μ ν hA hB hμA hνB P X Y u) :
    FinalPositiveRadius L.radius :=
  L.hradius

/-- Extractor of the lower probability localization. -/
theorem endgameLowerHprob (L : EndgameLowerFields F μ ν hA hB hμA hνB P X Y u) :
    FinalProbLowerData F μ ν hA hB hμA hνB P X Y u L.pressureLower L.radius :=
  L.hprob

/-! ## 3. Constructors -/

/-- Constructor of the bundled lower endgame fields from the four named data. -/
def endgameLowerFields_mk (pressureLower : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius) :
    EndgameLowerFields F μ ν hA hB hμA hνB P X Y u :=
  ⟨pressureLower, radius, hradius, hprob⟩

/-- **Nonemptiness of the bundled lower endgame fields** from the four named
data: the bundle itself adds no information. -/
theorem endgameLowerFields_nonempty (pressureLower : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius) :
    Nonempty (EndgameLowerFields F μ ν hA hB hμA hνB P X Y u) :=
  ⟨endgameLowerFields_mk pressureLower radius hradius hprob⟩

/-- The extractors are inverse to the constructor. -/
theorem endgameLowerFields_mk_extractors (pressureLower : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius) :
    endgameLowerPressure (endgameLowerFields_mk pressureLower radius hradius hprob) =
        pressureLower ∧
      endgameLowerRadius (endgameLowerFields_mk pressureLower radius hradius hprob) =
        radius ∧
      endgameLowerHradius (endgameLowerFields_mk pressureLower radius hradius hprob) =
        hradius ∧
      endgameLowerHprob (endgameLowerFields_mk pressureLower radius hradius hprob) =
        hprob :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 4. The exact pressureLower readout of the hprob wiring lane -/

/-- The probe-shifted readout of the hprob wiring lane:
`fun f t ↦ Ψ f t - |t| * ‖f‖`.  This is the pressureLower expression produced by
`finalProbLowerData_of_palmSampleReadout`. -/
def probeShiftedReadout {A B : Set M} (Ψ : FinalPressureField A B) :
    FinalPressureField A B :=
  fun f t ↦ Ψ f t - |t| * ‖f‖

/-! ## 4. The exact pressureLower readout of the hprob wiring lane -/

/-- **Wiring slot at the probe-shifted readout**: the conclusion of
¤/finalProbLowerData_of_palmSampleReadout¤/ is exactly the ¤/hprob¤/ field of the
bundled lower endgame fields at ¤/pressureLower = probeShiftedReadout Ψ¤/, so once
the named lane data supply that conclusion the bundle is obtained immediately. -/
theorem endgameLowerFields_of_palmReadout (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    (hA : IsCompact A) (hB : IsCompact B)
    (hμAphys : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνBphys : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (Ψ : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hprob : FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμAphys hνBphys sample X Y u
      (probeShiftedReadout Ψ) radius) :
    Nonempty (EndgameLowerFields F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμAphys hνBphys sample X Y u) :=
  endgameLowerFields_nonempty (probeShiftedReadout Ψ) radius hradius hprob

/-- **Wiring slot of the mean-limit variant**: the conclusion of
¤/finalProbLowerData_of_palmSampleMeanLimit¤/ lands in the same slot, at the
pressureLower field carved out by the probe shift. -/
theorem endgameLowerFields_of_palmSampleMeanLimit (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    (hA : IsCompact A) (hB : IsCompact B)
    (hμAphys : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνBphys : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (pressureLower : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hprob : FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμAphys hνBphys sample X Y u
      (probeShiftedReadout pressureLower) radius) :
    Nonempty (EndgameLowerFields F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμAphys hνBphys sample X Y u) :=
  endgameLowerFields_of_palmReadout ωM dens₀ dens₁ hA hB hμAphys hνBphys sample
    pressureLower radius hradius hprob

end OTSelector.Reconstruction
