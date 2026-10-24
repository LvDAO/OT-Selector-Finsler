import OTSelector.Reconstruction.FinslerGeneralSelectorAssemblyFinal

/-!
# Wiring audit of the final selector inputs

This module audits the wiring between the four explicit open analytic inputs of
`FinslerSelectorFinalInputs` (pressureLower, pressureUpper, radius/hradius,
hvalue, hprob, hupper) and the exact consumer interface of the final paper
theorem `existsUnique_general_finsler_selector_final`, together with the
readout input `hreadout` (differentiability of the limiting pressure at zero).

Contents:

1. Named interface definitions for each input, copied from the consumer type
   (the consumer types are literally the structure-field types, so the
   identification lemmas below are definitional).
2. A named audit structure `FinslerSelectorFinalInputsAudit` that documents each
   remaining analytic input as an explicit hypothesis field, plus forgetful and
   inverse maps to and from `FinslerSelectorFinalInputs`.  No information is
   added or lost: the two structures carry the same data.
3. The five-input assembly interface of
   `existsUnique_general_finsler_selector_of_open_inputs` is proved to be
   exactly the four-input structure together with the readout derivative.
4. The readout input `hreadout` is proved discharged: the final theorem itself
   supplies, for every instance of the four inputs, one derivative function of
   the limiting lower pressure at zero.

Status of the inputs: pressureLower and pressureUpper are reduced to the named
fields `pressureLower`/`pressureUpper` (their concrete suppliers are the frozen
readout convention of the pressure-lower lane and the upper energy lane); radius
and hradius are named fields; hvalue, hprob and hupper are named hypotheses;
hreadout is discharged (item 4).  No hypothesis is silently weakened.
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
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-! ## 1. The exact consumer interfaces -/

/-- The probe space of the final assembly. -/
abbrev FinalProbeSpace (A B : Set M) := ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ)

/-- Consumer interface of the fields `pressureLower` and `pressureUpper`. -/
abbrev FinalPressureField (A B : Set M) := FinalProbeSpace A B → ℝ → ℝ

/-- Consumer interface of the field `radius`. -/
abbrev FinalRadiusField (A B : Set M) := FinalProbeSpace A B → ℝ

/-- Consumer interface of the field `hradius`. -/
def FinalPositiveRadius {A B : Set M} (radius : FinalRadiusField A B) : Prop :=
  ∀ f, 0 < radius f

/-- Consumer interface of the field `hvalue`. -/
def FinalValueIdentification {A B : Set M}
    (pressureLower pressureUpper : FinalPressureField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t = pressureUpper f t

/-- The readout input of the five-input assembly: one derivative function of the
limiting lower pressure at zero, for every probe. -/
def FinalReadoutData {A B : Set M} (pressureLower : FinalPressureField A B) : Prop :=
  ∃ derivative : FinalRadiusField A B,
    ∀ f : FinalProbeSpace A B,
      HasDerivAt (fun t : ℝ ↦ pressureLower f t) (derivative f) 0

/-- Consumer interface of the field `hprob`. -/
def FinalProbLowerData (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureLower : FinalPressureField A B) (radius : FinalRadiusField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t ε : ℝ),
    |t| < radius f → 0 < ε →
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν
      (A ∪ B) (hA.union hB).measurableSet
      (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
      (fun i ↦ X n i s) (fun i ↦ Y n i s) u
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
        pressureLower f t - ε}) atTop (𝓝 0)

/-- Consumer interface of the field `hupper`. -/
def FinalProbUpperData (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureUpper : FinalPressureField A B) (radius : FinalRadiusField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t ε : ℝ),
    |t| < radius f → 0 < ε →
    ∀ᶠ n in atTop,
      ∫ s, finslerSupportedPressure F μ ν
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) u
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤
          pressureUpper f t + ε

/-! ## 2. The named audit structure and its relation to the consumer structure -/

/-- The four explicit open analytic inputs, documented field by field as the
exact consumer interfaces of `FinslerSelectorFinalInputs`. -/
structure FinslerSelectorFinalInputsAudit
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M) {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ) where
  /-- The lower pressure localization limit (frozen readout convention). -/
  pressureLower : FinalPressureField A B
  /-- The upper pressure localization limit. -/
  pressureUpper : FinalPressureField A B
  /-- The common tilt interval. -/
  radius : FinalRadiusField A B
  /-- Positive tilt interval at every probe. -/
  hradius : FinalPositiveRadius radius
  /-- Legal-repair/value identification closing the pressure bracket. -/
  hvalue : FinalValueIdentification pressureLower pressureUpper
  /-- Original iid lower pressure localization for the intrinsic length cost. -/
  hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius
  /-- Original iid upper pressure localization for the intrinsic length cost. -/
  hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius

/-- Forget the named audit interfaces and get the consumer structure. -/
def FinslerSelectorFinalInputsAudit.toFinalInputs
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (x : FinslerSelectorFinalInputsAudit F μ ν hA hB hμA hνB P X Y u) :
    FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := x.pressureLower
    pressureUpper := x.pressureUpper
    radius := x.radius
    hradius := x.hradius
    hvalue := x.hvalue
    hprob := x.hprob
    hupper := x.hupper }

/-- Document every consumer field as the corresponding named interface. -/
def FinslerSelectorFinalInputs.ofFinalInputs
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (x : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinslerSelectorFinalInputsAudit F μ ν hA hB hμA hνB P X Y u :=
  { pressureLower := x.pressureLower
    pressureUpper := x.pressureUpper
    radius := x.radius
    hradius := x.hradius
    hvalue := x.hvalue
    hprob := x.hprob
    hupper := x.hupper }

/-- Field-by-field, the consumer structure is exactly the named audit structure. -/
theorem nonempty_finalInputs_iff_nonempty_audit
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ} :
    Nonempty (FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) ↔
      Nonempty (FinslerSelectorFinalInputsAudit F μ ν hA hB hμA hνB P X Y u) :=
  ⟨fun ⟨x⟩ => ⟨x.ofFinalInputs⟩, fun ⟨x⟩ => ⟨x.toFinalInputs⟩⟩

/-! ## 3. Restatements of each consumer field at the named interfaces -/

def finalInputs_pressureLower_interface
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalPressureField A B := inputs.pressureLower

def finalInputs_pressureUpper_interface
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalPressureField A B := inputs.pressureUpper

def finalInputs_radius_interface
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalRadiusField A B := inputs.radius

theorem finalInputs_hradius_interface
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalPositiveRadius inputs.radius := inputs.hradius

theorem finalInputs_hvalue_interface
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalValueIdentification inputs.pressureLower inputs.pressureUpper := inputs.hvalue

theorem finalInputs_hprob_interface
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalProbLowerData F μ ν hA hB hμA hνB P X Y u inputs.pressureLower inputs.radius :=
  inputs.hprob

theorem finalInputs_hupper_interface
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u inputs.pressureUpper inputs.radius :=
  inputs.hupper

/-! ## 4. The five-input assembly interface is the four-input structure plus readout -/

/-- The five explicit inputs of
`existsUnique_general_finsler_selector_of_open_inputs`, as named interfaces,
are exactly the four-input consumer structure together with the readout data. -/
theorem fiveInputInterface_iff_finalInputs_and_readout
    {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ) :
    (∃ (pressureLower pressureUpper : FinalPressureField A B)
        (radius : FinalRadiusField A B),
      FinalPositiveRadius radius ∧
        FinalValueIdentification pressureLower pressureUpper ∧
        FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius ∧
        FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius ∧
        FinalReadoutData pressureLower) ↔
      (∃ inputs : FinslerSelectorFinalInputs F μ ν hA hB hμA hνB P X Y u,
        FinalReadoutData inputs.pressureLower) := by
  constructor
  · rintro ⟨pressureLower, pressureUpper, radius, hradius, hvalue, hprob, hupper, hreadout⟩
    exact ⟨{ pressureLower := pressureLower
             pressureUpper := pressureUpper
             radius := radius
             hradius := hradius
             hvalue := hvalue
             hprob := hprob
             hupper := hupper }, hreadout⟩
  · rintro ⟨inputs, hreadout⟩
    exact ⟨inputs.pressureLower, inputs.pressureUpper, inputs.radius, inputs.hradius,
      inputs.hvalue, inputs.hprob, inputs.hupper, hreadout⟩

/-! ## 5. The readout input hreadout is discharged -/

/-- **The readout input of the five-input assembly is discharged by the final
theorem.**  Under exactly the hypotheses of
`existsUnique_general_finsler_selector_final`, for every instance of the four
explicit inputs there is one derivative function of the limiting lower pressure
at zero, for every probe. -/
theorem final_selector_readout_discharged
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (physicalSourceProbability ωM ρ₀ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (physicalTargetProbability ωM ρ₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n)) :
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃ u : M → ℝ, (let _instFinalPotentialMetric : MetricSpace M := F.metricSpace
        LipschitzWith 1 u) ∧
      ∀ (inputs : FinslerSelectorFinalInputs F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          hA hB hμA hνB P X Y u),
        FinalReadoutData inputs.pressureLower := by
  obtain ⟨u, hu, hmain⟩ := existsUnique_general_finsler_selector_final
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
    hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY
  refine ⟨u, hu, ?_⟩
  intro inputs
  obtain ⟨derivative, hderivative⟩ := hmain inputs
  exact ⟨derivative, hderivative.1⟩

end OTSelector.Reconstruction
