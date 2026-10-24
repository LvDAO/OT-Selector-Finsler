import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationData

/-!
# The endgame upper field for the actual iid lane

This module packages the upper half of the endgame assembly: one structure
'EndgameUpperFields' bundling the upper pressure field 'pressureUpper', the
common tilt interval 'radius', and the original iid upper pressure localization
'hupper' in the exact consumer interface of 'FinalProbUpperData'
(FinslerSelectorFinalInputsWiringAudit.lean), together with projections and
nonemptiness theorems built from the weighted upper localization data of
FinslerOriginalWeightedUpperLocalizationData.lean.

## Named inputs

The structure itself does not assert realizability: 'endgameUpperFields_nonempty'
takes the named population-data input
'PhysicalWeightedLocalizationFamily' (the conclusion shape of the canonical-tile
localization theorem 'finsler_originalIID_pressure_upper_localization' after the
binder transfer documented in FinslerOriginalWeightedUpperLocalizationData.lean),
the local marked pressure limits 'pc', and the numerical identification of
'pressureUpper' with the block weighted sum.  The blockwise-limit variant takes
the per-block kernel marked scale pressure limits 'hlim' and the block-average
identification 'hpc' instead.  These are the exact remaining named inputs.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
  BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
  {hA : IsCompact A} {hB : IsCompact B}
  {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)} {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}

/-! ## 1. The endgame upper structure -/

/-- **The endgame upper fields.**  The upper pressure field, the common tilt
interval, and the original iid upper pressure localization, bundled in the
consumer interface of the endgame assembly (compare
'FinslerConditionalEndgameHypotheses.pressureUpper', '.radius', '.hupper'). -/
structure EndgameUpperFields
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ) where
  /-- The upper pressure localization limit. -/
  pressureUpper : FinalPressureField A B
  /-- The common tilt interval. -/
  radius : FinalRadiusField A B
  /-- The original iid upper pressure localization for the intrinsic length
  cost. -/
  hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius

/-- The upper pressure field of the endgame upper fields. -/
def endgameUpperFields_pressureUpper
    (S : EndgameUpperFields F μ ν hA hB hμA hνB P X Y u) : FinalPressureField A B :=
  S.pressureUpper

/-- The common tilt interval of the endgame upper fields. -/
def endgameUpperFields_radius
    (S : EndgameUpperFields F μ ν hA hB hμA hνB P X Y u) : FinalRadiusField A B :=
  S.radius

/-- The upper localization of the endgame upper fields. -/
theorem endgameUpperFields_hupper
    (S : EndgameUpperFields F μ ν hA hB hμA hνB P X Y u) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u
      (endgameUpperFields_pressureUpper S) (endgameUpperFields_radius S) :=
  S.hupper

/-! ## 2. Construction from the weighted upper localization data -/

/-- **The endgame upper fields from the block weighted localization family.**
The named input 'hLoc' is the conclusion shape of the canonical-tile
localization theorem after the binder transfer; 'hpc' identifies
'pressureUpper' with the block weighted sum of the local marked pressure limits
'pc'. -/
def endgameUpperFields_of_weightedLocalization
    (q m : ℕ) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (radius : FinalRadiusField A B)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (pressureUpper : FinalPressureField A B)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      pressureUpper f t =
        ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) :
    EndgameUpperFields F μ ν hA hB hμA hνB P X Y u :=
  { pressureUpper := pressureUpper
    radius := radius
    hupper := finalProbUpperData_actualLane q m radius hLoc pressureUpper hpc }

/-- **The endgame upper fields from the blockwise limit data.**
Same as 'endgameUpperFields_of_weightedLocalization', but the identification is
factored through the per-block kernel marked scale pressure limits 'hlim' and
the block-average identification 'hpc', exactly the inputs of
'finalProbUpperData_actualLane_blockwiseLimit'. -/
def endgameUpperFields_of_blockwiseLimit
    (q m : ℕ) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (radius : FinalRadiusField A B)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (pressureUpper : FinalPressureField A B)
    (hlim : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ∀ c : Fin q → Fin m,
        Tendsto (fun L : ℝ =>
          kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) (kin f t) (g f t) L t) atTop (𝓝 (pc f t c)))
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      (1 / (((m ^ q : ℕ) : ℝ))) * (∑ c : Fin q → Fin m, pc f t c) = pressureUpper f t) :
    EndgameUpperFields F μ ν hA hB hμA hνB P X Y u :=
  { pressureUpper := pressureUpper
    radius := radius
    hupper := finalProbUpperData_actualLane_blockwiseLimit q m radius hLoc
      Ks Kt kin g pressureUpper hlim hpc }

/-! ## 3. Nonemptiness of the endgame upper fields -/

/-- **Nonemptiness of the endgame upper fields** from the block weighted
localization family and the identification of the upper pressure field. -/
theorem endgameUpperFields_nonempty
    (q m : ℕ) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (radius : FinalRadiusField A B)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (pressureUpper : FinalPressureField A B)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      pressureUpper f t =
        ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) :
    Nonempty (EndgameUpperFields F μ ν hA hB hμA hνB P X Y u) :=
  ⟨endgameUpperFields_of_weightedLocalization q m radius hLoc pressureUpper hpc⟩

/-- **Nonemptiness of the endgame upper fields** from the blockwise limit data
(per-block kernel marked scale pressure limits and block-average
identification). -/
theorem endgameUpperFields_nonempty_of_blockwiseLimit
    (q m : ℕ) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (radius : FinalRadiusField A B)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (pressureUpper : FinalPressureField A B)
    (hlim : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ∀ c : Fin q → Fin m,
        Tendsto (fun L : ℝ =>
          kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) (kin f t) (g f t) L t) atTop (𝓝 (pc f t c)))
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      (1 / (((m ^ q : ℕ) : ℝ))) * (∑ c : Fin q → Fin m, pc f t c) = pressureUpper f t) :
    Nonempty (EndgameUpperFields F μ ν hA hB hμA hνB P X Y u) :=
  ⟨endgameUpperFields_of_blockwiseLimit q m radius hLoc Ks Kt kin g
    pressureUpper hlim hpc⟩

end OTSelector.Reconstruction
