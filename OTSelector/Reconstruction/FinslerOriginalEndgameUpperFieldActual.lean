import OTSelector.Reconstruction.FinslerOriginalEndgameUpperField
import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationRestated

/-!
# The actual-lane upper endgame bundle

Mirrors 'FinslerOriginalEndgameLowerFieldActual.lean' for the upper half.  For
the lane's own physical probabilities
'physicalSourceProbability omegaM rho0' / 'physicalTargetProbability omegaM rho1'
and the common tilt interval 'radius = fun _ => 1', this module instantiates the
upper endgame bundle end to end:

* 'endgameUpperPressure_actual': the lane's weighted-localization upper pressure,
  'fun f t => sum c, (1 / m^q) * pc f t c' (the block weighted sum of the local
  marked pressure limits);
* 'endgameUpperRadius_actual': the common tilt interval 'fun _ => 1';
* 'physicalWeightedLocalizationFamily_actualLane': the block weighted
  localization family for the actual physical probabilities, obtained from the
  literal restatement 'physicalWeightedLocalizationFamily_of_popData' (PopData +
  limit identification 'hpc');
* 'hupper_actualLane': the upper pressure localization for the actual lane, via
  'finalProbUpperData_actualLane';
* 'endgameUpperFields_actual_lane': the actual-lane 'EndgameUpperFields' bundle
  with 'pressureUpper = endgameUpperPressure_actual q m pc' and
  'radius = endgameUpperRadius_actual', built by 'endgameUpperFields_of_weightedLocalization'.

Every hypothesis stays an explicit binder; nothing is silently assumed.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
  BigOperators

noncomputable section

set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## 1. The lane's upper pressure and tilt interval -/

/-- The lane's weighted-localization upper pressure: the block weighted sum of
the local marked pressure limits. -/
def endgameUpperPressure_actual {A B : Set M} (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ) : FinalPressureField A B :=
  fun f t => ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c

/-- The lane's common tilt interval, 'radius = fun _ => 1'. -/
def endgameUpperRadius_actual {A B : Set M} : FinalRadiusField A B :=
  fun _ => 1

/-! ## 2. The weighted upper localization for the actual lane -/

/-- **The block weighted localization family for the actual physical
probabilities.**  Direct corollary of the literal restatement
'physicalWeightedLocalizationFamily_of_popData', with 'radius = fun _ => 1' and
the block weights '1 / m^q'.

Named inputs: the sampling hypotheses (transcribed as binders), the population
data 'PopData' for every probe and tilt, and the identification 'hpc' of the
local limits with 'pc'. -/
theorem physicalWeightedLocalizationFamily_actualLane
    (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (hu : let _instIIDPotentialMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (q m : ℕ) (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c) :
    PhysicalWeightedLocalizationFamily F
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ))) pc
      (endgameUpperRadius_actual (A := A) (B := B)) := by
  have h := physicalWeightedLocalizationFamily_of_popData
    (F := F) (φ := u) (hφ := hu) (hcomplete := hcomplete) (hdim := hdim)
    (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁) (hA := hA) (hB := hB) (hAB := hAB)
    (hμA := hμA) (hνB := hνB) (P := P) (X := X) (Y := Y)
    (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi) (hXlaw := hXlaw)
    (hYlaw := hYlaw) (hXY := hXY) (q := q) (m := m) (hm := hm)
    (radius := endgameUpperRadius_actual (A := A) (B := B)) (pc := pc)
    (Am := Am) (Cm := Cm) (data := data) (hpc := hpc)
  simpa [endgameUpperRadius_actual,
    show (fun c : Fin q → Fin m => ((blockW q m hm c : unitInterval) : ℝ)) =
        (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ))) from by
      funext c
      rfl] using h

/-- **The upper pressure localization for the actual lane.**  Via
'finalProbUpperData_actualLane' from the block weighted family and the
identification of 'pressureUpper' with the block weighted sum. -/
theorem hupper_actualLane
    (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (hu : let _instIIDPotentialMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (q m : ℕ) (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c)
    (pressureUpper : FinalPressureField A B)
    (hpcid : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      pressureUpper f t =
        ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) :
    FinalProbUpperData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u pressureUpper
      (endgameUpperRadius_actual (A := A) (B := B)) :=
  finalProbUpperData_actualLane q m (endgameUpperRadius_actual (A := A) (B := B))
    (physicalWeightedLocalizationFamily_actualLane (F := F) (u := u) (hu := hu)
      (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
      (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB) (P := P)
      (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
      (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY) (hm := hm) (pc := pc)
      (Am := Am) (Cm := Cm) (data := data) (hpc := hpc))
    pressureUpper hpcid

/-! ## 3. The actual-lane upper endgame bundle -/

/-- **The actual-lane upper endgame bundle.**  For the lane's own physical
probabilities, with 'pressureUpper = endgameUpperPressure_actual q m pc' and
'radius = endgameUpperRadius_actual', assembled by
'endgameUpperFields_of_weightedLocalization'.

Named inputs (all explicit binders): the sampling hypotheses, the population data
'PopData' for every probe and tilt inside the unit interval, and the
identification 'hpc' of the local limits with 'pc'. -/
def endgameUpperFields_actual_lane
    (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (hu : let _instIIDPotentialMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (q m : ℕ) (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c) :
    EndgameUpperFields F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u :=
  endgameUpperFields_of_weightedLocalization q m
    (endgameUpperRadius_actual (A := A) (B := B))
    (physicalWeightedLocalizationFamily_actualLane (F := F) (u := u) (hu := hu)
      (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
      (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB) (P := P)
      (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
      (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY) (hm := hm) (pc := pc)
      (Am := Am) (Cm := Cm) (data := data) (hpc := hpc))
    (endgameUpperPressure_actual q m pc)
    (fun _ _ _ => rfl)

end OTSelector.Reconstruction
