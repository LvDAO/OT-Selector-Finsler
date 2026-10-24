import OTSelector.Reconstruction.FinslerOriginalEndgameFieldsAssembly
import OTSelector.Reconstruction.FinslerOriginalPaperGeometricBundleActual
import OTSelector.Reconstruction.FinslerOriginalEndgameUpperFieldActual
import OTSelector.Reconstruction.FinslerOriginalReadoutGlue
import OTSelector.Reconstruction.FinslerOriginalScenePressureWiring
import OTSelector.Reconstruction.FinslerOriginalGeneralSelectorParameterized

/-!
# The paper endgame data at a calibrated potential: actual-lane assembly

This module assembles the paper endgame data `FinslerPaperEndgameData` at a
given calibrated potential `u` from the actual-lane producers of the
reconstruction lane, and composes the result with
`existsUnique_general_finsler_selector_at_potential_paperData`.

## What this module proves

* `paperEndgameData_of_upperBundle` -- the conditional assembler: from the
  population seed datum, the unshifted frozen lower readout with its F12
  probability localization, an actual-lane upper bundle with its F18 readout
  bridge, and the F15 frozen readout plus screening value data, it produces
  `FinslerPaperEndgameData` at the calibrated potential `u`.
* `paperEndgameData_actual` -- the same, with the upper bundle PRODUCED by the
  actual-lane producer `endgameUpperFields_actual_lane`; the upper lane's
  `PopData` telescope is an explicit binder (flag F13).
* `existsUnique_general_finsler_selector_at_potential_paperData_actual` -- the
  paper-facing selector theorem
  `existsUnique_general_finsler_selector_at_potential_paperData` at the
  calibrated potential `u`, with the endgame datum supplied by
  `paperEndgameData_actual`.  The only remaining analytic input is the
  differentiability of the unshifted frozen lower readout at zero
  (`FinslerReadoutTiltDerivative`).

Thus the endgame datum is PRODUCED at the given potential from the paper's
population data; there is no `forall u, 1-Lipschitz u -> ...` hypothesis of the
withdrawn wrapper (flag F10), and no vacuous residual assumption.

## Wiring at a glance

* `geometric` -- produced: `paperGeometricHypotheses_of_seedDatum` from
  `PaperGeometricSeedDatum`.
* `pressureLower` -- produced: the unshifted frozen readout
  `frozenPressureLower` (FinslerOriginalScenePressureWiring).
* `pressureUpper`, `hupper` -- produced: the actual-lane upper bundle
  `endgameUpperFields_actual_lane` (FinslerOriginalEndgameUpperFieldActual).
* `radius`, `hradius` -- produced: `radius = fun _ => 1`; the actual-lane bundle
  radius `endgameUpperRadius_actual` is definitionally `fun _ => 1`, and
  positivity is proved.
* `hvalue` -- derived: `finalValueIdentification_of_readoutBridges`
  (FinslerOriginalReadoutGlue) from the F15 frozen Campbell readout `hC`, the
  F18 upper stationary readout `hU`, and the screening data `hscreen`.
* `hprob` -- EXPLICIT BINDER, flag F12 (see below).
* `FinslerReadoutTiltDerivative` -- EXPLICIT BINDER of the composition theorem,
  the single remaining analytic input (paper-proven, Lean-open).

## Flags as explicit binders (not hidden)

* F12 (`hprob`): the actual-lane lower bundles
  (`FinslerOriginalEndgameLowerFieldActual`, `...LowerLaneInputsActual`,
  `FinslerOriginalFrozenInputsActual`) produce `FinalProbLowerData` only at the
  probe-SHIFTED readout `fun f t => Psi f t - |t| * ||f||`.  The paper endgame
  field and the differentiability input `FinslerReadoutTiltDerivative` need the
  UNSHIFTED frozen readout `frozenPressureLower` (the shifted field has no
  two-sided derivative at `t = 0` for nonzero probes).  Hence `hprob` is an
  explicit binder at the unshifted field: this is exactly audit flag F12.
* F13: the upper lane's `PopData` telescope is an explicit binder of
  `paperEndgameData_actual`; the internal `hCbnd` strength issue of `PopData`
  (`research/AUDIT-LANES-II.md`, flag F13) is inherited by
  `endgameUpperFields_actual_lane` and is NOT hidden here.
* F15 (`hC`): `FrozenCampbellReadout` is the paper-proven, Lean-open frozen
  Campbell readout identity; it stays an explicit binder.
* F18 (`hU`): `UpperStationaryReadout U.pressureUpper datum` is the unshifted
  upper readout identification of the actual upper pool with the datum's `I2`
  (`UpperStationaryReadout` of FinslerOriginalReadoutGlue); pairing it with the
  UNSHIFTED frozen lower readout is the coerced F18 convention.  (The shifted
  bridge `ProbeShiftedUpperReadout` belongs to the other, probe-shifted,
  pairing.)

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

variable {u : M → ℝ} {μ ν : ProbabilityMeasure M}
  {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
  {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}
  {X Y : ∀ n, Fin (n + 1) → Ω n → M}

/-- **The paper endgame data at a calibrated potential from the actual-lane
pieces.**  The geometric field and the value field are produced; the lower
probability localization is the F12 binder at the unshifted frozen readout, and
the upper bundle is the actual-lane `EndgameUpperFields` with its F18 upper
readout bridge. -/
noncomputable def paperEndgameData_of_upperBundle
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (seedDatum : PaperGeometricSeedDatum F u μ ν)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {g : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) (fun _ => 1))
    (U : EndgameUpperFields F μ ν hA hB hμA hνB P X Y u)
    (hUr : U.radius = fun _ => 1)
    {W : Type*} {G Cb : ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum)
    (hU : UpperStationaryReadout U.pressureUpper datum)
    (hscreen : StationaryScreening datum) :
    FinslerPaperEndgameData F μ ν hA hB hμA hνB P X Y u :=
  { geometric := paperGeometricHypotheses_of_seedDatum F u μ ν hF hu seedDatum
    pressureLower := frozenPressureLower (K := A ∪ B) Seed a κ lambda g q
    pressureUpper := U.pressureUpper
    radius := fun _ => 1
    hradius := fun _ => zero_lt_one
    hprob := hprob
    hupper := by simpa only [hUr] using U.hupper
    hvalue := finalValueIdentification_of_readoutBridges _ U.pressureUpper datum
      ((lowerStationaryReadout_frozenLowerField_iff (Seed := Seed) (a := a)
        (κ := κ) (lambda := lambda) g q datum).mpr hC) hU hscreen }


/-! ## 2. The fully wired actual-lane upper bundle -/

/-- **The paper endgame data from the actual upper-lane producer.**  The upper
bundle of `paperEndgameData_of_upperBundle` is now produced by
`endgameUpperFields_actual_lane`: its pressure is the block weighted pool of the
local marked pressure limits and its radius is `endgameUpperRadius_actual = fun _
o. 1`.  All upper-lane hypotheses (`PopData` for every probe and tilt, the block
identification `hpc`, the sampling hypotheses) are explicit binders, so audit
flag F13 stays visible. -/
noncomputable def paperEndgameData_actual
    (hF : F.IsSmoothStronglyConvex)
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
    (u : M → ℝ)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (seedDatum : PaperGeometricSeedDatum F u
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {g : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (hprob : FinalProbLowerData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) (fun _ => 1))
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (data f t hpert).p c t = pc f t c)
    {W : Type*} {G Cb : ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum)
    (hU : UpperStationaryReadout
      (endgameUpperPressure_actual (A := A) (B := B) qU mU pc) datum)
    (hscreen : StationaryScreening datum) :
    FinslerPaperEndgameData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u :=
  paperEndgameData_of_upperBundle (F := F) hF hu seedDatum hprob
    (U := endgameUpperFields_actual_lane F u hu hcomplete hdim ωM ρ₀ ρ₁
      hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY qU mU hmU pc
      data hpc)
    (hUr := rfl) hC hU hscreen

/-! ## 3. The paper-facing selector theorem at the calibrated potential -/

/-- **The paper-facing selector theorem at a given calibrated potential, with
the paper endgame data produced by the actual-lane assembly.**  This is
`existsUnique_general_finsler_selector_at_potential_paperData` applied to
`paperEndgameData_actual`: the endgame datum is no longer assumed for
all 1-Lipschitz potentials (the withdrawn wrapper F10), it is produced at the
chosen `u` from the geometric seed datum and the actual-lane data.  The only
remaining analytic input is the readout tilt derivative at zero.

The explicit binders keep the audit flags visible: `hprob` is F12 (unshifted
lower probability at the actual lane), `data` is F13 (`PopData` telescope with
its `hCbnd` strength issue), `hC` is F15 (`FrozenCampbellReadout`), `hU` is F18
(upper stationary readout of the actual upper pool), and `hderiv` is the
single remaining derivative input. -/
theorem existsUnique_general_finsler_selector_at_potential_paperData_actual
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
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
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (u : M → ℝ)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (seedDatum : PaperGeometricSeedDatum F u
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    (Z : Type*) [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (hprob : FinalProbLowerData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u
      (frozenPressureLower (K := A ∪ B) Seed a κ lambda g q) (fun _ => 1))
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    (Am Cm : Type*) [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (data f t hpert).p c t = pc f t c)
    {W : Type*} {G Cb : ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hC : FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) g q datum)
    (hU : UpperStationaryReadout
      (endgameUpperPressure_actual (A := A) (B := B) qU mU pc) datum)
    (hscreen : StationaryScreening datum)
    (hderiv : FinslerReadoutTiltDerivative
      (paperEndgameData_actual hF hcomplete hdim ωM ρ₀ ρ₁
        hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
        seedDatum hprob qU mU hmU pc data hpc hC hU hscreen).pressureLower) :
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let D := paperEndgameData_actual hF hcomplete hdim ωM ρ₀ ρ₁
      hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
      seedDatum hprob qU mU hmU pc data hpc hC hU hscreen
    Nonempty (FinslerSelectorFinalInputs F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          hA hB hμA hνB P X Y u) ∧
        Tendsto (fun n ↦ D.geometric.palm_sample_law.normalization n *
          D.geometric.palm_sample_law.maskedMean n -
          D.geometric.palm_sample_law.populationValue n) atTop (𝓝 0) ∧
        ∃ derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ,
          (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
            HasDerivAt (fun t ↦ D.pressureLower f t) (derivative f) 0) ∧
          ∃! π : ProbabilityMeasure (M × M),
            (∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
              ∫ z, f z ∂((π : Measure (M × M)).comap
                (Prod.map ((↑) : ↥(A ∪ B) → M) ((↑) : ↥(A ∪ B) → M))) = derivative f) ∧
            (∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
              {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0)) ∧
            (∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
              d π π = 0 →
              (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (M × M) | d γ π < ε}) →
              ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
                {s | ∃ γ ∈ Pressure.empiricalOptimalFace
                  (fun i ↦ X n i s) (fun i ↦ Y n i s), ε ≤ d γ π}) atTop (𝓝 0)) ∧
            IsOptimalCoupling edist
              (physicalSourceProbability ωM ρ₀ : Measure M)
              (physicalTargetProbability ωM ρ₁ : Measure M) (π : Measure (M × M)) := by
  let D := paperEndgameData_actual hF hcomplete hdim ωM ρ₀ ρ₁
    hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu
    seedDatum hprob qU mU hmU pc data hpc hC hU hscreen
  exact existsUnique_general_finsler_selector_at_potential_paperData
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg
    hvolume hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu D hderiv

end OTSelector.Reconstruction