import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanLaw
import OTSelector.MeasureTheory.ProbabilityMeasureWeakBorel
import Mathlib.MeasureTheory.Order.Group.Lattice
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeWeakContinuity

/-!
# Actual original allocation law readouts are unchanged finite-plan probes

The probability completion affects only the original null exceptional event.
The source-only continuous readout extension justifies the law integral, and
all original allocations and random target columns remain literal.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry OTSelector.Probability
open scoped Topology ContDiff CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Ω] {n : ℕ}
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- The joint original probability-plan law gives exactly the original finite
experiment's full signed physical-probe absolute gap expectation. -/
theorem lintegral_originalAllocationPlanPairLaw_seed_probe_eq
    (Renv : Measure Ω) [IsProbabilityMeasure Renv]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (ap w))
    (hfm : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (am w))
    (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    (∫⁻ s, ENNReal.ofReal
      |(∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g e.1 e.2 ∂(s.1 : Measure (M × M))) -
        ∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g e.1 e.2 ∂(s.2 : Measure (M × M))|
      ∂(physicalSceneOriginalAllocationPlanPairLaw Renv μ ν ap am hpm hmm Y hY :
        Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) =
    ∫⁻ w, ENNReal.ofReal
      |(∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g e.1 e.2 ∂physicalSceneGlobalAllocationFamily μ ap Y w) -
        ∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g e.1 e.2 ∂physicalSceneGlobalAllocationFamily μ am Y w| ∂Renv := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instPlanBorel : BorelSpace (ProbabilityMeasure (M × M)) :=
    probabilityMeasure_weakBorelSpace
  let S := ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)
  let pair : Ω → S := fun w ↦
    (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w,
      physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w)
  have hpair : Measurable pair :=
    (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap hpm Y hY).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am hmm Y hY)
  let f : M × M → ℝ := Function.uncurry (physicalSceneOriginalSeedCompactProbe
    (P := P) (a := a) (κ := κ) (lambda := lambda) j g)
  let obs : S → ℝ := fun s ↦
    |(∫ e, f e ∂(s.1 : Measure (M × M))) - ∫ e, f e ∂(s.2 : Measure (M × M))|
  obtain ⟨L, _, hLeq⟩ := exists_original_seed_compact_probe_boundedContinuous_probability_readout
    (P := P) (a := a) (κ := κ) (lambda := lambda) hF hcomplete hu ha hinj μ j g
  let H : S → ℝ := fun s ↦ |L s.1 - L s.2|
  have hH : Measurable (fun s ↦ ENNReal.ofReal (H s)) :=
    ENNReal.measurable_ofReal.comp
      (((L.continuous.measurable.comp measurable_fst).sub
        (L.continuous.measurable.comp measurable_snd)).abs)
  let C : Set S := {s | (s.1 : Measure (M × M)).fst = μ ∧ (s.2 : Measure (M × M)).fst = μ}
  have hC : MeasurableSet C :=
    ((isClosed_probability_fixed_source μ).measurableSet.preimage measurable_fst).inter
      ((isClosed_probability_fixed_source μ).measurableSet.preimage measurable_snd)
  have hsrcP := ae_fst_physicalSceneOriginalAllocationProbabilityPlanFamily Renv μ ν ap Y p hfp
  have hsrcM := ae_fst_physicalSceneOriginalAllocationProbabilityPlanFamily Renv μ ν am Y p hfm
  have hpairC : ∀ᵐ w ∂Renv, pair w ∈ C := by
    filter_upwards [hsrcP, hsrcM] with w hp hm using ⟨hp, hm⟩
  have hlawC : ∀ᵐ s ∂Renv.map pair, s ∈ C := (ae_map_iff hpair.aemeasurable hC).mpr hpairC
  have hObsEq (s : S) (hs : s ∈ C) : obs s = H s := by
    dsimp only [obs, H, f]
    rw [hLeq s.1 hs.1, hLeq s.2 hs.2]
    rfl
  have hpEq := physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq Renv μ ν ap Y p hfp
  have hmEq := physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq Renv μ ν am Y p hfm
  change (∫⁻ s, ENNReal.ofReal (obs s) ∂Renv.map pair) = _
  calc
    _ = ∫⁻ s, ENNReal.ofReal (H s) ∂Renv.map pair :=
      lintegral_congr_ae (hlawC.mono fun s hs ↦ congrArg ENNReal.ofReal (hObsEq s hs))
    _ = ∫⁻ w, ENNReal.ofReal (H (pair w)) ∂Renv := lintegral_map hH hpair
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hpairC, hpEq, hmEq] with w hw hp hm
      rw [← hObsEq (pair w) hw]
      change ENNReal.ofReal
        |(∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w :
            Measure (M × M))) -
          ∫ e, f e ∂(physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w :
            Measure (M × M))| = _
      rw [hp, hm]
      rfl

/-- The same unchanged original experiment gives exactly the original compact
seed readout against the actual global plans restricted to that source seed. -/
theorem lintegral_originalAllocationPlanPairLaw_seed_probe_eq_restrict_readout
    (Renv : Measure Ω) [IsProbabilityMeasure Renv]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (ap w))
    (hfm : ∀ᵐ w ∂Renv, IsSemidiscreteAllocation μ (p w) (am w))
    (j : ℕ)
    (g : C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ)) :
    (∫⁻ s, ENNReal.ofReal
      |(∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g e.1 e.2 ∂(s.1 : Measure (M × M))) -
        ∫ e, physicalSceneOriginalSeedCompactProbe (P := P) (a := a) (κ := κ)
          (lambda := lambda) j g e.1 e.2 ∂(s.2 : Measure (M × M))|
      ∂(physicalSceneOriginalAllocationPlanPairLaw Renv μ ν ap am hpm hmm Y hY :
        Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) =
    ∫⁻ w, ENNReal.ofReal
      |(∫ e, g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j e)
          ∂(physicalSceneGlobalAllocationFamily μ ap Y w).restrict
            (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
              (lambda := lambda) j ×ˢ univ)) -
        ∫ e, g (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j e)
          ∂(physicalSceneGlobalAllocationFamily μ am Y w).restrict
            (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
              (lambda := lambda) j ×ˢ univ)| ∂Renv := by
  rw [lintegral_originalAllocationPlanPairLaw_seed_probe_eq hF hcomplete hu ha hinj
    Renv μ ν ap am hpm hmm Y hY p hfp hfm j g]
  apply lintegral_congr_ae
  apply ae_of_all
  intro w
  dsimp only
  rw [integral_physicalSceneOriginalSeedCompactProbe_eq_restrict_readout
    hF hcomplete hu ha hinj j g (physicalSceneGlobalAllocationFamily μ ap Y w),
    integral_physicalSceneOriginalSeedCompactProbe_eq_restrict_readout
      hF hcomplete hu ha hinj j g (physicalSceneGlobalAllocationFamily μ am Y w)]

end OTSelector.Reconstruction
