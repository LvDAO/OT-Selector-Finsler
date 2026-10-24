import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointExpectation
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointTargetBudget

/-! Exact same-law expectation of actual target cutoff defects. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputJointTargetExpectationInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointTargetExpectationPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual original missing targets and actual source escape pay the entire
joint cutoff defect in expectation. Only the fixed compact target support is
covered by the chosen open spatial window. -/
theorem lintegral_abs_legalMarkedInputTargetCutoffDefect_le
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {L : ℝ} (hL : 0 < L) (f χ : C_c(LegalMarkedPhysicalPoint q, ℝ))
    (hχ : ∀ x, χ x ∈ Icc 0 1) {T : Set (LegalMarkedPhysicalPoint q)}
    (hT : IsClosed T) (hχT : EqOn χ 1 T)
    {U : Set (Fin q → ℝ)} (hU : IsOpen U) (hcover : ∀ x ∈ tsupport f, x.1 ∈ U) :
    (∫⁻ s, ENNReal.ofReal |legalMarkedInputTargetCutoffDefect q f χ s|
      ∂(legalMarkedOptimalInputSceneLaw q α β kin hk g hg t L hL :
        Measure (LegalMarkedOptimalInputScene q))) ≤
      legalMarkedRootedTargetTestError q L α β kin g t f +
      ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
        ∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
          {e | e.2.1 ∈ U ∧ e.1 ∉ T}
          ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL :
            Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) := by
  let E : Set (LegalMarkedPhysicalEdge q) := {e | e.2.1 ∈ U ∧ e.1 ∉ T}
  have hE : IsOpen E := (hU.preimage (continuous_fst.comp continuous_snd)).inter
    (hT.isOpen_compl.preimage continuous_fst)
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) E) :=
    (LocalFiniteMeasure.measurable_measure_open hE).comp measurable_fst.fst
  have hsubset : Tᶜ ×ˢ tsupport f ⊆ E := by
    intro e he
    exact ⟨hcover e.2 he.2, he.1⟩
  have hobs := measurable_legalMarkedOptimalInputObservation q hL hk hg t
  have : IsProbabilityMeasure (legalMarkedHaarRootLaw q L) :=
    isProbabilityMeasure_legalMarkedHaarRootLaw q hL
  have herr : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedTargetTest q L kin g t (fun x ↦ f x) p.1 p.2 -
        legalMarkedRootedTargetInputTest q L (fun x ↦ f x) p.1 p.2) :=
    (measurable_legalMarkedRooted_targetTests q L hk hg t f.continuous.measurable).1.sub
      (measurable_legalMarkedRooted_targetTests q L hk hg t f.continuous.measurable).2
  have hproj : (∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) E
      ∂(legalMarkedOptimalInputSceneLaw q α β kin hk g hg t L hL :
        Measure (LegalMarkedOptimalInputScene q))) =
      ∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q)) E
        ∂(legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t L hL :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) := by
    rw [← map_legalMarkedOptimalInputSceneLaw_fst q hq α β kin hk g hg t hL]
    exact (lintegral_map (f := fun scene : CavityLocalScene
      (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
        (scene.1 : Measure (LegalMarkedPhysicalEdge q)) E)
      ((LocalFiniteMeasure.measurable_measure_open hE).comp measurable_fst) measurable_fst).symm
  rw [lintegral_legalMarkedOptimalInputSceneLaw q α β kin hk g hg t hL _
    ((continuous_legalMarkedInputTargetCutoffDefect q f χ).abs.measurable.ennreal_ofReal)]
  have hprod := lintegral_prod
    (μ := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)))
    (ν := legalMarkedHaarRootLaw q L)
    (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦ ENNReal.ofReal
      |legalMarkedInputTargetCutoffDefect q f χ (legalMarkedOptimalInputObservation q hL kin g t p)|)
    ((continuous_legalMarkedInputTargetCutoffDefect q f χ).abs.measurable.ennreal_ofReal.comp hobs).aemeasurable
  rw [← hprod]
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal |legalMarkedRootedTargetTest q L kin g t f p.1 p.2 -
        legalMarkedRootedTargetInputTest q L f p.1 p.2| +
        ENNReal.ofReal ‖f.toBoundedContinuousFunction‖ *
          ((legalMarkedOptimalInputObservation q hL kin g t p).1.1 : Measure (LegalMarkedPhysicalEdge q)) E
        ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod (legalMarkedHaarRootLaw q L) := by
      apply lintegral_mono
      intro p
      exact (ofReal_abs_legalMarkedInputTargetCutoffDefect_observation_le q hL kin g t f χ hχ hT.measurableSet hχT p).trans
        (add_le_add le_rfl (mul_le_mul_right (measure_mono hsubset) _))
    _ = _ := by
      rw [lintegral_add_left herr.abs.ennreal_ofReal]
      apply congrArg₂ (fun a b : ℝ≥0∞ ↦ a + b)
      · exact lintegral_prod _ herr.abs.ennreal_ofReal.aemeasurable
      · have heobs : Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
            ((legalMarkedOptimalInputObservation q hL kin g t p).1.1 :
              Measure (LegalMarkedPhysicalEdge q)) E) := by
          have h := hm.comp hobs
          simpa only [Function.comp_def] using h
        rw [lintegral_const_mul _ heobs]
        congr 1
        have hmap := lintegral_map (μ := (twoMarkedCloudLaw q ℝ ℝ α β
          (Real.toNNReal (L ^ q))).prod (legalMarkedHaarRootLaw q L)) hm hobs
        exact hmap.symm.trans hproj


end OTSelector.Reconstruction
