import OTSelector.MeasureTheory.LocalFiniteMeasureReadoutLoss
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedLossLimit

/-!
# Full original agreement controls retained compact readouts by actual lost mass

The unchanged full pair agrees on the exact projected law. Its actual closed
retained/lost decomposition leaves only the two discarded compact-test errors.
Their sum is twice the arithmetic-mean lost source mass, without any finiteness
assumption on that source-window mass. Bounded macro weights are retained.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local instance maskedReadoutAgreementStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance maskedReadoutAgreementConfigTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance maskedReadoutAgreementConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance maskedReadoutAgreementConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance maskedReadoutAgreementPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Exact actual full agreement and the closed decomposition pay the retained
compact readout difference by twice the average discarded source mass. -/
theorem ofReal_retained_compact_difference_le_lost_of_full_agreement
    (s : JointScene) (hdecomp : s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hfull : (s.1.2.1.1 : Measure Edge) = (s.1.2.1.2 : Measure Edge))
    (χ : C_c(Edge, ℝ)) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) :
    ENNReal.ofReal |LocalFiniteMeasure.testIntegral s.2.1.1 χ -
      LocalFiniteMeasure.testIntegral s.2.1.2 χ| ≤
      ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
        physicalSceneMaskedLostSourceMass base U s := by
  have hd : s.1.2.1 = physicalScenePairSum s.2 := hdecomp
  have hp : (s.1.2.1.1 : Measure Edge) =
      (s.2.1.1 : Measure Edge) + (s.2.2.1 : Measure Edge) :=
    congrArg (fun p : PairScene ↦ (p.1 : Measure Edge)) hd
  have hm : (s.1.2.1.2 : Measure Edge) =
      (s.2.1.2 : Measure Edge) + (s.2.2.2 : Measure Edge) :=
    congrArg (fun p : PairScene ↦ (p.2 : Measure Edge)) hd
  have htest : LocalFiniteMeasure.testIntegral s.1.2.1.1 χ =
      LocalFiniteMeasure.testIntegral s.1.2.1.2 χ := by
    change (∫ e, χ e ∂(s.1.2.1.1 : Measure Edge)) = _
    rw [hfull]
    rfl
  have htriangle : |LocalFiniteMeasure.testIntegral s.2.1.1 χ -
      LocalFiniteMeasure.testIntegral s.2.1.2 χ| ≤
      |LocalFiniteMeasure.testIntegral s.1.2.1.1 χ -
        LocalFiniteMeasure.testIntegral s.2.1.1 χ| +
      |LocalFiniteMeasure.testIntegral s.1.2.1.2 χ -
        LocalFiniteMeasure.testIntegral s.2.1.2 χ| := by
    rw [htest]
    calc
      _ = |(LocalFiniteMeasure.testIntegral s.2.1.1 χ -
          LocalFiniteMeasure.testIntegral s.1.2.1.2 χ) +
          (LocalFiniteMeasure.testIntegral s.1.2.1.2 χ -
            LocalFiniteMeasure.testIntegral s.2.1.2 χ)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans_eq (by rw [abs_sub_comm
        (LocalFiniteMeasure.testIntegral s.2.1.1 χ)
        (LocalFiniteMeasure.testIntegral s.1.2.1.2 χ)])
  have hUp : MeasurableSet {e : Edge | e.1.1 ∈ U} := hU.preimage measurable_fst.fst
  have hbplus := LocalFiniteMeasure.ofReal_abs_testIntegral_sub_le_lost_mass
    s.1.2.1.1 s.2.1.1 s.2.2.1 hp χ _ hUp hχU
  have hbminus := LocalFiniteMeasure.ofReal_abs_testIntegral_sub_le_lost_mass
    s.1.2.1.2 s.2.1.2 s.2.2.2 hm χ _ hUp hχU
  calc
    _ ≤ ENNReal.ofReal (|LocalFiniteMeasure.testIntegral s.1.2.1.1 χ -
        LocalFiniteMeasure.testIntegral s.2.1.1 χ| +
        |LocalFiniteMeasure.testIntegral s.1.2.1.2 χ -
          LocalFiniteMeasure.testIntegral s.2.1.2 χ|) := ENNReal.ofReal_le_ofReal htriangle
    _ ≤ ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ *
        (s.2.2.1 : Measure Edge) {e : Edge | e.1.1 ∈ U} +
        ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ *
          (s.2.2.2 : Measure Edge) {e : Edge | e.1.1 ∈ U} := by
      rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact add_le_add hbplus hbminus
    _ = _ := by
      rw [physicalSceneMaskedLostSourceMass, LocalFiniteMeasure.coe_cavityAverage,
        Measure.smul_apply, Measure.add_apply, smul_eq_mul,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat]
      rw [← mul_add]
      have hinv : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      calc
        _ = ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ *
            (((2 : ℝ≥0∞)⁻¹ * 2) *
              ((s.2.2.1 : Measure Edge) {e : Edge | e.1.1 ∈ U} +
                (s.2.2.2 : Measure Edge) {e : Edge | e.1.1 ∈ U})) := by
          rw [hinv, one_mul]
        _ = _ := by ring


/-- Actual joint-law expectation of the retained difference is controlled by
actual lost source mass, including infinite values on either side. -/
theorem lintegral_retained_compact_difference_le_lost_of_full_agreement
    (Raux : Measure JointScene)
    (hdecomp : ∀ᵐ s ∂Raux, s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hfull : ∀ᵐ s ∂Raux, (s.1.2.1.1 : Measure Edge) = (s.1.2.1.2 : Measure Edge))
    (χ : C_c(Edge, ℝ)) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) :
    (∫⁻ s, ENNReal.ofReal |LocalFiniteMeasure.testIntegral s.2.1.1 χ -
      LocalFiniteMeasure.testIntegral s.2.1.2 χ| ∂Raux) ≤
      ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
        ∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂Raux := by
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
        physicalSceneMaskedLostSourceMass base U s ∂Raux := by
      apply lintegral_mono_ae
      filter_upwards [hdecomp, hfull] with s hd hf
      exact ofReal_retained_compact_difference_le_lost_of_full_agreement base s hd hf χ U hU hχU
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Exact full projection lifts agreement from the SAME prescribed full law
and supplies the actual retained/lost expectation estimate internally. -/
theorem lintegral_retained_compact_difference_le_lost_of_projected_full_agreement
    (Rfull : ProbabilityMeasure MacroScene) (Raux : ProbabilityMeasure JointScene)
    (hprojection : Raux.map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (hdecomp : ∀ᵐ s ∂(Raux : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hfull : ∀ᵐ s ∂(Rfull : Measure MacroScene),
      (s.2.1.1 : Measure Edge) = (s.2.1.2 : Measure Edge))
    (χ : C_c(Edge, ℝ)) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) :
    (∫⁻ s, ENNReal.ofReal |LocalFiniteMeasure.testIntegral s.2.1.1 χ -
      LocalFiniteMeasure.testIntegral s.2.1.2 χ| ∂(Raux : Measure JointScene)) ≤
      ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
        ∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂(Raux : Measure JointScene) := by
  rw [← hprojection] at hfull
  exact lintegral_retained_compact_difference_le_lost_of_full_agreement base
    (Raux : Measure JointScene) hdecomp (ae_of_ae_map measurable_fst.aemeasurable hfull)
    χ U hU hχU

/-- A bounded actual macro-tag weight preserves the same lost-mass estimate. -/
theorem lintegral_tagged_retained_compact_difference_le_lost_of_full_agreement
    (Raux : Measure JointScene)
    (hdecomp : ∀ᵐ s ∂Raux, s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hfull : ∀ᵐ s ∂Raux, (s.1.2.1.1 : Measure Edge) = (s.1.2.1.2 : Measure Edge))
    (tag : BoundedContinuousFunction (ι → ℝ) ℝ)
    (χ : C_c(Edge, ℝ)) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) :
    (∫⁻ s, ENNReal.ofReal |tag s.1.1 * (LocalFiniteMeasure.testIntegral s.2.1.1 χ -
      LocalFiniteMeasure.testIntegral s.2.1.2 χ)| ∂Raux) ≤
      ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
        ∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂Raux := by
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
        physicalSceneMaskedLostSourceMass base U s ∂Raux := by
      apply lintegral_mono_ae
      filter_upwards [hdecomp, hfull] with s hd hf
      have hb := ofReal_retained_compact_difference_le_lost_of_full_agreement base
        s hd hf χ U hU hχU
      rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
      calc
        _ ≤ ENNReal.ofReal ‖tag‖ * (ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
            physicalSceneMaskedLostSourceMass base U s) :=
          mul_le_mul (ENNReal.ofReal_le_ofReal (by
            simpa only [Real.norm_eq_abs] using tag.norm_coe_le_norm s.1.1)) hb
            (by positivity) (by positivity)
        _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
          congr 2
          ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The bounded weighted retained readout uses full agreement only on the
SAME full projection; no agreement premise on the auxiliary plans is supplied. -/
theorem lintegral_tagged_retained_compact_difference_le_lost_of_projected_full_agreement
    (Rfull : ProbabilityMeasure MacroScene) (Raux : ProbabilityMeasure JointScene)
    (hprojection : Raux.map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (hdecomp : ∀ᵐ s ∂(Raux : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hfull : ∀ᵐ s ∂(Rfull : Measure MacroScene),
      (s.2.1.1 : Measure Edge) = (s.2.1.2 : Measure Edge))
    (tag : BoundedContinuousFunction (ι → ℝ) ℝ)
    (χ : C_c(Edge, ℝ)) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) :
    (∫⁻ s, ENNReal.ofReal |tag s.1.1 * (LocalFiniteMeasure.testIntegral s.2.1.1 χ -
      LocalFiniteMeasure.testIntegral s.2.1.2 χ)| ∂(Raux : Measure JointScene)) ≤
      ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
        ∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂(Raux : Measure JointScene) := by
  rw [← hprojection] at hfull
  exact lintegral_tagged_retained_compact_difference_le_lost_of_full_agreement base
    (Raux : Measure JointScene) hdecomp (ae_of_ae_map measurable_fst.aemeasurable hfull)
    tag χ U hU hχU

end OTSelector.Reconstruction
