import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedTaggedCompactReadout
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutClipping
import OTSelector.MeasureTheory.LocalFiniteMeasureReadoutLoss
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedLossLimit

/-!
# Actual masked loss bounds full compact readout clipping

A bounded retained readout approximates the full tagged compact readout on its
original joint scene. Their actual retained/lost decomposition controls clipping
error by discarded source mass, including infinite discarded mass.
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
local instance maskedClippingReadoutStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance maskedClippingReadoutConfigTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance maskedClippingReadoutConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance maskedClippingReadoutConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance maskedClippingReadoutPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The full compact readout keeps the original macro tag and the selected full plan. -/
def physicalSceneFullTaggedCompactReadout (χ : C_c(Edge, ℝ)) (plus : Bool)
    (tag : BoundedContinuousFunction (ι → ℝ) ℝ) (s : MacroScene) : ℝ :=
  tag s.1 * LocalFiniteMeasure.testIntegral (if plus then s.2.1.1 else s.2.1.2) χ

theorem continuous_physicalSceneFullTaggedCompactReadout (χ : C_c(Edge, ℝ)) (plus : Bool)
    (tag : BoundedContinuousFunction (ι → ℝ) ℝ) :
    Continuous (physicalSceneFullTaggedCompactReadout base χ plus tag) := by
  cases plus
  · exact (tag.continuous.comp continuous_fst).mul
      ((LocalFiniteMeasure.continuous_testIntegral χ).comp continuous_snd.fst.snd)
  · exact (tag.continuous.comp continuous_fst).mul
      ((LocalFiniteMeasure.continuous_testIntegral χ).comp continuous_snd.fst.fst)

/-- A bounded actual retained readout controls clipping of the SAME full readout
by original discarded source mass, without any finite lost-mass assumption. -/
theorem ofReal_full_tagged_compact_clipping_error_le_lost
    (s : JointScene) (hdecomp : s ∈ physicalSceneMaskedDecompositionCarrier base)
    (χ : C_c(Edge, ℝ)) (plus : Bool) (tag : BoundedContinuousFunction (ι → ℝ) ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) (K : ℝ)
    (hbound : |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ K) :
    ENNReal.ofReal |physicalSceneFullTaggedCompactReadout base χ plus tag s.1 -
      continuousReadoutClip K (physicalSceneFullTaggedCompactReadout base χ plus tag) s.1| ≤
      ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
        physicalSceneMaskedLostSourceMass base U s := by
  let full := if plus then s.1.2.1.1 else s.1.2.1.2
  let retained := if plus then s.2.1.1 else s.2.1.2
  let lost := if plus then s.2.2.1 else s.2.2.2
  have hd : s.1.2.1 = physicalScenePairSum s.2 := hdecomp
  have hdec : (full : Measure Edge) = (retained : Measure Edge) + (lost : Measure Edge) := by
    cases plus
    · exact congrArg (fun p : PairScene ↦ (p.2 : Measure Edge)) hd
    · exact congrArg (fun p : PairScene ↦ (p.1 : Measure Edge)) hd
  have herr := LocalFiniteMeasure.ofReal_abs_testIntegral_sub_le_lost_mass
    full retained lost hdec χ _ (hU.preimage measurable_fst.fst) hχU
  have hsum : (lost : Measure Edge) {e : Edge | e.1.1 ∈ U} ≤
      (s.2.2.1 : Measure Edge) {e : Edge | e.1.1 ∈ U} +
        (s.2.2.2 : Measure Edge) {e : Edge | e.1.1 ∈ U} := by
    cases plus
    · exact le_add_left le_rfl
    · exact le_add_right le_rfl
  have hsumEq : (s.2.2.1 : Measure Edge) {e : Edge | e.1.1 ∈ U} +
      (s.2.2.2 : Measure Edge) {e : Edge | e.1.1 ∈ U} =
        2 * physicalSceneMaskedLostSourceMass base U s := by
    rw [physicalSceneMaskedLostSourceMass, LocalFiniteMeasure.coe_cavityAverage,
      Measure.smul_apply, Measure.add_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have htag : ENNReal.ofReal |tag s.1.1| ≤ ENNReal.ofReal ‖tag‖ :=
    ENNReal.ofReal_le_ofReal (by
      simpa only [Real.norm_eq_abs] using tag.norm_coe_le_norm s.1.1)
  calc
    _ ≤ ENNReal.ofReal |physicalSceneFullTaggedCompactReadout base χ plus tag s.1 -
        physicalSceneRetainedTaggedCompactReadout base χ plus tag s| :=
      ENNReal.ofReal_le_ofReal
        (abs_sub_continuousReadoutClip_le K
          (physicalSceneFullTaggedCompactReadout base χ plus tag) s.1 _ hbound)
    _ = ENNReal.ofReal |tag s.1.1| * ENNReal.ofReal
        |LocalFiniteMeasure.testIntegral full χ - LocalFiniteMeasure.testIntegral retained χ| := by
      have hr : physicalSceneRetainedTaggedCompactReadout base χ plus tag s =
          tag s.1.1 * LocalFiniteMeasure.testIntegral retained χ := by cases plus <;> rfl
      rw [hr]
      change ENNReal.ofReal |tag s.1.1 * LocalFiniteMeasure.testIntegral full χ -
        tag s.1.1 * LocalFiniteMeasure.testIntegral retained χ| = _
      rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ ENNReal.ofReal ‖tag‖ * (ENNReal.ofReal ‖χ.toBoundedContinuousFunction‖ *
        (2 * physicalSceneMaskedLostSourceMass base U s)) :=
      (mul_le_mul htag herr (by positivity) (by positivity)).trans (by gcongr; exact hsum.trans_eq hsumEq)
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (norm_nonneg _)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      ring

/-- The finite actual joint law transfers the full clipping error to its actual
lost expectation; each original core may have its own retained bound. -/
theorem lintegral_full_tagged_compact_clipping_error_le_lost
    (Raux : Measure JointScene)
    (hdecomp : ∀ᵐ s ∂Raux, s ∈ physicalSceneMaskedDecompositionCarrier base)
    (χ : C_c(Edge, ℝ)) (plus : Bool) (tag : BoundedContinuousFunction (ι → ℝ) ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) (K : ℝ)
    (hbound : ∀ᵐ s ∂Raux, |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ K) :
    (∫⁻ s, ENNReal.ofReal |physicalSceneFullTaggedCompactReadout base χ plus tag s.1 -
      continuousReadoutClip K (physicalSceneFullTaggedCompactReadout base χ plus tag) s.1| ∂Raux) ≤
      ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
        ∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂Raux := by
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
        physicalSceneMaskedLostSourceMass base U s ∂Raux := by
      apply lintegral_mono_ae
      filter_upwards [hdecomp, hbound] with s hd hb
      exact ofReal_full_tagged_compact_clipping_error_le_lost base s hd χ plus tag U hU hχU K hb
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end OTSelector.Reconstruction
