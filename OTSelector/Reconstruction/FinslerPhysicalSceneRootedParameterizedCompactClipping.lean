import OTSelector.MeasureTheory.ParameterizedCompactReadout
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedCompactClipping

/-!
# Joint compact kernels have actual masked clipping budgets

Each actual macro tag selects its own compact edge slice. Uniform support and
norm control transfer the original retained/lost estimate to the joint test.
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
local instance parameterizedClippingReadoutStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance parameterizedClippingReadoutConfigTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance parameterizedClippingReadoutConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance parameterizedClippingReadoutConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance parameterizedClippingReadoutPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The full readout evaluates the actual joint compact kernel at its own macro tag. -/
def physicalSceneFullParameterizedCompactReadout (G : C_c((ι → ℝ) × Edge, ℝ))
    (plus : Bool) (s : MacroScene) : ℝ :=
  parameterizedCompactReadout G (s.1, if plus then s.2.1.1 else s.2.1.2)

/-- The retained readout keeps the same original macro tag. -/
def physicalSceneRetainedParameterizedCompactReadout (G : C_c((ι → ℝ) × Edge, ℝ))
    (plus : Bool) (s : JointScene) : ℝ :=
  parameterizedCompactReadout G (s.1.1, if plus then s.2.1.1 else s.2.1.2)

theorem continuous_physicalSceneFullParameterizedCompactReadout
    (G : C_c((ι → ℝ) × Edge, ℝ)) (plus : Bool) :
    Continuous (physicalSceneFullParameterizedCompactReadout base G plus) := by
  cases plus
  · exact (continuous_parameterizedCompactReadout G).comp
      (continuous_fst.prodMk continuous_snd.fst.snd)
  · exact (continuous_parameterizedCompactReadout G).comp
      (continuous_fst.prodMk continuous_snd.fst.fst)

theorem continuous_physicalSceneRetainedParameterizedCompactReadout
    (G : C_c((ι → ℝ) × Edge, ℝ)) (plus : Bool) :
    Continuous (physicalSceneRetainedParameterizedCompactReadout base G plus) := by
  cases plus
  · exact (continuous_parameterizedCompactReadout G).comp
      (continuous_fst.fst.prodMk continuous_snd.fst.snd)
  · exact (continuous_parameterizedCompactReadout G).comp
      (continuous_fst.fst.prodMk continuous_snd.fst.fst)

/-- The current parameter slice may be used in the actual full clipping estimate;
its support and norm are controlled by the original joint compact test. -/
theorem ofReal_full_parameterized_compact_clipping_error_le_lost
    (s : JointScene) (hdecomp : s ∈ physicalSceneMaskedDecompositionCarrier base)
    (G : C_c((ι → ℝ) × Edge, ℝ)) (plus : Bool)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hGU : tsupport G ⊆ {p : (ι → ℝ) × Edge | p.2.1.1 ∈ U}) (K : ℝ)
    (hbound : |physicalSceneRetainedParameterizedCompactReadout base G plus s| ≤ K) :
    ENNReal.ofReal |physicalSceneFullParameterizedCompactReadout base G plus s.1 -
      continuousReadoutClip K (physicalSceneFullParameterizedCompactReadout base G plus) s.1| ≤
      ENNReal.ofReal (2 * ‖G.toBoundedContinuousFunction‖) *
        physicalSceneMaskedLostSourceMass base U s := by
  let χ := parameterizedCompactSlice G s.1.1
  have hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U} := by
    intro e he
    rcases tsupport_parameterizedCompactSlice_subset G s.1.1 he with ⟨p, hp, rfl⟩
    exact hGU hp
  have hret : physicalSceneRetainedParameterizedCompactReadout base G plus s =
      physicalSceneRetainedTaggedCompactReadout base χ plus 1 s := by
    cases plus <;> simp [physicalSceneRetainedParameterizedCompactReadout,
      physicalSceneRetainedTaggedCompactReadout, physicalSceneRetainedCompactReadout,
      parameterizedCompactReadout, χ]
  have hfull : physicalSceneFullParameterizedCompactReadout base G plus s.1 =
      physicalSceneFullTaggedCompactReadout base χ plus 1 s.1 := by
    cases plus <;> simp [physicalSceneFullParameterizedCompactReadout,
      physicalSceneFullTaggedCompactReadout, parameterizedCompactReadout, χ]
  have hb := ofReal_full_tagged_compact_clipping_error_le_lost base s hdecomp χ plus 1
    U hU hχU K (by simpa only [← hret] using hbound)
  have hC : ENNReal.ofReal (2 * ‖(1 : BoundedContinuousFunction (ι → ℝ) ℝ)‖ *
      ‖χ.toBoundedContinuousFunction‖) ≤ ENNReal.ofReal (2 * ‖G.toBoundedContinuousFunction‖) := by
    apply ENNReal.ofReal_le_ofReal
    simpa only [norm_one, mul_one] using
      mul_le_mul_of_nonneg_left (norm_parameterizedCompactSlice_le G s.1.1)
        (by norm_num : (0 : ℝ) ≤ 2)
  have heq : ENNReal.ofReal |physicalSceneFullParameterizedCompactReadout base G plus s.1 -
      continuousReadoutClip K (physicalSceneFullParameterizedCompactReadout base G plus) s.1| =
      ENNReal.ofReal |physicalSceneFullTaggedCompactReadout base χ plus 1 s.1 -
        continuousReadoutClip K (physicalSceneFullTaggedCompactReadout base χ plus 1) s.1| := by
    simp only [continuousReadoutClip, hfull]
  rw [heq]
  exact hb.trans (mul_le_mul_left hC _)

/-- The same full-law projection inherits the expected actual discarded-mass bound. -/
theorem lintegral_full_parameterized_compact_clipping_error_le_lost
    (Raux : Measure JointScene)
    (hdecomp : ∀ᵐ s ∂Raux, s ∈ physicalSceneMaskedDecompositionCarrier base)
    (G : C_c((ι → ℝ) × Edge, ℝ)) (plus : Bool)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hGU : tsupport G ⊆ {p : (ι → ℝ) × Edge | p.2.1.1 ∈ U}) (K : ℝ)
    (hbound : ∀ᵐ s ∂Raux, |physicalSceneRetainedParameterizedCompactReadout base G plus s| ≤ K) :
    (∫⁻ s, ENNReal.ofReal |physicalSceneFullParameterizedCompactReadout base G plus s.1 -
      continuousReadoutClip K (physicalSceneFullParameterizedCompactReadout base G plus) s.1| ∂Raux) ≤
      ENNReal.ofReal (2 * ‖G.toBoundedContinuousFunction‖) *
        ∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂Raux := by
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal (2 * ‖G.toBoundedContinuousFunction‖) *
        physicalSceneMaskedLostSourceMass base U s ∂Raux := by
      apply lintegral_mono_ae
      filter_upwards [hdecomp, hbound] with s hd hb
      exact ofReal_full_parameterized_compact_clipping_error_le_lost base s hd G plus U hU hGU K hb
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end OTSelector.Reconstruction
