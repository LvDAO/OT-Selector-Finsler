import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClockWindows
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedLossLimit

/-! Full clock collars on the unchanged original masked joint scene. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance maskedClockWindowStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedClockWindowConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance maskedClockWindowConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedClockWindowConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedClockWindowPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Both full original plans are read in their actual spatial source window
and original endpoint clock band. Auxiliary retained/lost components are ignored. -/
def physicalSceneMaskedFullClockMass (U : Set (ι → ℝ)) (T : Set (ℝ × ℝ))
    (s : JointScene) : ℝ≥0∞ :=
  (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge)
    (physicalSceneRootedClockWindow U T)

/-- Original open clock bands give a lower semicontinuous full-plan readout. -/
theorem lowerSemicontinuous_physicalSceneMaskedFullClockMass
    {U : Set (ι → ℝ)} (hU : IsOpen U) {T : Set (ℝ × ℝ)} (hT : IsOpen T) :
    LowerSemicontinuous (physicalSceneMaskedFullClockMass base U T) :=
  (lowerSemicontinuous_cavityAverage_open (isOpen_physicalSceneRootedClockWindow hU hT)).comp
    continuous_fst.snd.fst

/-- The same original expected clock-band mass bounds the complete joint
scene readout, independently of the chosen retained event and physical scale. -/
theorem lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw_fullClock_le {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : volume U ≠ ⊤)
    (T : Set (ℝ × ℝ)) (hT : IsOpen T) (C : ℝ≥0∞)
    (hCp : (∫⁻ w, Γp w ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' T) ∂Penv) ≤ C)
    (hCm : (∫⁻ w, Γm w ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' T) ∂Penv) ≤ C) :
    (∫⁻ s, physicalSceneMaskedFullClockMass base U T s
      ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
        coord hcoord u hu scale Y hY D hD : Measure JointScene)) ≤ volume U * C := by
  let Q := (fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' T
  have hQ : MeasurableSet Q := hT.measurableSet.preimage
    ((hu.comp measurable_fst).prodMk (hu.comp measurable_snd))
  have hr (Γ : Measure (M × M)) :
      (Γ.restrict (H ×ˢ univ)).restrict Q = Γ.restrict (Q ∩ (H ×ˢ univ)) := by
    rw [Measure.restrict_restrict hQ]
  have heq (Γ : Measure (M × M)) (z : ι → ℝ) :
      physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u ((n : ℝ) + 1) z
        (physicalSceneRootedClockWindow U T) =
      physicalSceneRootedPlan (Γ.restrict (Q ∩ (H ×ˢ univ))) coord u ((n : ℝ) + 1) z
        {e | e.1.1 ∈ U} := by
    rw [physicalSceneRootedPlan_clockWindow_eq_restrict _ coord hcoord u hu _ _
      hU.measurableSet hT.measurableSet, hr]
  rw [lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm
    H hH E hE coord hcoord u hu scale Y hY D hD _
    (lowerSemicontinuous_physicalSceneMaskedFullClockMass base hU hT).measurable]
  have hb := lintegral_physicalSceneRooted_average_endpoint_loss_le Penv Γp Γm hp hm
    Qᶜ hQ.compl H hH coord hcoord u hu ((n : ℝ) + 1) (by positivity)
    D U hD hU.measurableSet hUf C (by simpa only [compl_compl] using hCp)
    (by simpa only [compl_compl] using hCm)
  simpa only [physicalSceneMaskedFullClockMass, physicalSceneRootedMaskedMacroscopicObservation,
    physicalSceneRootedMacroscopicObservation, physicalSceneRootedCountableObservation,
    physicalSceneRootedLocalScene, LocalFiniteMeasure.coe_cavityAverage,
    coe_physicalSceneRootedLocalPlan, Measure.smul_apply, Measure.add_apply, heq,
    compl_compl] using hb
end OTSelector.Reconstruction
