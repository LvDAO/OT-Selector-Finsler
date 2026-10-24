import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedLscDefect

/-!
# Original lost physical mass on a joint extension of the fixed full scene

The discarded pair consists of restrictions of the same original global plans.
Its source-window expectation is controlled on the unchanged Haar experiment;
the resulting probability bound survives the separate sample and tilt limits.
-/

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
local instance maskedLostLimitStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedLostLimitConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance maskedLostLimitConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedLostLimitConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance maskedLostLimitPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The arithmetic mean of the original discarded plans in a spatial source window. -/
def physicalSceneMaskedLostSourceMass (U : Set (ι → ℝ)) (s : JointScene) : ℝ≥0∞ :=
  (LocalFiniteMeasure.cavityAverage s.2.2 :
    Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) {e | e.1.1 ∈ U}

/-- Open source windows give a lower semicontinuous readout of the actual lost pair. -/
theorem lowerSemicontinuous_physicalSceneMaskedLostSourceMass
    {U : Set (ι → ℝ)} (hU : IsOpen U) :
    LowerSemicontinuous (physicalSceneMaskedLostSourceMass base U) :=
  (lowerSemicontinuous_cavityAverage_open (hU.preimage continuous_fst.fst)).comp
    continuous_snd.snd

/-- Every measurable joint readout is exactly the unchanged original experiment
and its original normalized Haar root integral. -/
theorem lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    (W : JointScene → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ s, W s ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
      coord hcoord u hu scale Y hY D hD : Measure JointScene)) =
      ∫⁻ w, ∫⁻ z, W (physicalSceneRootedMaskedMacroscopicObservation base Γp Γm H E
        coord u ((n : ℝ) + 1) scale Y (w, z))
        ∂cavityRootMeasure volume D ((n : ℝ) + 1) ∂Penv := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  have hObs := measurable_physicalSceneRootedMaskedMacroscopicObservation base Γp Γm hp hm
    H hH E hE coord hcoord u hu ((n : ℝ) + 1) scale Y hY
  change (∫⁻ s, W s ∂(Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map _) = _
  rw [lintegral_map hW hObs]
  exact lintegral_prod _ (hW.comp hObs).aemeasurable

/-- Only the original discarded global edge mass pays the observed lost source
window, with every actual restricted target column kept unchanged. -/
theorem lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw_lost_le {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γp Γm : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γp w)] [∀ w, IsFiniteMeasure (Γm w)]
    (hp : Measurable Γp) (hm : Measurable Γm)
    (H : Set M) (hH : MeasurableSet H) (E : Set (M × M)) (hE : MeasurableSet E)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : volume U ≠ ⊤) (C : ℝ≥0∞)
    (hCp : (∫⁻ w, Γp w Eᶜ ∂Penv) ≤ C)
    (hCm : (∫⁻ w, Γm w Eᶜ ∂Penv) ≤ C) :
    (∫⁻ s, physicalSceneMaskedLostSourceMass base U s
      ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm H hH E hE
        coord hcoord u hu scale Y hY D hD : Measure JointScene)) ≤ volume U * C := by
  rw [lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw base Penv Γp Γm hp hm
    H hH E hE coord hcoord u hu scale Y hY D hD _
    (lowerSemicontinuous_physicalSceneMaskedLostSourceMass base hU).measurable]
  have hr (Γ : Measure (M × M)) :
      (Γ.restrict Eᶜ).restrict (H ×ˢ univ) = Γ.restrict (Eᶜ ∩ (H ×ˢ univ)) := by
    rw [Measure.restrict_restrict (hH.prod MeasurableSet.univ), inter_comm]
  simpa only [physicalSceneMaskedLostSourceMass, physicalSceneRootedMaskedMacroscopicObservation,
    physicalSceneRootedLocalScene, LocalFiniteMeasure.coe_cavityAverage,
    coe_physicalSceneRootedLocalPlan, hr] using
    lintegral_physicalSceneRooted_average_endpoint_loss_le Penv Γp Γm hp hm E hE H hH
      coord hcoord u hu ((n : ℝ) + 1) (by positivity) D U hD hU.measurableSet hUf C hCp hCm

/-- The actual lost source-window mass keeps only the fixed auxiliary population
loss after the sample stage; the tilt stage preserves the same bound. -/
theorem measure_lostSourceMass_gt_le_of_iterated_masked_scene
    (P : ℕ → ℕ → ProbabilityMeasure JointScene) (Q : ℕ → ProbabilityMeasure JointScene)
    (R : ProbabilityMeasure JointScene)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ P ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : volume U ≠ ⊤)
    (loss : ℝ≥0∞) (sample : ℕ → ℝ≥0∞) (hsample : Tendsto sample atTop (𝓝 0))
    (hbound : ∀ ℓ, ∀ᶠ n in atTop,
      (∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂(P ℓ n : Measure JointScene)) ≤
        volume U * (loss + sample n))
    (level : ℝ≥0∞) (hl0 : 0 < level) (hlt : level ≠ ⊤) :
    (R : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base U s} ≤
      (volume U * loss) / level := by
  apply measure_lsc_gt_le_of_iterated_weak_sample_tilt_defect_bounds P Q R φ hφ ψ hψ
    hinner houter _ (lowerSemicontinuous_physicalSceneMaskedLostSourceMass base hU)
    (volume U * loss) (fun _ ↦ 0) (fun n ↦ volume U * sample n)
    tendsto_const_nhds ?_ ?_ level hl0 hlt
  · simpa only [mul_zero] using ENNReal.Tendsto.const_mul hsample (Or.inr hUf)
  · exact Eventually.of_forall fun ℓ ↦ (hbound ℓ).mono fun n hn ↦ by
      simpa only [zero_add, mul_add] using hn

end OTSelector.Reconstruction
