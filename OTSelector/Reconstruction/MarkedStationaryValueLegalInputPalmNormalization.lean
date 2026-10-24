import OTSelector.Reconstruction.MarkedStationaryValueLegalInputIntensity
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputFullScene

/-!
# The actual full-input stationary weak scene has its prescribed probability Palm

Projection forgets only the immutable input factor and retains the same actual
original legal optimal plans. Their complete input marginals and exact original
Poisson mean intensities normalize the true full-displacement pair Palm.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputPalmNormalizationInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputPalmNormalizationPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Keep the actual matching pair and forget only its unchanged input factor. -/
def legalMarkedInputPairLaw (q : ℕ) (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    ProbabilityMeasure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)) :=
  Q.map measurable_fst.aemeasurable

theorem measurePreserving_legalMarkedInputPairLaw (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)))
    (v : Fin q → ℝ) :
    MeasurePreserving (physicalSceneReroot v)
      (legalMarkedInputPairLaw q Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
      (legalMarkedInputPairLaw q Q : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) := by
  refine ⟨(continuous_physicalSceneReroot v).measurable, ?_⟩
  change ((Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst).map (physicalSceneReroot v) =
    (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst
  rw [Measure.map_map (continuous_physicalSceneReroot v).measurable measurable_fst]
  have heq : physicalSceneReroot v ∘ Prod.fst = Prod.fst ∘ legalMarkedInputSceneReroot q v := rfl
  rw [heq, ← Measure.map_map measurable_fst (continuous_legalMarkedInputSceneReroot q v).measurable,
    (hstat v).map_eq]

/-- Forgetting only the input factor preserves the literal actual optimal
pair weak limit, so its original legality and energy theorems apply unchanged. -/
theorem legalMarkedInputPairLaw_tendsto
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    Tendsto (fun k ↦ legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 (legalMarkedInputPairLaw q Q)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ Q hweak continuous_fst
  have hproj (k : ℕ) :
      (legalMarkedOptimalInputSceneLaw q α β kin hk g hg t (L k) (hL k)).map
        measurable_fst.aemeasurable =
        legalMarkedOptimalRootedSceneLaw q hq α β kin hk g hg t (L k) (hL k) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact map_legalMarkedOptimalInputSceneLaw_fst q hq α β kin hk g hg t (hL k)
  simpa only [legalMarkedInputPairLaw, hproj] using h

/-- The same actual joint weak scene and its own pair Palm keep the original
positive forward gap, with no replacement of its complete bipartite graph. -/
theorem ae_cubePalm_legalMarkedInputPairLaw_clockGap
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    {δ : ℝ} (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|) :
    ∀ᵐ m ∂cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))),
      δ ≤ m.1.2 - m.1.1 :=
  (ae_cubePalm_clockGap_of_legalMarkedOptimalRootedSceneLaw_tendsto q hq α β kin hk g hg t
    L hL (legalMarkedInputPairLaw_tendsto q hq α β kin hk g hg t L hL hweak) hsep).2

/-- Exact whole input marginals identify both true matching intensity measures
with the corresponding original same-scene input intensities. -/
theorem physicalScene_intensities_eq_inputColors (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hfull : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1) :
    physicalSceneSourceIntensity (legalMarkedInputPairLaw q Q :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      legalMarkedInputColorIntensity q (Q : Measure (LegalMarkedOptimalInputScene q)) 0 ∧
    physicalSceneTargetIntensity (legalMarkedInputPairLaw q Q :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      legalMarkedInputColorIntensity q (Q : Measure (LegalMarkedOptimalInputScene q)) 1 := by
  constructor
  · ext B hB
    change (((Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst).bind physicalSceneSourceKernel) B = _
    rw [Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
      legalMarkedInputColorIntensity, Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
    rw [lintegral_map (f := fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      physicalSceneSourceKernel scene B) (Kernel.measurable_coe _ hB) measurable_fst]
    apply lintegral_congr_ae
    filter_upwards [hfull] with s hs
    have hk : physicalSceneSourceKernel s.1 = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst := by
      rw [physicalSceneSourceKernel, Kernel.map_apply _ measurable_fst]
      rfl
    rw [hk, legalMarkedInputColorKernel_apply]
    exact congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ B) hs.1
  · ext B hB
    change (((Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst).bind physicalSceneTargetKernel) B = _
    rw [Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
      legalMarkedInputColorIntensity, Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
    rw [lintegral_map (f := fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      physicalSceneTargetKernel scene B) (Kernel.measurable_coe _ hB) measurable_fst]
    apply lintegral_congr_ae
    filter_upwards [hfull] with s hs
    have hk : physicalSceneTargetKernel s.1 = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd := by
      rw [physicalSceneTargetKernel, Kernel.map_apply _ measurable_snd]
      rfl
    rw [hk, legalMarkedInputColorKernel_apply]
    exact congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ B) hs.2

/-- The actual joint weak law with its internally recovered full original
inputs has a probability pair Palm and exactly both original scalar-clock
marginals. The source-unit moment and normalization are produced internally. -/
theorem probability_cubePalm_of_legalMarkedInputSceneLaw_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)))
    (hfull : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1) :
    IsProbabilityMeasure (cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) ∧
    (cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))).map
        (fun m ↦ m.1.1) = α ∧
    (cubePalm (Fin q) (physicalScenePairCampbell (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))).map
        (fun m ↦ m.1.2) = β := by
  obtain ⟨hs, ht⟩ := physicalScene_intensities_eq_inputColors q Q hfull
  obtain ⟨hα, hβ⟩ := legalMarkedInputColorIntensities_eq_of_tendsto q α β kin hk g hg t L hL hlarge hweak
  exact probability_cubePalm_physicalScenePairCampbell_clock_marginals _
    (measurePreserving_legalMarkedInputPairLaw q Q hstat) α β (hs.trans hα) (ht.trans hβ)

end OTSelector.Reconstruction
