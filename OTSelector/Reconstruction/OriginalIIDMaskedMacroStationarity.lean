import OTSelector.Reconstruction.OriginalIIDMaskedBipartiteMacroScene
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootConditionalPhysical

/-! The same actual masked iid macro weak limit supplies conditional spatial
stationarity of its original pair-plan projection. Both original input records
remain in the parent joint law; this projection does not assert stationarity of
the full colored-input scene. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance maskedMacroStationarityStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance maskedMacroStationarityConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance maskedMacroStationarityConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance maskedMacroStationarityConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance maskedMacroStationarityPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance maskedMacroStationarityPlanNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  ⟨⟨0, inferInstance⟩⟩
set_option quotPrecheck false
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "Macro" => (ι → ℝ) × (PairScene × LocalConfiguration base)

/-- Retain the original common macroscopic root and both original pair plans. -/
def originalIIDMaskedMacroPlanProjection (s : Macro × Macro) : (ι → ℝ) × PairScene :=
  (s.1.1,s.1.2.1)

/-- Forgetting the literal input records is a continuous projection. -/
theorem continuous_originalIIDMaskedMacroPlanProjection :
    Continuous (originalIIDMaskedMacroPlanProjection base) :=
  continuous_fst.fst.prodMk continuous_fst.snd.fst

/-- The plan projection keeps the exact optimizer, source mask and integer
edge prefactor n+1 from the original two-product iid experiment. -/
theorem originalIIDMaskedMacroPlanProjection_observation
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ) (H : Set M)
    (coord : M → (ι → ℝ)) (u : M → ℝ) (scale : ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    originalIIDMaskedMacroPlanProjection base
      (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale w) =
      (physicalSceneMacroscopicRoot scale w.2,
        physicalSceneRootedLocalScene
          (fun ξ ↦ (originalIIDOptimalPhysicalPlan (n := n + 1) cost k ξ).restrict (H ×ˢ univ))
          (fun ξ ↦ (originalIIDOptimalPhysicalPlan (n := n + 1) cost k ξ).restrict (H ×ˢ univ))
          coord u ((n : ℝ) + 1) w) := rfl

/-- The original macro-root and pair-plan marginal of the same masked joint law. -/
def originalIIDMaskedMacroPlanLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) : ProbabilityMeasure ((ι → ℝ) × PairScene) :=
  (originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH coord hcoord u hu).map
    (continuous_originalIIDMaskedMacroPlanProjection base).measurable.aemeasurable

/-- The projected finite law is exactly the actual Haar-cube average of the
same original physical plans, with root cube mass and edge prefactor n+1. -/
theorem originalIIDMaskedMacroPlanLaw_eq_haarCubeAverageLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    (originalIIDMaskedMacroPlanLaw base μ ν hq cost hcost k n H hH coord hcoord u hu :
      Measure ((ι → ℝ) × PairScene)) =
      haarCubeAverageLaw
        ((Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))
        (fun w ↦ (physicalSceneMacroscopicRoot
            (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)) w.2,
          physicalSceneRootedLocalScene
            (fun ξ ↦ (originalIIDOptimalPhysicalPlan (n := n + 1) cost k ξ).restrict (H ×ˢ univ))
            (fun ξ ↦ (originalIIDOptimalPhysicalPlan (n := n + 1) cost k ξ).restrict (H ×ˢ univ))
            coord u ((n : ℝ) + 1) w))
        (haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)) := by
  rw [originalIIDMaskedMacroPlanLaw, ProbabilityMeasure.toMeasure_map]
  change ((((Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))).prod (cavityRootMeasure volume
      (haarRootCube ι (haarRootRadius (Fintype.card ι) ((n : ℝ) + 1))) ((n : ℝ) + 1))).map
      (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u
        (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)))).map
      (originalIIDMaskedMacroPlanProjection base) = _
  rw [Measure.map_map (continuous_originalIIDMaskedMacroPlanProjection base).measurable
    (measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
      coord hcoord u hu _)]
  simp only [Function.comp_def, originalIIDMaskedMacroPlanProjection_observation]
  rw [haarCubeAverageLaw, haarCubeRootLaw, haarRootRadius_mass _ hq (by positivity)]

/-- Every prescribed weak limit of the masked joint laws retains this exact
macro-root/plan projection along the same sample subsequence. -/
theorem tendsto_originalIIDMaskedMacroPlanLaw_of_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (m : ℕ → ℕ)
    {Q : ProbabilityMeasure (Macro × Macro)}
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q)) :
    Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop
      (𝓝 (Q.map (continuous_originalIIDMaskedMacroPlanProjection base).measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hweak
    (continuous_originalIIDMaskedMacroPlanProjection base)

/-- The same actual growing-scale iid optimizer has conditionally stationary
pair plans at almost every retained macroscopic root, simultaneously under all
physical translations. No desired stationarity or replacement scene is assumed. -/
theorem ae_conditional_physicalSceneReroot_of_originalIIDMaskedMacro_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    {Q : ProbabilityMeasure (Macro × Macro)}
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q)) :
    let ρ := (Q.map
      (continuous_originalIIDMaskedMacroPlanProjection base).measurable.aemeasurable :
        Measure ((ι → ℝ) × PairScene))
    ∀ᵐ w ∂ρ.fst, ∀ v : ι → ℝ,
      MeasurePreserving (physicalSceneReroot v) (ρ.condKernel w) (ρ.condKernel w) := by
  let P := fun n ↦ (Measure.pi (fun _ : Fin (m n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (m n + 1) ↦ ν))
  let Γ := fun n ξ ↦ (originalIIDOptimalPhysicalPlan (n := m n + 1)
    (cost (m n)) (k (m n)) ξ).restrict (H ×ˢ univ)
  have hΓ (n : ℕ) : Measurable (Γ n) :=
    measurable_physicalPlan_sourceRestriction _
      (measurable_originalIIDOptimalPhysicalPlan (cost (m n)) (hcost (m n)) (k (m n))) H hH
  let N := fun n ↦ (m n : ℝ) + 1
  let radius := fun n ↦ haarRootRadius (Fintype.card ι) (N n)
  have hR (n : ℕ) : 0 < radius n := haarRootRadius_pos _ (by dsimp [N]; positivity)
  have hNlarge : Tendsto N atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp hm)
  have hRlarge : Tendsto radius atTop atTop := tendsto_haarRootRadius _ hq hNlarge
  have hslarge : Tendsto (fun n ↦ 2 * radius n) atTop atTop :=
    hRlarge.const_mul_atTop (by norm_num)
  let laws := fun n ↦ originalIIDMaskedMacroPlanLaw base μ ν hq
    (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
    (coord (m n)) (hcoord (m n)) u hu
  have hlaw (n : ℕ) : (laws n : Measure ((ι → ℝ) × PairScene)) =
      haarCubeAverageLaw (P n)
        (fun p ↦ ((fun i ↦ p.2 i / (2 * radius n)),
          physicalSceneRootedLocalScene (Γ n) (Γ n) (coord (m n)) u (N n) p)) (radius n) :=
    originalIIDMaskedMacroPlanLaw_eq_haarCubeAverageLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu
  exact ae_conditional_physicalSceneReroot_of_macroRooted_tendsto P Γ Γ hΓ hΓ
    (fun n ↦ coord (m n)) (fun n ↦ hcoord (m n)) u hu
    N radius (fun n ↦ 2 * radius n) hR hRlarge hslarge laws hlaw
    (tendsto_originalIIDMaskedMacroPlanLaw_of_tendsto base μ ν hq cost hcost k H hH
      coord hcoord u hu m hweak)

end OTSelector.Reconstruction
