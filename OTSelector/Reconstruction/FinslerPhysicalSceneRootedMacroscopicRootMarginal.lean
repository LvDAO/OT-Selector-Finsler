import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMacroscopic

/-!
# Exact original macroscopic root marginals

The tag marginal of the actual joint allocation scene is exactly the original
normalized Haar root under its original inverse spatial scale. The same
marginal is retained through the separate sample and tilt weak limits.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]
variable (base : (ι → ℝ) × ℝ)
local instance macroscopicRootMarginalStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance macroscopicRootMarginalConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance macroscopicRootMarginalConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance macroscopicRootMarginalConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance macroscopicRootMarginalPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- The actual normalized Haar root observed at its original macroscopic scale. -/
def physicalSceneMacroscopicRootLaw (n : ℕ) (scale : ℝ) (D : Set (ι → ℝ))
    (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) : ProbabilityMeasure (ι → ℝ) := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  exact ⟨(cavityRootMeasure volume D ((n : ℝ) + 1)).map
    (physicalSceneMacroscopicRoot scale), Measure.isProbabilityMeasure_map
      (continuous_physicalSceneMacroscopicRoot scale).measurable.aemeasurable⟩

/-- The actual full joint law's macro tag has precisely the original normalized
root marginal, independently of which original physical plans were observed. -/
theorem map_physicalSceneRootedMacroscopicSceneLaw_root {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    (physicalSceneRootedMacroscopicSceneLaw base Penv Γplus Γminus hplus hminus H hH
      coord hcoord u hu scale Y hY D hD).map (f := Prod.fst) measurable_fst.aemeasurable =
        physicalSceneMacroscopicRootLaw n scale D hD := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have := isProbabilityMeasure_cavityRootMeasure volume D ((n : ℝ) + 1) hN hD
  apply Subtype.ext
  change ((Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneRootedMacroscopicObservation base
      (fun w ↦ (Γplus w).restrict (H ×ˢ univ))
      (fun w ↦ (Γminus w).restrict (H ×ˢ univ)) coord u ((n : ℝ) + 1) scale Y)).map Prod.fst = _
  rw [Measure.map_map measurable_fst
    (measurable_physicalSceneRootedMacroscopicObservation base _ _
      (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
      (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
      coord hcoord u hu ((n : ℝ) + 1) scale Y hY)]
  change (Penv.prod (cavityRootMeasure volume D ((n : ℝ) + 1))).map
    (physicalSceneMacroscopicRoot scale ∘ Prod.snd) = _
  rw [← Measure.map_map (continuous_physicalSceneMacroscopicRoot scale).measurable
    measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  rfl

/-- Original global allocation families retain exactly the same original macro
root marginal, with their realized random restricted columns unchanged. -/
theorem map_actualAllocationRootedMacroscopicSceneLaw_root {n : ℕ}
    (Penv : Measure Ω) [IsProbabilityMeasure Penv] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (scale : ℝ)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    (actualAllocationRootedMacroscopicSceneLaw base Penv μ aplus aminus hplus hminus
      Y hY H hH coord hcoord u hu scale D hD).map (f := Prod.fst) measurable_fst.aemeasurable =
        physicalSceneMacroscopicRootLaw n scale D hD :=
  map_physicalSceneRootedMacroscopicSceneLaw_root base Penv _ _ _ _ H hH
    coord hcoord u hu scale Y hY D hD

/-- The exact original root marginal is preserved under a weak limit whenever
that original root law converges; no new coupling or root law is selected. -/
theorem map_root_eq_of_physicalScene_weak_tendsto
    (Pn : ℕ → ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
    (Q : ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
    (Ln : ℕ → ProbabilityMeasure (ι → ℝ)) (L : ProbabilityMeasure (ι → ℝ))
    (hPn : Tendsto Pn atTop (𝓝 Q)) (hLn : Tendsto Ln atTop (𝓝 L))
    (hmap : ∀ n, (Pn n).map (f := Prod.fst) measurable_fst.aemeasurable = Ln n) :
    Q.map (f := Prod.fst) measurable_fst.aemeasurable = L := by
  have hm := ((ProbabilityMeasure.continuous_map
    (show Continuous (Prod.fst : ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)) → (ι → ℝ))
        from continuous_fst)).tendsto Q).comp hPn
  simp_rw [Function.comp_def, hmap] at hm
  exact tendsto_nhds_unique hm hLn

/-- Both original weak-limit stages preserve the same root marginal. -/
theorem map_root_eq_of_iterated_physicalScene_weak_tendsto
    (Pn : ℕ → ℕ → ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
    (Q : ℕ → ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
    (R : ProbabilityMeasure ((ι → ℝ) ×
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
    (Ln : ℕ → ProbabilityMeasure (ι → ℝ)) (L : ProbabilityMeasure (ι → ℝ))
    (hLn : Tendsto Ln atTop (𝓝 L))
    (hmap : ∀ ℓ n, (Pn ℓ n).map (f := Prod.fst) measurable_fst.aemeasurable = Ln n)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ) (_hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R)) :
    (∀ ℓ, (Q ℓ).map (f := Prod.fst) measurable_fst.aemeasurable = L) ∧
      R.map (f := Prod.fst) measurable_fst.aemeasurable = L := by
  have hQ (ℓ : ℕ) : (Q ℓ).map (f := Prod.fst) measurable_fst.aemeasurable = L :=
    map_root_eq_of_physicalScene_weak_tendsto base
      (fun n ↦ Pn ℓ (φ ℓ n)) (Q ℓ) (fun n ↦ Ln (φ ℓ n)) L
      (hinner ℓ) (hLn.comp (hφ ℓ)) (fun n ↦ hmap ℓ (φ ℓ n))
  refine ⟨hQ, ?_⟩
  exact map_root_eq_of_physicalScene_weak_tendsto base
    (fun ℓ ↦ Q (ψ ℓ)) R (fun _ ↦ L) L houter tendsto_const_nhds (fun ℓ ↦ hQ (ψ ℓ))

end OTSelector.Reconstruction
