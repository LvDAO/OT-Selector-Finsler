import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalEnergy
import OTSelector.Reconstruction.FinslerOriginalAtlasEnergyBudget

/-! Actual countable general Finsler seed pieces share the original iid
optimal plan's single energy budget. The original atlas potential is retained. -/
open Set Function MeasureTheory ProbabilityTheory Manifold
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]

/-- Original atlas source restrictions inherit one unchanged iid energy
constant. The cost is the actual intrinsic distance slack for that same atlas
potential, not a frozen coefficient or a substituted potential. -/
theorem tsum_finsler_originalIID_seedSourceEnergy_uniform
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (μ ν : Measure M) {C : ℝ}
    (henergy : PopulationUniformEnergyBound μ ν (Module.finrank ℝ E - 1)
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x) C)
    {n : ℕ} (hn : 0 < n) :
    (∑' j, ∫⁻ ξ, ∫⁻ p in physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ (univ : Set M),
      ENNReal.ofReal ((n : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂originalIIDOptimalPhysicalPlan
        (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x)
        ((n : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))) ξ
      ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))) ≤
      ENNReal.ofReal C := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  have hnonneg (x y : M) : 0 ≤ (F.lengthEDist x y).toReal - u y + u x := by
    have h := hu.le_add_mul y x
    simp only [NNReal.coe_one, one_mul, dist_comm y x] at h
    change 0 ≤ dist x y - u y + u x
    linarith
  have hm : Measurable (Function.uncurry
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x)) :=
    F.measurable_distance_slack hu
  exact tsum_originalIIDOptimalPhysicalPlan_sourceEnergy_uniform μ ν
    (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x) hm hnonneg henergy hn
    (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda))
    (fun j ↦ measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
    pairwiseDisjoint_physicalSceneOriginalSeedSource

end OTSelector.Reconstruction
