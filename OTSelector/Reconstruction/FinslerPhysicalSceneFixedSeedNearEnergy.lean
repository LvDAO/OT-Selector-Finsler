import OTSelector.Reconstruction.FinslerPhysicalSceneFixedSeed
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetDisplacement

/-!
# Auxiliary near-energy tails in one fixed original seed scene

The source set and coordinates stay fixed while the auxiliary finite core is
chosen for estimates. Same-seed coordinates agree exactly; other-seed near
events vanish under the fixed source restriction. One auxiliary coefficient and
radius therefore control both window tails for every retained near piece.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] {μ ν : Measure M}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞} [∀ j, SigmaFinite (κ j)]

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- In one fixed original seed frame, every auxiliary near event has both
window tails controlled by the same original global energy. Near events of any
other seed are empty after the fixed physical source restriction. -/
theorem exists_uniform_fixed_seed_near_expected_tails :
    ∃ q > 0, ∃ radius > 0,
      ∀ (j : ℕ) (i : Fin D.haar.continuous.count) (Ω : Type*) [MeasurableSpace Ω]
        (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)]
        (spatialScale N : ℝ), 0 < N →
        ∀ (rootDomain U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)),
        MeasurableSet U → volume U ≠ ⊤ →
        ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ →
        ∀ C : ℝ≥0∞,
        (∫⁻ env, ∫⁻ p, ENNReal.ofReal
          (spatialScale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
          ∂Γ env ∂Penv) ≤ C →
        let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
        let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j spatialScale
        ((∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
          ((Γ env).restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)))
          coord u N z (physicalSceneLongEdgeWindow U threshold)
          ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
          (volume U * (C / ENNReal.ofReal q)) / threshold) ∧
        ((∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
          ((Γ env).restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)))
          coord u N z (physicalSceneTargetLongEdgeWindow U threshold)
          ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
          (volume U * (C / ENNReal.ofReal q)) / threshold) := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨q, hq, radius, hradius, hb⟩ :=
    D.exists_uniform_rooted_nearDisplacement_both_expected_tails hF hcomplete hu ha hinj
  refine ⟨q, hq, radius, hradius, ?_⟩
  intro j i Ω _ Penv Γ _ spatialScale N hN rootDomain U hU hUf threshold ht0 htt C henergy
  dsimp only
  by_cases hs : (D.haar.continuous.coefficient i).seedIndex = j
  · subst j
    exact hb i Ω Penv Γ _
      (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _) spatialScale N hN
      rootDomain U hU hUf threshold ht0 htt C henergy
  · have he : D.nearDisplacementEvent i radius ∩
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ
          (univ : Set M)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hs ((D.nearDisplacement_source_mem_fixed_seed_iff i j hp.1).mp hp.2.1)
    simp [he, physicalSceneRootedPlan]

end PopulationLocalPressureCore
end OTSelector.Reconstruction
