import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedLossLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedJoint
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonNearFullMass
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCoreCarrierInclusion

/-!
# Actual original retained-union losses on the unchanged joint scene

The original populations, physical support gap and true global energy produce
the discarded-pair source-window budget. The full original scene, its target
cloud and every realized restricted target column remain unchanged.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local instance originalMaskedLossStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalMaskedLossConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance originalMaskedLossConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalMaskedLossConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalMaskedLossPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- One original physical gap produces the actual discarded-pair budget before
sample size, global allocation families, physical scale and source windows are chosen. -/
theorem exists_original_retainedNear_joint_lost_budget
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    {gap nearRadius : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hnearRadius : 0 < nearRadius)
    (hwindow : ∀ j, ((D.haar.continuous.coefficient j).window.val.2.2 : ℝ) ≤ gap / 2) :
    ∃ c > 0, ∀ n : ℕ,
    ∀ ap am : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ,
    ∀ hpm : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap z.1 z.2 j),
    ∀ hmm : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am z.1 z.2 j),
      (∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap w)) →
      (∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am w)) →
    ∀ scale : ℝ, 0 < scale → ∀ Energy : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ ap (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy →
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ am (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy →
    ∀ H : Set M, ∀ hH : MeasurableSet H,
    ∀ coord : M → (ι → ℝ), ∀ hcoord : Measurable coord,
    ∀ macroScale : ℝ, ∀ rootDomain : Set (ι → ℝ),
    ∀ hrootDomain : volume rootDomain = ENNReal.ofReal ((n : ℝ) + 1),
    ∀ U : Set (ι → ℝ), IsOpen U → volume U ≠ ⊤ →
      (∫⁻ s, physicalSceneMaskedLostSourceMass base U s
        ∂(actualAllocationRootedMaskedMacroscopicSceneLaw base
          ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ ap am hpm hmm
          (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
          H hH (D.retainedNearCarrierEvent A B nearRadius)
          (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
          coord hcoord u (by
            let _inst : MetricSpace M := F.metricSpace
            exact hu.continuous.measurable) macroScale rootDomain hrootDomain : Measure JointScene)) ≤
        volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
          Energy / ENNReal.ofReal (scale ^ 2 * c)) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨c, hc, hb⟩ := D.exists_original_fullNonNear_mass_bound hF hcomplete hu ha hinj horder
    hA hB hμA hνB hgap hdist hnearRadius hwindow
  refine ⟨c, hc, ?_⟩
  intro n ap am hpm hmm hfp hfm scale hs Energy hEp hEm H hH coord hcoord
    macroScale rootDomain hrootDomain U hU hUf
  exact lintegral_physicalSceneRootedMaskedMacroscopicSceneLaw_lost_le base _ _ _
    (measurable_physicalSceneGlobalAllocationFamily μ ap hpm _
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst))
    (measurable_physicalSceneGlobalAllocationFamily μ am hmm _
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst))
    H hH (D.retainedNearCarrierEvent A B nearRadius)
    (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
    coord hcoord u hu.continuous.measurable macroScale _
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst) rootDomain hrootDomain U hU hUf _
    (hb n ap hpm hfp (scale ^ 2) (sq_pos_of_pos hs) Energy hEp)
    (hb n am hmm hfm (scale ^ 2) (sq_pos_of_pos hs) Energy hEm)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
