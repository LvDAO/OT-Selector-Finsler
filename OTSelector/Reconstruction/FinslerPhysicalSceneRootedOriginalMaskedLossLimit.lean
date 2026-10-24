import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLoss
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
local instance originalMaskedLossLimitStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalMaskedLossLimitConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance originalMaskedLossLimitConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalMaskedLossLimitConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalMaskedLossLimitPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Original true energy removes the sample error at fixed tilt, leaving
only the original union population loss after the outer tilt weak limit. -/
theorem measure_lostSourceMass_gt_le_of_original_retainedNear_iterated
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
    (hwindow : ∀ j, ((D.haar.continuous.coefficient j).window.val.2.2 : ℝ) ≤ gap / 2)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j))
    (hfp : ∀ ℓ n, ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ w.2 (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ w.2 (am ℓ n w))
    (Energy : ℝ≥0∞) (hEnergy : Energy ≠ ⊤)
    (hEp : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (hEm : ∀ ℓ n,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy)
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (rootDomain : ℕ → Set (ι → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : volume U ≠ ⊤) :
    let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      (H n) (hH n) (D.retainedNearCarrierEvent A B nearRadius)
      (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
      (coord n) (hcoord n) u (by
        let _inst : MetricSpace M := F.metricSpace
        exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (Rlaw : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) →
      ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 Rlaw) →
      ∀ level : ℝ≥0∞, 0 < level → level ≠ ⊤ →
        (Rlaw : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base U s} ≤
          (volume U * (μ (⋃ j, D.physicalCoreDomain j)ᶜ +
            ν (⋃ j, D.physicalCoreDomain j)ᶜ)) / level := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro Q Rlaw φ hφ ψ hψ hinner houter level hl0 hlt
  let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (H n) (hH n) (D.retainedNearCarrierEvent A B nearRadius)
    (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
    (coord n) (hcoord n) u (by
      let _inst : MetricSpace M := F.metricSpace
      exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
  obtain ⟨c, hc, hb⟩ := D.exists_original_retainedNear_joint_lost_budget base
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hnearRadius hwindow
  have hscale2 : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp hscale
  have hden : Tendsto (fun n ↦ ENNReal.ofReal (scale n ^ 2 * c)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr (hscale2.atTop_mul_const hc)
  have hsample : Tendsto (fun n ↦ Energy / ENNReal.ofReal (scale n ^ 2 * c))
      atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using ENNReal.Tendsto.div tendsto_const_nhds
      (Or.inr (by simp)) hden (Or.inr hEnergy)
  apply measure_lostSourceMass_gt_le_of_iterated_masked_scene base laws Q Rlaw
    φ hφ ψ hψ hinner houter U hU hUf
    (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ)
    _ hsample ?_ level hl0 hlt
  intro ℓ
  apply Eventually.of_forall
  intro n
  exact hb n (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (hfp ℓ n) (hfm ℓ n)
    (scale n) (hscalePos n) Energy (hEp ℓ n) (hEm ℓ n)
    (H n) (hH n) (coord n) (hcoord n) (scale n) (rootDomain n) (hrootDomain n) U hU hUf

end PopulationLocalPressureCore
end OTSelector.Reconstruction
