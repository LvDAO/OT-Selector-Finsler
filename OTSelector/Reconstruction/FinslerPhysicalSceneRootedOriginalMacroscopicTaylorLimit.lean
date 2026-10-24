import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroscopicTaylorWitness
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedLscDefect

/-!
# The original full physical cycle budget in the same iterated weak scene

The original true-energy error vanishes at each fixed tilt. The opposite tilt
then vanishes in the outer weak limit. Only the explicit original finite-union
population loss remains; the fixed core is never silently exhausted in N.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
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
  (i : Fin D.haar.continuous.count)
variable (base : ((D.coreSpatialCoordinateSpace i) × ℝ))


local instance originalTaylorLimitStandardBorel :
    StandardBorelSpace ((D.coreSpatialCoordinateSpace i) × ℝ) := inferInstance
local instance originalTaylorLimitConfigTopology :
    TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance originalTaylorLimitConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace (base := base)
local instance originalTaylorLimitConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace (base := base)
local instance originalTaylorLimitPlanPolish : PolishSpace
    (LocalFiniteMeasure (((D.coreSpatialCoordinateSpace i) × ℝ) ×
      ((D.coreSpatialCoordinateSpace i) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

local notation "MacroScene" => (D.coreSpatialCoordinateSpace i) ×
  (CavityLocalScene ((D.coreSpatialCoordinateSpace i) × ℝ)
    ((D.coreSpatialCoordinateSpace i) × ℝ) × LocalConfiguration base)

/-- The actual full physical rectangle budget controls the SAME outer scene's
positive-level witnesses. The original sample and tilt limits remove their own
errors separately, leaving exactly the fixed union population loss. -/
theorem OriginalFixedSeedMacroRectangleBudget.measure_level_le_of_iterated_actual_scene
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (c threshold R ε phaseSize : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (Emacro : Set (D.coreSpatialCoordinateSpace i)) (hEmacro : IsOpen Emacro)
    (A₀ A₁ B₀ B₁ : Set ((D.coreSpatialCoordinateSpace i) × ℝ))
    (hA₀ : IsOpen A₀) (hA₁ : IsOpen A₁) (hB₀ : IsOpen B₀) (hB₁ : IsOpen B₁)
    (hbudget : D.OriginalFixedSeedMacroRectangleBudget i base hF hcomplete hu ha hinj
      c threshold R ε phaseSize Emacro A₀ A₁ B₀ B₁)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobeBound : ∀ x y, |probe x y| ≤ G)
    (t : ℕ → ℝ) (ht : ∀ ℓ, 0 ≤ t ℓ) (ht0 : Tendsto t atTop (𝓝 0))
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j))
    (hp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            t ℓ * probe x (w.1 j)) (ap ℓ n w))
    (hm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            (-t ℓ) * probe x (w.1 j)) (am ℓ n w))
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
    (rootDomain : ℕ → Set (D.coreSpatialCoordinateSpace i))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex
    let laws := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (scale n))
      (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (scale n))
      u (by
        let _inst : MetricSpace M := F.metricSpace
        exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure MacroScene) (Rlaw : ProbabilityMeasure MacroScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) →
      ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 Rlaw) →
      ∀ level : ℝ≥0∞, 0 < level → level ≠ ⊤ →
        (Rlaw : Measure MacroScene) {s | level < physicalSceneMacroscopicAverageWitness base
          Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s} ≤
          (volume (Metric.closedBall (0 : D.coreSpatialCoordinateSpace i) (|R| + 1)) *
            (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ)) / level := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro Q Rlaw φ hφ ψ hψ hinner houter level hlevel hlevelt
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex
  let laws := fun ℓ n ↦ actualAllocationRootedMacroscopicSceneLaw base
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
    (physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (scale n))
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (scale n))
    u hu.continuous.measurable (scale n) (rootDomain n) (hrootDomain n)
  let V := volume (Metric.closedBall (0 : D.coreSpatialCoordinateSpace i) (|R| + 1))
  have hV : V ≠ ⊤ := (isCompact_closedBall (0 : D.coreSpatialCoordinateSpace i) (|R| + 1)).measure_ne_top
  have hscale2 : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp hscale
  have hden : Tendsto (fun n ↦ ENNReal.ofReal (scale n ^ 2 * c)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr (hscale2.atTop_mul_const hc)
  have hsample : Tendsto (fun n ↦ V * (Energy / ENNReal.ofReal (scale n ^ 2 * c)))
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n ↦ Energy / ENNReal.ofReal (scale n ^ 2 * c)) atTop (𝓝 0) := by
      simpa only [ENNReal.div_top] using ENNReal.Tendsto.div tendsto_const_nhds
        (Or.inr (by simp)) hden (Or.inr hEnergy)
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hdiv (Or.inr hV)
  have htilt : Tendsto (fun ℓ ↦ ENNReal.ofReal (t ℓ * G) *
      ENNReal.ofReal phaseSize ^ Fintype.card
        (Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)))
      atTop (𝓝 0) := by
    have htg : Tendsto (fun ℓ ↦ ENNReal.ofReal (t ℓ * G)) atTop (𝓝 0) := by
      simpa only [zero_mul, ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 * (G : ℝ))).comp (ht0.mul_const (G : ℝ))
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const htg
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  apply measure_lsc_gt_le_of_iterated_weak_weighted_sample_tilt_defect_bounds
    laws Q Rlaw φ hφ ψ hψ hinner houter
    (physicalSceneMacroscopicAverageWitness base Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁))
    (lowerSemicontinuous_physicalSceneMacroscopicAverageWitness base hEmacro
      (hA₀.prod hB₀) (hA₁.prod hB₁))
    (ENNReal.ofReal ε)
    (V * (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ))
    (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
    _ _ htilt hsample ?_ level hlevel hlevelt
  apply Eventually.of_forall
  intro ℓ
  filter_upwards [hscale.eventually_ge_atTop threshold] with n hn
  have hb := hbudget n (scale n) hn probe hprobe G hprobeBound (t ℓ) (ht ℓ)
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (hp ℓ n) (hm ℓ n)
    Energy (hEp ℓ n) (hEm ℓ n) (rootDomain n) (hrootDomain n)
  simpa only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_add] using hb

end PopulationLocalPressureCore
end OTSelector.Reconstruction
