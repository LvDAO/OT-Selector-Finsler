import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalTaylorRetained
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedWeightedCoreWitness

/-!
# Original retained Taylor cycles vanish after the two separate weak stages

The retained pair uses the same original allocation experiment. Its original
Taylor packing budget contains no discarded population error, so its fixed
positive-margin witness vanishes after the sample limit and then the tilt limit.
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


local instance originalTaylorRetainedLimitStandardBorel :
    StandardBorelSpace ((D.coreSpatialCoordinateSpace i) × ℝ) := inferInstance
local instance originalTaylorRetainedLimitConfigTopology :
    TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance originalTaylorRetainedLimitConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace (base := base)
local instance originalTaylorRetainedLimitConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace (base := base)
local instance originalTaylorRetainedLimitPlanPolish : PolishSpace
    (LocalFiniteMeasure (((D.coreSpatialCoordinateSpace i) × ℝ) ×
      ((D.coreSpatialCoordinateSpace i) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

local notation "MacroScene" => (D.coreSpatialCoordinateSpace i) ×
  (CavityLocalScene ((D.coreSpatialCoordinateSpace i) × ℝ)
    ((D.coreSpatialCoordinateSpace i) × ℝ) × LocalConfiguration base)

local notation "JointScene" => MacroScene ×
  (CavityLocalScene ((D.coreSpatialCoordinateSpace i) × ℝ)
    ((D.coreSpatialCoordinateSpace i) × ℝ) ×
   CavityLocalScene ((D.coreSpatialCoordinateSpace i) × ℝ)
    ((D.coreSpatialCoordinateSpace i) × ℝ))

/-- Original retained packing, with its physical gap and event inclusion already
produced by the original Taylor core, yields zero witness on the actual joint
outer scene. The sample and tilt subsequences remain separate. -/
theorem OriginalFixedSeedMacroRetainedRectangleBudget.ae_zero_of_iterated_actual_scene
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (nearRadius threshold ε phaseSize : ℝ) (hε : 0 < ε)
    (Emacro : Set (D.coreSpatialCoordinateSpace i)) (hEmacro : IsOpen Emacro)
    (A₀ A₁ B₀ B₁ : Set ((D.coreSpatialCoordinateSpace i) × ℝ))
    (hA₀ : IsOpen A₀) (hA₁ : IsOpen A₁) (hB₀ : IsOpen B₀) (hB₁ : IsOpen B₁)
    (hbudget : D.OriginalFixedSeedMacroRetainedRectangleBudget i base hF hcomplete hu ha hinj
      A B hA hB nearRadius threshold ε phaseSize Emacro A₀ A₁ B₀ B₁)
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
    (rootDomain : ℕ → Set (D.coreSpatialCoordinateSpace i))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex
    let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
      (D.retainedNearCarrierEvent A B nearRadius)
      (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (scale n))
      (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (scale n))
      u (by
        let _inst : MetricSpace M := F.metricSpace
        exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (Rlaw : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) →
      ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 Rlaw) →
      ∀ᵐ s ∂(Rlaw : Measure JointScene),
        physicalSceneMaskedRetainedAverageWitness base Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s = 0 := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro Q Rlaw φ hφ ψ hψ hinner houter
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex
  let laws := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
      (D.retainedNearCarrierEvent A B nearRadius)
      (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
    (physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (scale n))
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (scale n))
    u hu.continuous.measurable (scale n) (rootDomain n) (hrootDomain n)
  have htilt : Tendsto (fun ℓ ↦ ENNReal.ofReal (t ℓ * G) *
      ENNReal.ofReal phaseSize ^ Fintype.card
        (Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)))
      atTop (𝓝 0) := by
    have htg : Tendsto (fun ℓ ↦ ENNReal.ofReal (t ℓ * G)) atTop (𝓝 0) := by
      simpa only [zero_mul, ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 * (G : ℝ))).comp (ht0.mul_const (G : ℝ))
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const htg
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  apply ae_eq_zero_of_iterated_weak_lsc_weighted_core_accuracy_bounds
    laws Q Rlaw φ hφ ψ hψ hinner houter
    (physicalSceneMaskedRetainedAverageWitness base Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁))
    (lowerSemicontinuous_physicalSceneMaskedRetainedAverageWitness base hEmacro
      (hA₀.prod hB₀) (hA₁.prod hB₁))
    (fun _ ↦ 0) tendsto_const_nhds (fun _ ↦ ENNReal.ofReal ε)
    (fun _ ↦ (ENNReal.ofReal_pos.mpr hε).ne') (fun _ ↦ ENNReal.ofReal_ne_top)
  intro _accuracy
  refine ⟨_, htilt, Eventually.of_forall fun ℓ ↦ ?_⟩
  filter_upwards [hscale.eventually_ge_atTop threshold] with n hn
  have hb := hbudget n (scale n) hn probe hprobe G hprobeBound (t ℓ) (ht ℓ)
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (hp ℓ n) (hm ℓ n)
    (rootDomain n) (hrootDomain n)
  simpa only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_zero, add_zero] using hb

end PopulationLocalPressureCore
end OTSelector.Reconstruction
