import OTSelector.Reconstruction.FinslerPhysicalSceneRootedStrictClockExhaustion
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroRetainedSupport
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroTagRetained
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalTaylorRetainedLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedWeightedCoreWitness

/-!
# Actual retained support cycles at the original varying macroscopic coefficient

Original Taylor control and finite core isolation give local packing witnesses.
Both original weak stages and a countable macro basis put their consequences
on one probability-one event for the SAME actual joint scene. The resulting
cost depends on the actual macro tag and is independent of auxiliary core data.
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


local instance originalMacroRetainedStrictSupportStandardBorel :
    StandardBorelSpace ((D.coreSpatialCoordinateSpace i) × ℝ) := inferInstance
local instance originalMacroRetainedStrictSupportConfigTopology :
    TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance originalMacroRetainedStrictSupportConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace (base := base)
local instance originalMacroRetainedStrictSupportConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace (base := base)
local instance originalMacroRetainedStrictSupportPlanPolish : PolishSpace
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

/-- Countable rational clock bins and integral spatial radii remove the
bounded-box parameters from the actual original retained-support no-cycle
producer. One common AE event covers the whole strict original clock window. -/
theorem ae_original_macro_tag_retained_support_strictClock_twoCycle
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {Acompact A B : Set M}
    (hAcompact : IsCompact Acompact) (hμAcompact : ∀ᵐ x ∂μ, x ∈ Acompact)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAreg : A ⊆ F.potentialRegularDomain u) (hBreg : B ⊆ F.potentialRegularDomain u)
    (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobeBound : ∀ x y, |probe x y| ≤ G)
    (t : ℕ → ℝ) (ht0 : ∀ ℓ, 0 ≤ t ℓ) (ht0lim : Tendsto t atTop (𝓝 0))
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
        s.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a)
            (D.haar.continuous.coefficient i).seedIndex '' (D.haar.continuous.coefficient i).roots →
        IsTwoCycleMonotoneOn
          (physicalSceneOriginalMacroCost (P := P) (a := a)
            (D.haar.continuous.coefficient i).seedIndex s.1.1)
          (physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window)
          (((LocalFiniteMeasure.cavityAverage s.2.1 : Measure _).support) ∩
            physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window) := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro Q Rlaw φ hφ ψ hψ hinner houter
  let C := D.haar.continuous.coefficient i
  apply ae_tagged_strictClock_twoCycle_of_countable_bounded_boxes (Rlaw : Measure JointScene)
    (fun s ↦ s.1.1) (fun s ↦ (LocalFiniteMeasure.cavityAverage s.2.1 : Measure _))
    (physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex '' C.roots)
    (physicalSceneOriginalMacroCost (P := P) (a := a) C.seedIndex) C.window
  intro N sL sR tL tR hvalid
  have hh := D.ae_original_macro_tag_retained_support_twoCycle i base
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart hAcompact hμAcompact
    hA hB hAreg hBreg nearRadius (N : ℝ) sL sR tL tR hvalid.1 hvalid.2.1 hvalid.2.2
    scale hscale probe hprobe G hprobeBound t ht0 ht0lim ap am hpm hmm hp hm
    rootDomain hrootDomain Q Rlaw φ hφ ψ hψ hinner houter
  exact hh

end PopulationLocalPressureCore
end OTSelector.Reconstruction
