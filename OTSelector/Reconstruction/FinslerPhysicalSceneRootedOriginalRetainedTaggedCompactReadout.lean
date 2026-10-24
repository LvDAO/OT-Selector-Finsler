import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedCompactReadout

/-!
# Original retained compact expectations retain the actual macroscopic tag

The SAME original finite reference bounds every bounded continuous macro-tag
weight times a retained compact edge test. The product observable is continuous
and uniformly bounded on the actual laws, so its expectations pass both original
weak stages by clipping the product itself.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  TopologicalSpace OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

local instance retainedTaggedCompactReadoutStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance retainedTaggedCompactReadoutConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance retainedTaggedCompactReadoutConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance retainedTaggedCompactReadoutConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance retainedTaggedCompactReadoutPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

section TaggedReadout
variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local notation "Endpoint" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Endpoint × Endpoint)
local notation "PairScene" => CavityLocalScene Endpoint Endpoint
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The unchanged actual macro tag weights the selected retained compact edge readout. -/
def physicalSceneRetainedTaggedCompactReadout (χ : C_c(Edge, ℝ)) (plus : Bool)
    (tag : BoundedContinuousFunction (ι → ℝ) ℝ) (s : JointScene) : ℝ :=
  tag s.1.1 * physicalSceneRetainedCompactReadout base χ plus s

theorem continuous_physicalSceneRetainedTaggedCompactReadout
    (χ : C_c(Edge, ℝ)) (plus : Bool) (tag : BoundedContinuousFunction (ι → ℝ) ℝ) :
    Continuous (physicalSceneRetainedTaggedCompactReadout base χ plus tag) :=
  (tag.continuous.comp continuous_fst.fst).mul
    (continuous_physicalSceneRetainedCompactReadout base χ plus)

/-- The original reference bound controls the product observable at the actual tag. -/
theorem abs_physicalSceneRetainedTaggedCompactReadout_le
    (χ : C_c(Edge, ℝ)) (plus : Bool) (tag : BoundedContinuousFunction (ι → ℝ) ℝ)
    (s : JointScene) {K : ℝ}
    (hbound : |physicalSceneRetainedCompactReadout base χ plus s| ≤ K) :
    |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ ‖tag‖ * K := by
  rw [physicalSceneRetainedTaggedCompactReadout, abs_mul]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using tag.norm_coe_le_norm s.1.1)
    hbound (abs_nonneg _) (norm_nonneg _)
end TaggedReadout

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)



variable (j : ℕ)
set_option quotPrecheck false
local notation "V" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Edge" => (Point × Point)
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => V × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)
/-- Original global feasible families supply the SAME retained compact expectation bound
and both weak expectation limits for every bounded continuous original macro-tag weight. -/
theorem exists_original_retained_tagged_compact_readout_convergence_of_iterated
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, (κ j).IsAddHaarMeasure]
    (U : Set V) (hU : IsOpen U) (hUfinite : volume U ≠ ⊤)
    (χ : C_c(Edge, ℝ)) (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U})
    (error : ℝ≥0∞) (herror : error ≠ 0) (herrortop : error ≠ ⊤)
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 k))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M)
    (hY : ∀ n k, Measurable (fun w ↦ Y n w k))
    (weights : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation η₀ (weights n w) (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation η₀ (weights n w) (am ℓ n w))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B) (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (m n : ℝ) + 1)
    (rootDomain : ℕ → Set V)
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((m n : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
    let Egood := D.retainedNearCarrierEvent A B nearRadius
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
      actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) η₀
        (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
        H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        Egood (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
        (coord n) (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
        u (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)
        (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (R : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) →
      ∀ tag : BoundedContinuousFunction V ℝ,
      (∀ ℓ n plus, ∀ᵐ s ∂(laws ℓ n : Measure JointScene),
        |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ ‖tag‖ * K) ∧
      (∀ ℓ plus,
        (∀ᵐ s ∂(Q ℓ : Measure JointScene),
          |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ ‖tag‖ * K) ∧
        Tendsto (fun n ↦ ∫ s, physicalSceneRetainedTaggedCompactReadout base χ plus tag s
          ∂(laws ℓ (φ ℓ n) : Measure JointScene)) atTop
          (𝓝 (∫ s, physicalSceneRetainedTaggedCompactReadout base χ plus tag s
            ∂(Q ℓ : Measure JointScene)))) ∧
      ∀ plus,
        (∀ᵐ s ∂(R : Measure JointScene),
          |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ ‖tag‖ * K) ∧
        Tendsto (fun ℓ ↦ ∫ s, physicalSceneRetainedTaggedCompactReadout base χ plus tag s
          ∂(Q (ψ ℓ) : Measure JointScene)) atTop
          (𝓝 (∫ s, physicalSceneRetainedTaggedCompactReadout base χ plus tag s
            ∂(R : Measure JointScene))) := by
  obtain ⟨K, hK, hdata⟩ :=
    D.exists_original_retained_compact_readout_convergence_of_iterated j base
      hF hcomplete hu ha hinj U hU hUfinite χ hχU error herror herrortop
      m Penv ap am hpm hmm Y hY weights hfp hfm A B hA hB nearRadius
      scale hscale hnormalization rootDomain hrootDomain
  refine ⟨K, hK, ?_⟩
  dsimp only
  intro Q R φ hφ ψ hinner houter tag
  have hbase := hdata Q R φ hφ ψ hinner houter
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
    actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) η₀
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
      H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
      Egood (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
      (coord n) (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
      u (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)
      (scale n) (rootDomain n) (hrootDomain n)
  have hbound (ℓ n : ℕ) (plus : Bool) : ∀ᵐ s ∂(laws ℓ n : Measure JointScene),
      |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ ‖tag‖ * K :=
    (hbase.1 ℓ n plus).mono fun s hs ↦
      abs_physicalSceneRetainedTaggedCompactReadout_le base χ plus tag s hs
  have htagK : 0 ≤ ‖tag‖ * K := mul_nonneg (norm_nonneg _) hK
  have hinnerReadout (ℓ : ℕ) (plus : Bool) :=
    ae_bound_and_tendsto_integral_of_weak_uniform_bound (fun n ↦ laws ℓ (φ ℓ n))
      (Q ℓ) (hinner ℓ) (physicalSceneRetainedTaggedCompactReadout base χ plus tag)
      (continuous_physicalSceneRetainedTaggedCompactReadout base χ plus tag) (‖tag‖ * K) htagK
      (fun n ↦ hbound ℓ (φ ℓ n) plus)
  exact ⟨hbound, hinnerReadout, fun plus ↦
    ae_bound_and_tendsto_integral_of_weak_uniform_bound (fun ℓ ↦ Q (ψ ℓ)) R houter
      (physicalSceneRetainedTaggedCompactReadout base χ plus tag)
      (continuous_physicalSceneRetainedTaggedCompactReadout base χ plus tag) (‖tag‖ * K) htagK
      (fun ℓ ↦ (hinnerReadout (ψ ℓ) plus).1)⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
