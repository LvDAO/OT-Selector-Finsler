import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalFullClockCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedTaggedCompactReadout
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLoss
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedCompactClipping

/-!
# Original finite full tagged compact readouts have actual clipping budgets

A masked weak extension supplies the bounded retained readout at a fixed
original core. The same finite full law is its exact projection. Original
population loss and true global slack energy control the clipping error.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module TopologicalSpace OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

local instance originalFullClippingBudgetStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFullClippingBudgetConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalFullClippingBudgetConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFullClippingBudgetConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFullClippingBudgetPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

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

variable (j : ℕ)
set_option quotPrecheck false
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- Original globally feasible allocations and true energy produce the finite
full clipping budget internally on the unchanged original full scene laws. -/
theorem exists_original_full_tagged_compact_clipping_budget_of_iterated
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ i, (κ i).IsAddHaarMeasure]
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (gap nearRadius : ℝ) (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hnearRadius : 0 < nearRadius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (_hscale : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (n : ℝ) + 1)
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 k))
    (hfp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (ap ℓ n w))
    (hfm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsSemidiscreteAllocation μ w.2 (am ℓ n w))
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1))
    (Energy : ℝ≥0∞) (_hEnergy : Energy ≠ ⊤)
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
    (rootCarrier : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootCarrier : IsCompact rootCarrier)
    (hrootIn : ∀ n z, z ∈ rootDomain n → physicalSceneMacroscopicRoot (scale n) z ∈ rootCarrier)
    (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hU : IsOpen U) (hUf : volume U ≠ ⊤)
    (χ : C_c(Edge, ℝ)) (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U})
    (tag : BoundedContinuousFunction (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ℝ)
 :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
    let laws : ℕ → ℕ → ProbabilityMeasure MacroScene := fun ℓ n ↦
      actualAllocationRootedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
        (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
        (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
        H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n))
        (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
        u (by
          let _inst : MetricSpace M := F.metricSpace
          exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Qfull : ℕ → ProbabilityMeasure MacroScene) (Rfull : ProbabilityMeasure MacroScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, StrictMono (φ ℓ)) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Qfull ℓ))) →
      Tendsto (fun ℓ ↦ Qfull (ψ ℓ)) atTop (𝓝 Rfull) →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ c : ℝ, 0 < c ∧ ∀ ℓ n (plus : Bool),
        (∫⁻ s, ENNReal.ofReal |physicalSceneFullTaggedCompactReadout base χ plus tag s -
          continuousReadoutClip K (physicalSceneFullTaggedCompactReadout base χ plus tag) s|
          ∂(laws ℓ n : Measure MacroScene)) ≤
          ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
            (volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
              ν (⋃ i, D.physicalCoreDomain i)ᶜ +
              Energy / ENNReal.ofReal (scale n ^ 2 * c))) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  dsimp only
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  intro Qfull Rfull φ hφ ψ hψ hinner houter
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  have hEgood : MeasurableSet Egood :=
    D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n)
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  obtain ⟨Q, θ, hQ, Raux, η, hη, hψη, hR, hRmap, hdecomp⟩ :=
    exists_iterated_actualAllocationRootedMaskedScene_decomposition_over_given_full_limits
      base id Penv μ ap am hpm hmm (fun _ w ↦ w.1)
      (fun _ k ↦ (measurable_pi_apply k).comp measurable_fst) (fun _ w ↦ w.2)
      hfp hfm (fun _ ↦ H) (fun _ ↦ hH) Egood hEgood coord hcoord
      u hu.continuous.measurable scale rootDomain hrootDomain rootCarrier hrootCarrier hrootIn
      Qfull Rfull φ hφ ψ hψ hinner houter
  obtain ⟨K₀, hK₀, hretData⟩ :=
    D.exists_original_retained_tagged_compact_readout_convergence_of_iterated j base
      hF hcomplete hu ha hinj U hU hUf χ hχU 1 one_ne_zero ENNReal.one_ne_top
      id Penv ap am hpm hmm (fun _ w ↦ w.1)
      (fun _ k ↦ (measurable_pi_apply k).comp measurable_fst) (fun _ w ↦ w.2)
      hfp hfm A B hA hB nearRadius scale hscalePos hnormalization rootDomain hrootDomain
  have hret := hretData Q Raux (fun ℓ n ↦ φ ℓ (θ ℓ n))
    (fun ℓ ↦ (hQ ℓ).2.1.tendsto_atTop) (fun ℓ ↦ ψ (η ℓ))
    (fun ℓ ↦ (hQ ℓ).2.2.1) hR tag
  obtain ⟨c, hc, hlostBudget⟩ := D.exists_original_retainedNear_joint_lost_budget base
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hnearRadius hwindow
  let K := ‖tag‖ * K₀
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) hK₀
  refine ⟨K, hK, c, hc, ?_⟩
  intro ℓ n plus
  let maskedLaw := actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
    H hH Egood hEgood (coord n) (hcoord n) u hu.continuous.measurable
    (scale n) (rootDomain n) (hrootDomain n)
  have hfiniteDecomp : ∀ᵐ s ∂(maskedLaw : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base :=
    ae_physicalSceneRootedMaskedMacroscopicSceneLaw_decomposition base (Penv n)
      (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1))
      (physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1))
      (measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hpm ℓ n) _
        (fun k ↦ (measurable_pi_apply k).comp measurable_fst))
      (measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hmm ℓ n) _
        (fun k ↦ (measurable_pi_apply k).comp measurable_fst))
      H hH Egood hEgood (coord n) (hcoord n) u hu.continuous.measurable (scale n)
      (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
      (rootDomain n) (hrootDomain n)
  have hretBound : ∀ᵐ s ∂(maskedLaw : Measure JointScene),
      |physicalSceneRetainedTaggedCompactReadout base χ plus tag s| ≤ K := hret.1 ℓ n plus
  have hmasked := lintegral_full_tagged_compact_clipping_error_le_lost base
    (maskedLaw : Measure JointScene) hfiniteDecomp χ plus tag U hU.measurableSet hχU K hretBound
  have hlost := hlostBudget n (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (hfp ℓ n) (hfm ℓ n) (scale n) (hscalePos n) Energy (hEp ℓ n) (hEm ℓ n)
    H hH (coord n) (hcoord n) (scale n) (rootDomain n) (hrootDomain n) U hU hUf
  have hmap := map_actualAllocationRootedMaskedMacroscopicSceneLaw_full base (Penv n) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
    (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
    H hH Egood hEgood (coord n) (hcoord n) u hu.continuous.measurable
    (scale n) (rootDomain n) (hrootDomain n)
  have hreadout := continuous_physicalSceneFullTaggedCompactReadout base χ plus tag
  have herrorMeas : Measurable (fun s : MacroScene ↦ ENNReal.ofReal
      |physicalSceneFullTaggedCompactReadout base χ plus tag s -
        continuousReadoutClip K (physicalSceneFullTaggedCompactReadout base χ plus tag) s|) :=
    (hreadout.sub (continuous_continuousReadoutClip K hreadout)).abs.measurable.ennreal_ofReal
  calc
    _ = ∫⁻ s, ENNReal.ofReal |physicalSceneFullTaggedCompactReadout base χ plus tag s.1 -
        continuousReadoutClip K (physicalSceneFullTaggedCompactReadout base χ plus tag) s.1|
        ∂(maskedLaw : Measure JointScene) := by
      rw [← hmap, ProbabilityMeasure.toMeasure_map]
      exact lintegral_map herrorMeas measurable_fst
    _ ≤ _ := hmasked.trans (mul_le_mul_right hlost _)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
