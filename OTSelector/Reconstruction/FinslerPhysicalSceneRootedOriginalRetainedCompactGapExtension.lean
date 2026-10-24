import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalFullClockCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLossExpectation
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedReadoutAgreementLoss

/-!
# Original retained compact readout gaps over prescribed full limits

The original allocation families supply a masked extension with both refined
weak stages exposed. Original global energy bounds its expected lost mass;
full-plan agreement on the unchanged full projection controls retained compact
readout gaps, also with bounded macroscopic tag weights.
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

local instance originalRetainedCompactGapStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalRetainedCompactGapConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalRetainedCompactGapConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalRetainedCompactGapConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalRetainedCompactGapPlanPolish {ι : Type*} [Fintype ι] :
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

/-- The actual fixed-core extension keeps the two original weak stages and
bounds retained compact readout gaps by the original population loss. -/
theorem exists_original_retained_compact_gap_extension
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
    (gap nearRadius : ℝ) (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hnearRadius : 0 < nearRadius)
    (hwindow : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
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
    (rootCarrier : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootCarrier : IsCompact rootCarrier)
    (hrootIn : ∀ n z, z ∈ rootDomain n → physicalSceneMacroscopicRoot (scale n) z ∈ rootCarrier)
    (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hU : IsOpen U) (hUf : volume U ≠ ⊤)

    (χ : C_c(Edge, ℝ)) (hχU : tsupport χ ⊆ {e : Edge | e.1.1 ∈ U}) :
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
    let maskedLaws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
      actualAllocationRootedMaskedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ
        (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
        (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
        H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        (D.retainedNearCarrierEvent A B nearRadius)
        (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
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
      (∀ᵐ s ∂(Rfull : Measure MacroScene),
        (s.2.1.1 : Measure Edge) = (s.2.1.2 : Measure Edge)) →
      ∃ Qaux : ℕ → ProbabilityMeasure JointScene, ∃ θ : ℕ → ℕ → ℕ,
        (∀ ℓ, StrictMono (θ ℓ) ∧ StrictMono (fun n ↦ φ ℓ (θ ℓ n)) ∧
          Tendsto (fun n ↦ maskedLaws ℓ (φ ℓ (θ ℓ n))) atTop (𝓝 (Qaux ℓ)) ∧
          (Qaux ℓ).map (f := Prod.fst) measurable_fst.aemeasurable = Qfull ℓ ∧
          ∀ᵐ s ∂(Qaux ℓ : Measure JointScene),
            s ∈ physicalSceneMaskedDecompositionCarrier base) ∧
        ∃ Raux : ProbabilityMeasure JointScene, ∃ η : ℕ → ℕ,
          StrictMono η ∧ StrictMono (fun ℓ ↦ ψ (η ℓ)) ∧
          Tendsto (fun ℓ ↦ Qaux (ψ (η ℓ))) atTop (𝓝 Raux) ∧
          Raux.map (f := Prod.fst) measurable_fst.aemeasurable = Rfull ∧
          (∀ᵐ s ∂(Raux : Measure JointScene),
            s ∈ physicalSceneMaskedDecompositionCarrier base) ∧
          (∫⁻ s, physicalSceneMaskedLostSourceMass base U s ∂(Raux : Measure JointScene)) ≤
            volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
              ν (⋃ i, D.physicalCoreDomain i)ᶜ) ∧
          (∫⁻ s, ENNReal.ofReal |LocalFiniteMeasure.testIntegral s.2.1.1 χ -
            LocalFiniteMeasure.testIntegral s.2.1.2 χ| ∂(Raux : Measure JointScene)) ≤
            ENNReal.ofReal (2 * ‖χ.toBoundedContinuousFunction‖) *
              (volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
                ν (⋃ i, D.physicalCoreDomain i)ᶜ)) ∧
          ∀ tag : BoundedContinuousFunction (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ℝ,
            (∫⁻ s, ENNReal.ofReal |tag s.1.1 *
              (LocalFiniteMeasure.testIntegral s.2.1.1 χ -
                LocalFiniteMeasure.testIntegral s.2.1.2 χ)| ∂(Raux : Measure JointScene)) ≤
              ENNReal.ofReal (2 * ‖tag‖ * ‖χ.toBoundedContinuousFunction‖) *
                (volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
                  ν (⋃ i, D.physicalCoreDomain i)ᶜ)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  dsimp only
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  intro Qfull Rfull φ hφ ψ hψ hinner houter hfull
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
  have hlost := (D.lintegral_lostSourceMass_le_of_original_retainedNear_iterated base
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hnearRadius hwindow
    scale hscalePos hscale ap am hpm hmm hfp hfm Energy hEnergy hEp hEm
    (fun _ ↦ H) (fun _ ↦ hH) coord hcoord rootDomain hrootDomain U hU hUf
    Q Raux (fun ℓ n ↦ φ ℓ (θ ℓ n)) (fun ℓ ↦ (hQ ℓ).2.1.tendsto_atTop)
    (fun ℓ ↦ ψ (η ℓ)) (fun ℓ ↦ (hQ ℓ).2.2.1) hR).2
  have hgapBound :=
    lintegral_retained_compact_difference_le_lost_of_projected_full_agreement
      base Rfull Raux hRmap hdecomp hfull χ U hU.measurableSet hχU
  refine ⟨Q, θ, hQ, Raux, η, hη, hψη, hR, hRmap, hdecomp, hlost,
    hgapBound.trans (mul_le_mul_right hlost _), ?_⟩
  intro tag
  exact (lintegral_tagged_retained_compact_difference_le_lost_of_projected_full_agreement
    base Rfull Raux hRmap hdecomp hfull tag χ U hU.measurableSet hχU).trans
      (mul_le_mul_right hlost _)

end PopulationLocalPressureCore
end OTSelector.Reconstruction
