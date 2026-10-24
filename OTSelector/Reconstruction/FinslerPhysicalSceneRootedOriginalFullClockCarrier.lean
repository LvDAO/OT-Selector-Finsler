import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClosedClockCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedProjectedCarrierAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalClockScreenAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLossLimit

/-!
# Original accuracy cores carry the SAME full scene in closed calibration windows

Actual original allocation families provide retained/lost extensions over prescribed
sample and tilt limits. Closed original clock carriers and vanishing original
population loss yield one countable Borel carrier on the unchanged full limit.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

local instance originalFullClockCarrierStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalFullClockCarrierConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalFullClockCarrierConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalFullClockCarrierConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalFullClockCarrierPlanPolish {ι : Type*} [Fintype ι] :
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

/-- Actual two-stage extensions retain the literal original closed-clock carrier. -/
theorem exists_original_retained_closedClockCarrier_extension
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
      ∃ Raux : ProbabilityMeasure JointScene,
        Raux.map (f := Prod.fst) measurable_fst.aemeasurable = Rfull ∧
        (∀ᵐ s ∂(Raux : Measure JointScene), s ∈ physicalSceneMaskedDecompositionCarrier base) ∧
        (∀ᵐ s ∂(Raux : Measure JointScene),
          ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
            (s.1, e) ∈ D.originalClosedClockCarrier j base) ∧
        ∀ level : ℝ≥0∞, 0 < level → level ≠ ⊤ →
          (Raux : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base U s} ≤
            (volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
              ν (⋃ i, D.physicalCoreDomain i)ᶜ)) / level := by
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
  have hret := D.ae_original_retained_average_closed_clock_carrier_of_iterated j base
    hF hcomplete hu ha hinj A B hA hB nearRadius Penv ap am hpm hmm
    (fun _ w ↦ w.1) (fun _ k ↦ (measurable_pi_apply k).comp measurable_fst)
    scale hscalePos hscale rootDomain hrootDomain
    Q Raux (fun ℓ n ↦ φ ℓ (θ ℓ n))
    (fun ℓ ↦ (hQ ℓ).2.1.tendsto_atTop) (fun ℓ ↦ ψ (η ℓ))
    (fun ℓ ↦ (hQ ℓ).2.2.1) hR
  refine ⟨Raux, hRmap, hdecomp, hret.2, ?_⟩
  exact D.measure_lostSourceMass_gt_le_of_original_retainedNear_iterated base
    hF hcomplete hu ha hinj horder hA hB hμA hνB hgap hdist hnearRadius hwindow
    scale hscalePos hscale ap am hpm hmm hfp hfm Energy hEnergy hEp hEm
    (fun _ ↦ H) (fun _ ↦ hH) coord hcoord rootDomain hrootDomain U hU hUf
    Q Raux (fun ℓ n ↦ φ ℓ (θ ℓ n)) (fun ℓ ↦ (hQ ℓ).2.1.tendsto_atTop)
    (fun ℓ ↦ ψ (η ℓ)) hψη.tendsto_atTop (fun ℓ ↦ (hQ ℓ).2.2.1) hR

end PopulationLocalPressureCore

variable (j : ℕ)
set_option quotPrecheck false
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The original face builds countably many literal closed-clock carriers carrying the SAME full law. -/
theorem ae_original_full_closedClockCarrier_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ i, (κ i).IsAddHaarMeasure)
    (hbalance : μ.map a = ν.map a)
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (nearRadius : ℝ) (hnearRadius : 0 < nearRadius)
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
 :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
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
      ∃ Dseq : (m : ℕ) → PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
          (fun z ↦ ∃ π : Measure (ℝ × ℝ),
            Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) ∧
              ∀ᵐ p ∂π, p.1 ≤ p.2) r
          (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹,
      ∃ Γ : Set (MacroScene × Edge),
        Γ = ⋃ m : ℕ, (Dseq m).originalClosedClockCarrier j base ∧
        MeasurableSet Γ ∧
        ∀ᵐ s ∂(Rfull : Measure MacroScene),
          ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), (s, e) ∈ Γ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws Qfull Rfull φ hφ ψ hψ hinner houter
  have hμAs : ∀ᵐ x ∂μ, x ∈ A := hμA
  have hνBs : ∀ᵐ y ∂ν, y ∈ B := hνB
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hA hB hAB
  obtain ⟨Dseq, hscreen, _hμtail, _hνtail, hpopulation⟩ :=
    exists_original_small_clock_screen_core_sequence_of_face hcore hrecovery hF hcomplete hu ha hinj
      hκ hbalance hA hB hμAs hνBs hνreg hμreg hface (by positivity : 0 < gap / 2)
  let Γ : Set (MacroScene × Edge) := ⋃ m : ℕ, (Dseq m).originalClosedClockCarrier j base
  have hΓ : MeasurableSet Γ :=
    MeasurableSet.iUnion fun m ↦ (Dseq m).measurableSet_originalClosedClockCarrier j base
  refine ⟨Dseq, Γ, rfl, hΓ, ?_⟩
  have hlocal (U : Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
      (hU : IsOpen U) (hUf : volume U ≠ ⊤) :
      ∀ᵐ s ∂(Rfull : Measure MacroScene),
        ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
          e.1.1 ∈ U → (s, e) ∈ Γ := by
    have hext (m : ℕ) := (Dseq m).exists_original_retained_closedClockCarrier_extension j base
      hF hcomplete hu ha hinj horder hA.measurableSet hB.measurableSet hμA hνB
      gap nearRadius hgap hdist hnearRadius (hscreen m) scale hscalePos hscale
      ap am hpm hmm hfp hfm rootDomain hrootDomain Energy hEnergy hEp hEm
      rootCarrier hrootCarrier hrootIn U hU hUf Qfull Rfull φ hφ ψ hψ hinner houter
    choose Raux hprojection hdecomposition hretained hlost using hext
    have hretainedUnion (m : ℕ) : ∀ᵐ s ∂(Raux m : Measure JointScene),
        ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), (s.1, e) ∈ Γ :=
      (hretained m).mono fun _ hs ↦ hs.mono fun _ he ↦ mem_iUnion_of_mem m he
    have hloss : Tendsto (fun m ↦ volume U *
        (μ (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ +
          ν (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hpopulation (Or.inr hUf)
    exact ae_full_carried_on_source_window_of_actual_projected_carrier_accuracy base
      Rfull Raux hprojection Γ hΓ U hU.measurableSet hdecomposition hretainedUnion
      (fun m ↦ volume U * (μ (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ +
        ν (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ)) hloss hlost
  have hballs (k : ℕ) := hlocal (Metric.ball 0 ((k : ℝ) + 1)) Metric.isOpen_ball
    (ne_top_of_le_ne_top
      (isCompact_closedBall (0 : Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)
        ((k : ℝ) + 1)).measure_ne_top (measure_mono Metric.ball_subset_closedBall))
  filter_upwards [ae_all_iff.mpr hballs] with s hs
  filter_upwards [ae_all_iff.mpr hs] with e he
  obtain ⟨k, hk⟩ := exists_nat_gt ‖e.1.1‖
  apply he k
  change dist e.1.1 0 < (k : ℝ) + 1
  rw [dist_zero_right]
  exact hk.trans (by linarith)

end OTSelector.Reconstruction
