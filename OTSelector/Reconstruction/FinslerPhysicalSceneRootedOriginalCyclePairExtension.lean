import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedCyclePairZero
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedMeasurableClockGap
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLossLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockCarrierConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalCoreConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRationalClockLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroRetainedStrictSupport

/-!
# An actual certified retained/lost extension of the same full original scene

Original global optimality, physical energy and clock densities produce the
retained no-cycle witness and positive full clock gap internally. The original
population complements are the only remaining lost-mass error, with exact full
projection and full = retained + lost preserved through both weak limits.
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

local instance originalCycleExtensionStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalCycleExtensionConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalCycleExtensionConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalCycleExtensionConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalCycleExtensionPlanPolish {ι : Type*} [Fintype ι] :
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

theorem exists_original_retained_cyclePair_zero_extension
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
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
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
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1))
    (hμlaw : PopulationConditionalWindowLaw P a κ lambda μ ρ₀ v)
    (hνlaw : PopulationConditionalWindowLaw P a κ lambda ν ρ₁ v)
    (physicalGap g margin : ℝ) (hmargin : 0 ≤ margin)
    (hscreenGap : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) < physicalGap / 2)
    (hscreenCycle : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ g)
    (K : Set Edge) (hK : MeasurableSet K)
    (hphysicalGap : 0 < physicalGap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, physicalGap ≤ dist x y)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hnearRadius : 0 < nearRadius)
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
    (hU : IsOpen U) (hUf : volume U ≠ ⊤) :
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
        (∀ᵐ s ∂(Raux : Measure JointScene), physicalSceneCyclePairMass
          (fun s : JointScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
          (physicalSceneStrictCyclePairEvent
            (fun s : JointScene ↦ physicalSceneOriginalMacroCost (P := P) (a := a) j s.1.1)
            (physicalSceneClockGapRegion g) K margin) s = 0) ∧
        ∀ level : ℝ≥0∞, 0 < level → level ≠ ⊤ →
          (Raux : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base U s} ≤
            (volume U * (μ (⋃ i, D.physicalCoreDomain i)ᶜ +
              ν (⋃ i, D.physicalCoreDomain i)ᶜ)) / level := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws Qfull Rfull φ hφ ψ hψ hinner houter
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  have hEgood : MeasurableSet Egood :=
    D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n)
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  have hfp ℓ n := (hp ℓ n).mono fun _ hw ↦ hw.1
  have hfm ℓ n := (hm ℓ n).mono fun _ hw ↦ hw.1
  obtain ⟨Q, θ, hQ, Raux, η, hη, hψη, hR, hRmap, hdecomp⟩ :=
    exists_iterated_actualAllocationRootedMaskedScene_decomposition_over_given_full_limits
      base id Penv μ ap am hpm hmm (fun _ w ↦ w.1)
      (fun _ k ↦ (measurable_pi_apply k).comp measurable_fst) (fun _ w ↦ w.2)
      hfp hfm (fun _ ↦ H) (fun _ ↦ hH) Egood hEgood coord hcoord
      u hu.continuous.measurable scale rootDomain hrootDomain rootCarrier hrootCarrier hrootIn
      Qfull Rfull φ hφ ψ hψ hinner houter
  have hμAs : ∀ᵐ x ∂μ, x ∈ A := by
    rw [ae_iff]
    exact hμA
  have hνBs : ∀ᵐ y ∂ν, y ∈ B := by
    rw [ae_iff]
    exact hνB
  have hgapAux := ae_iterated_original_iid_actualMaskedMacroscopicScene_full_average_clock_gap_of_measurable_support
    base id μ ν hA hB hphysicalGap hdist hμAs hνBs
    ap am hpm hmm hfp hfm (fun _ ↦ H) (fun _ ↦ hH)
    (fun _ _ ↦ Egood) (fun _ _ ↦ hEgood) coord hcoord hu scale hscalePos hscale
    rootDomain hrootDomain Energy hEnergy hEp hEm Q
    (fun ℓ n ↦ φ ℓ (θ ℓ n)) (fun ℓ ↦ (hQ ℓ).2.1)
    (fun ℓ ↦ (hQ ℓ).2.2.1) Raux (fun ℓ ↦ ψ (η ℓ)) hR
  have hret := D.ae_original_retained_cyclePairMass_zero_of_iterated j base
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart hAcompact hμAcompact
    hA hB hAreg hBreg nearRadius scale hscalePos hscale probe hprobe G hprobeBound
    t ht0 ht0lim ap am hpm hmm hp hm rootDomain hrootDomain hμlaw hνlaw
    (physicalGap / 2) g margin hmargin hscreenGap hscreenCycle K hK
    Q Raux (fun ℓ n ↦ φ ℓ (θ ℓ n)) (fun ℓ ↦ (hQ ℓ).2.1.tendsto_atTop)
    (fun ℓ ↦ ψ (η ℓ)) hψη.tendsto_atTop (fun ℓ ↦ (hQ ℓ).2.2.1) hR hgapAux
  refine ⟨Raux, hRmap, hdecomp, hret, ?_⟩
  exact D.measure_lostSourceMass_gt_le_of_original_retainedNear_iterated base
    hF hcomplete hu ha hinj horder hA hB hμA hνB hphysicalGap hdist hnearRadius (fun i ↦ (hscreenGap i).le)
    scale hscalePos hscale ap am hpm hmm hfp hfm Energy hEnergy hEp hEm
    (fun _ ↦ H) (fun _ ↦ hH) coord hcoord rootDomain hrootDomain U hU hUf
    Q Raux (fun ℓ n ↦ φ ℓ (θ ℓ n)) (fun ℓ ↦ (hQ ℓ).2.1.tendsto_atTop)
    (fun ℓ ↦ ψ (η ℓ)) hψη.tendsto_atTop (fun ℓ ↦ (hQ ℓ).2.2.1) hR
end PopulationLocalPressureCore
end OTSelector.Reconstruction
