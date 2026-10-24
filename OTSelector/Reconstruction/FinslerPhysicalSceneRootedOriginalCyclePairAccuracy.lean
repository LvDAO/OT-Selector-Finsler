import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalCyclePairExtension
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedProjectedCyclePairAccuracy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedDecomposition
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMaskedLossLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockCarrierConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalCoreConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRationalClockLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroRetainedStrictSupport

/-!
# Original core accuracy removes full cycle mass on one fixed original law

Each auxiliary original core produces its own actual retained/lost extension
of the SAME prescribed complete scene law. Original global energy, allocation
optimality and clock density build every retained certificate internally; only
the original population complement is sent to zero after both scene limits.
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

local instance originalCycleAccuracyStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalCycleAccuracyConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalCycleAccuracyConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalCycleAccuracyConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalCycleAccuracyPlanPolish {ι : Type*} [Fintype ι] :
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

/-- Original global optimizer families and auxiliary population cores with
vanishing original complement produce zero complete strict-cycle mass on the
same full scene law, without a newly prescribed witness or clock-gap law. -/
theorem ae_original_full_cyclePairMass_zero_of_core_accuracy
    {δseq lossseq : ℕ → ℝ≥0∞}
    (Dseq : ∀ m, PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r (δseq m) (lossseq m))
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
    (hscreenGap : ∀ m i, (((Dseq m).haar.continuous.coefficient i).window.val.2.2 : ℝ) < physicalGap / 2)
    (hscreenCycle : ∀ m i, (((Dseq m).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ g)
    (K : Set Edge) (hK : IsCompact K)
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
    (hU : IsOpen U) (hUf : volume U ≠ ⊤)
    (hKU : K ⊆ {e | e.1.1 ∈ U})
    (hpopulation : Tendsto (fun m ↦ μ (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ +
      ν (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ) atTop (𝓝 0)) :
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
      ∀ᵐ s ∂(Rfull : Measure MacroScene), physicalSceneCyclePairMass
        (fun s : MacroScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
        (physicalSceneStrictCyclePairEvent
          (fun s : MacroScene ↦ physicalSceneOriginalMacroCost (P := P) (a := a) j s.1)
          (physicalSceneClockGapRegion g) K margin) s = 0 := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws Qfull Rfull φ hφ ψ hψ hinner houter
  have hext (q : ℕ) := (Dseq q).exists_original_retained_cyclePair_zero_extension j base
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart hAcompact hμAcompact
    hA hB hAreg hBreg nearRadius scale hscalePos hscale probe hprobe G hprobeBound
    t ht0 ht0lim ap am hpm hmm hp hm rootDomain hrootDomain hμlaw hνlaw
    physicalGap g margin hmargin (hscreenGap q) (hscreenCycle q) K hK.measurableSet
    hphysicalGap hdist hμA hνB hnearRadius Energy hEnergy hEp hEm
    rootCarrier hrootCarrier hrootIn U hU hUf Qfull Rfull φ hφ ψ hψ hinner houter
  choose Raux hRaux using hext
  let c : MacroScene → Point → Point → ℝ :=
    fun s ↦ physicalSceneOriginalMacroCost (P := P) (a := a) j s.1
  let bad := physicalSceneStrictCyclePairEvent c (physicalSceneClockGapRegion g) K margin
  have hc : Measurable (fun z : MacroScene × Edge ↦ c z.1 z.2.1 z.2.2) := by
    have hm := (measurable_physicalSceneOriginalMacroCost hF hcomplete hu ha hinj j).comp
      (show Measurable (fun z : MacroScene × Edge ↦ (z.1.1, z.2)) from
        measurable_fst.fst.prodMk measurable_snd)
    dsimp only [c]
    simpa only [Function.comp_def] using hm
  have hbad : MeasurableSet bad := measurableSet_physicalSceneStrictCyclePairEvent c hc
    (isOpen_physicalSceneClockGapRegion g).measurableSet hK.measurableSet margin
  have hbadK (s : MacroScene) : Prod.mk s ⁻¹' bad ⊆ K ×ˢ K := fun _ hp ↦ ⟨hp.1, hp.2.1⟩
  have hlift : ((fun z : JointScene × (Edge × Edge) ↦ (z.1.1, z.2)) ⁻¹' bad) =
      physicalSceneStrictCyclePairEvent
        (fun s : JointScene ↦ physicalSceneOriginalMacroCost (P := P) (a := a) j s.1.1)
        (physicalSceneClockGapRegion g) K margin := by
    ext p
    rfl
  apply ae_full_cyclePairMass_zero_of_actual_projected_core_accuracy base Rfull Raux
    (fun m ↦ (hRaux m).1) bad hbad K hK hbadK U hKU
    (fun m ↦ (hRaux m).2.1) ?_
    (fun m ↦ volume U * (μ (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ +
      ν (⋃ i, (Dseq m).physicalCoreDomain i)ᶜ)) ?_ (fun m ↦ (hRaux m).2.2.2)
  · intro m
    rw [hlift]
    exact (hRaux m).2.2.1
  · simpa only [mul_zero] using ENNReal.Tendsto.const_mul hpopulation (Or.inr hUf)
end PopulationLocalPressureCore
end OTSelector.Reconstruction
