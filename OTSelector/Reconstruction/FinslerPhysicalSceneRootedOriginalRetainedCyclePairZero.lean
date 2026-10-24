import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCyclePairWitness
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockCarrierConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalCoreConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRationalClockLimit
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroRetainedStrictSupport

/-! Original opposite global optimizers produce zero retained strict-cycle mass. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

local instance originalCyclePairZeroStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalCyclePairZeroConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalCyclePairZeroConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalCyclePairZeroConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalCyclePairZeroPlanPolish {ι : Type*} [Fintype ι] :
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

/-- The SAME original global optimizer families internally produce zero
retained strict-cycle product mass at the actual original macro coefficient.
All source-carrier, clock-carrier, endpoint-null and local no-cycle inputs are
constructed; only the already produced full-scene positive gap is used. -/
theorem ae_original_retained_cyclePairMass_zero_of_iterated
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
    (gap g margin : ℝ) (hmargin : 0 ≤ margin)
    (hscreenGap : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) < gap)
    (hscreenCycle : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ g)
    (K : Set Edge) (hK : MeasurableSet K) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
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
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (Rlaw : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) →
      ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop →
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 Rlaw) →
      (∀ᵐ s ∂(Rlaw : Measure JointScene),
        ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge),
          gap ≤ e.2.2 - e.1.2) →
      ∀ᵐ s ∂(Rlaw : Measure JointScene), physicalSceneCyclePairMass
        (fun s : JointScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
        (physicalSceneStrictCyclePairEvent
          (fun s : JointScene ↦ physicalSceneOriginalMacroCost (P := P) (a := a) j s.1.1)
          (physicalSceneClockGapRegion g) K margin) s = 0 := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  classical
  intro H laws Q Rlaw φ hφ ψ hψ hinner houter hgapFull
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  have hEgood : MeasurableSet Egood :=
    D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n)
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let c : JointScene → Point → Point → ℝ :=
    fun s ↦ physicalSceneOriginalMacroCost (P := P) (a := a) j s.1.1
  have hcost : Measurable (fun z : JointScene × Edge ↦ c z.1 z.2.1 z.2.2) := by
    have hc : Measurable (fun q :
        (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × Edge ↦
          physicalSceneOriginalMacroCost (P := P) (a := a) j q.1 q.2.1 q.2.2) :=
      measurable_physicalSceneOriginalMacroCost hF hcomplete hu ha hinj j
    have hpr : Measurable (fun z : JointScene × Edge ↦ (z.1.1.1, z.2)) :=
      measurable_fst.fst.fst.prodMk measurable_snd
    dsimp only [c]
    have hh := hc.comp hpr
    simpa only [Function.comp_def] using hh
  have hnull := PopulationConditionalWindowLaw.ae_originalAllocation_full_rational_clock_null_of_iterated
    base hμlaw hνlaw ha hu.continuous.measurable ap am hpm hmm
    (fun ℓ n ↦ (hp ℓ n).mono fun _ hw ↦ hw.1)
    (fun ℓ n ↦ (hm ℓ n).mono fun _ hw ↦ hw.1)
    H hH Egood hEgood coord hcoord scale rootDomain hrootDomain
    Q Rlaw φ hφ ψ hψ hinner houter
  have hdecomp := (ae_physicalSceneMaskedDecomposition_of_iterated_weak
    base laws Q Rlaw φ ψ hinner houter (fun ℓ n ↦
      ae_physicalSceneRootedMaskedMacroscopicSceneLaw_decomposition base
        (Penv n)
        (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (fun w ↦ w.1))
        (physicalSceneGlobalAllocationFamily μ (am ℓ n) (fun w ↦ w.1))
        (measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hpm ℓ n)
          (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst))
        (measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hmm ℓ n)
          (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst))
        H hH Egood hEgood (coord n) (hcoord n) u hu.continuous.measurable (scale n)
        (fun w ↦ w.1) (fun k ↦ (measurable_pi_apply k).comp measurable_fst)
        (rootDomain n) (hrootDomain n))).2
  have hsource := (D.ae_original_retained_plans_zero_outside_macroCarrier_of_iterated j base
    hF hcomplete hu ha hinj A B hA hB nearRadius Penv ap am hpm hmm
    (fun _ w ↦ w.1) (fun _ k ↦ (measurable_pi_apply k).comp measurable_fst)
    scale hscalePos hscale rootDomain hrootDomain Q Rlaw φ hφ ψ hinner houter).2
  have hclosed (i : Fin D.haar.continuous.count)
      (hi : (D.haar.continuous.coefficient i).seedIndex = j) :=
    (D.ae_original_retained_plans_clock_carrier_of_iterated j base i hi
      hF hcomplete hu ha hinj A B hA hB nearRadius Penv ap am hpm hmm
      (fun _ w ↦ w.1) (fun _ k ↦ (measurable_pi_apply k).comp measurable_fst)
      scale hscalePos hscale rootDomain hrootDomain Q Rlaw φ hφ ψ hinner houter).2
  have hmono (i : Fin D.haar.continuous.count)
      (hi : (D.haar.continuous.coefficient i).seedIndex = j) :
      ∀ᵐ s ∂(Rlaw : Measure JointScene),
        s.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
          (D.haar.continuous.coefficient i).roots →
        IsTwoCycleMonotoneOn (c s)
          (physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window)
          ((LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).support ∩
            physicalSceneStrictClockRegion (D.haar.continuous.coefficient i).window) := by
    clear hnull hdecomp hsource hclosed hcost
    subst j
    exact D.ae_original_macro_tag_retained_support_strictClock_twoCycle i base
      hF hcomplete hu ha hinj horder hdim m hμchart hνchart hAcompact hμAcompact
      hA hB hAreg hBreg nearRadius scale hscale probe hprobe G hprobeBound t ht0 ht0lim
      ap am hpm hmm hp hm rootDomain hrootDomain Q Rlaw φ hφ ψ hψ hinner houter
  have hlocal (i : Fin D.haar.continuous.count)
      (hi : (D.haar.continuous.coefficient i).seedIndex = j) :
      ∀ᵐ s ∂(Rlaw : Measure JointScene),
        s.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
          (D.haar.continuous.coefficient i).roots →
        physicalSceneCyclePairMass
          (fun s : JointScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
          (physicalSceneStrictCyclePairEvent c (physicalSceneClockGapRegion g) K margin) s = 0 := by
    filter_upwards [hclosed i hi, hmono i hi, hnull, hdecomp, hgapFull]
      with s hc hm hn hd hg htag
    exact physicalScene_retainedCyclePairMass_zero_of_original_certificates base c hcost
      K hK s hd (D.haar.continuous.coefficient i).window gap g margin
      (hscreenGap i) (hscreenCycle i) hmargin hn hg (hc htag) (hm htag)
  have hall : ∀ᵐ s ∂(Rlaw : Measure JointScene), ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).seedIndex = j →
      s.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
        (D.haar.continuous.coefficient i).roots →
      physicalSceneCyclePairMass
        (fun s : JointScene ↦ LocalFiniteMeasure.cavityAverage s.2.1)
        (physicalSceneStrictCyclePairEvent c (physicalSceneClockGapRegion g) K margin) s = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : (D.haar.continuous.coefficient i).seedIndex = j
    · exact (hlocal i hi).mono fun _ hs _ ↦ hs
    · exact ae_of_all _ fun _ h ↦ False.elim (hi h)
  filter_upwards [hall, hsource] with s hs hsource
  rcases hsource with htag | hzero
  · obtain ⟨i, hi⟩ := mem_iUnion.mp htag
    by_cases hseed : (D.haar.continuous.coefficient i).seedIndex = j
    · rw [ite_eq_left hseed] at hi
      exact hs i hseed hi
    · rw [ite_eq_right hseed] at hi
      exact False.elim hi
  · have hz : (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) = 0 := by
      rw [LocalFiniteMeasure.coe_cavityAverage, hzero.1, hzero.2]
      simp
    change (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).prod
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) _ = 0
    rw [hz, Measure.zero_prod]
    rfl
end PopulationLocalPressureCore
end OTSelector.Reconstruction
