import OTSelector.Reconstruction.FinslerOriginalChosenPopulationAtlas
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockNull
import OTSelector.Reconstruction.FinslerPopulationPressureTiles

/-!
# Original clock laws and pressure tiles at one chosen population potential

The original population moment atlas supplies the same potential, labels, windows,
conditional laws and local-core laws. Its original joint densities imply Lebesgue
absolute continuity and atomlessness of both potential clocks. Arbitrarily accurate
local pressure cores and Taylor tiles are then constructed from these retained laws,
without a separately supplied seed family, local core or Taylor partition.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Both original clock laws of the chosen potential are Lebesgue absolutely
continuous and atomless. These conclusions concern the original physical marginals. -/
theorem chosenPopulationPotential_original_clock_laws
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    μ.map u ≪ volume ∧ ν.map u ≪ volume ∧
      NullSingletonClass (μ.map u) ∧ NullSingletonClass (ν.map u) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  have hatlas := chosenPopulationPotential_atlas
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  dsimp only [ChosenWitnessSpec] at hatlas
  obtain ⟨a, hu, _, _, _, ha, _, _, _, _, P, κ, b, _, _, _, _, _, _, _, _,
    hμlaw, hνlaw, _⟩ := hatlas
  have hu' : LipschitzWith 1 u := hu
  have project (η : Measure M)
      (hη : η.map (fun x ↦ (a x, u x)) ≪ (μ.map a).prod (volume : Measure ℝ)) :
      η.map u ≪ volume := by
    have hsnd := hη.map measurable_snd
    rw [Measure.map_map measurable_snd (ha.prodMk hu'.continuous.measurable),
      Measure.map_snd_prod] at hsnd
    exact hsnd.trans Measure.smul_absolutelyContinuous
  have hsource := project μ hμlaw.joint_absolutelyContinuous
  have htarget := project ν hνlaw.joint_absolutelyContinuous
  exact ⟨hsource, htarget,
    ⟨fun r ↦ hsource (s := {r}) Real.volume_singleton⟩,
    ⟨fun r ↦ htarget (s := {r}) Real.volume_singleton⟩⟩

/-- The chosen original atlas supplies local cores and Taylor tiles for every
positive accuracy and every almost-everywhere retained label condition. -/
theorem chosenPopulationPotential_local_pressure_data
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    ∃ (a : M → (ℚ → M)) (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker)
      (b : (ℚ → M) × ℝ → M) (vP : ℕ → E → ℝ),
      Measurable a ∧
      Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)) ∧
      ∀ (r : ℝ) (Good : (ℚ → M) → Prop), (∀ᵐ z ∂μ.map a, Good z) →
        ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ loss : ℝ≥0∞, loss ≠ 0 →
          ∀ ε : ℝ, 0 < ε →
            ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ vP b
              Good r δ loss, Nonempty (D.TaylorTiles ε) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  have hatlas := chosenPopulationPotential_atlas
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  dsimp only [ChosenWitnessSpec] at hatlas
  obtain ⟨a, hu, _hN, _hμreg, _hνreg, ha, hinj, _horder, _hbalance, _hface,
    P, κ, b, _hcover, _hμcover, _hνcover, _hκ, _hprod, _hb, _hbinv, _hwindow,
    _hμlaw, _hνlaw, _hμfull, _hνfull, _hμseed, _hνseed, _hsupport, _hcomparison,
    _hrecovery, _hcompact, _hfinite, _hpiece, _hpressure, _hcontinuous,
    _hhaar, hlocal, _hsep, _hmoment⟩ := hatlas
  refine ⟨a, P, κ, b,
    (fun j ↦ populationChartVolumeExtension v ((P j).toManifold (P j).center)),
    ha, hinj, ?_⟩
  intro r Good hGood δ hδ loss hloss ε hε
  obtain ⟨D⟩ := hlocal r Good hGood δ hδ loss hloss
  exact ⟨D, D.nonempty_taylorTiles hF hcomplete hu ha hinj hε⟩

end OTSelector.Reconstruction
