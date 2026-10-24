import OTSelector.Reconstruction.FinslerPhysicalSceneEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOptima

/-!
# Actual Dirichlet plan energy for a fixed original atlas potential

The given original potential's empirical energy bound transfers to its actual
target-times-Dirichlet experiment and every measurable tilted global allocation.
The potential is kept fixed while actual chart atomlessness and the same
allocation measure supply the energy transfer.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The given original atlas potential and its same-potential empirical energy
bound control every actual tilted Dirichlet allocation, without selecting a new potential. -/
theorem finsler_given_potential_dirichlet_plan_energy_le
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (pot : M → ℝ)
    (hpot : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    (C₀ : ℝ)
    (hbound : PopulationUniformEnergyBound μ ν (Module.finrank ℝ E - 1)
      (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x) C₀)
    (n : ℕ) (probe : M → M → ℝ) (G : ℝ≥0)
    (hprobeM : Measurable (Function.uncurry probe)) (hprobe : ∀ x y, |probe x y| ≤ G)
    (t : ℝ)
    (allocation : (Fin (n + 1) → M) → (Fin (n + 1) → ℝ) → M → Fin (n + 1) → ℝ)
    (hallocM : ∀ j, Measurable (fun z : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) ↦
      allocation z.1.1 z.1.2 z.2 j))
    (hfeas : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsSemidiscreteAllocation μ z.2 (allocation z.1 z.2))
    (hopt : ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      ∀ b, IsSemidiscreteAllocation μ z.2 b → semidiscreteAllocationCost μ
        (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
          ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) + t * probe s (z.1 j))
        (allocation z.1 z.2) ≤ semidiscreteAllocationCost μ
        (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
          ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) + t * probe s (z.1 j)) b) :
    (∫⁻ z, ∫⁻ e, ENNReal.ofReal
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
        ((F.lengthEDist e.1 (z.1 e.2)).toReal - pot (z.1 e.2) + pot e.1))
        ∂semidiscreteAllocationMeasure μ (allocation z.1 z.2)
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      ENNReal.ofReal (C₀ + 2 * |t| * (G : ℝ)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instDiffuse : NullSingletonClass ν :=
    nullSingletonClass_of_chartwise_ac m ν hdim hνchart
  let cost := fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x
  have hcostm : Measurable (Function.uncurry cost) := F.measurable_distance_slack hpot
  have hcost : Integrable (Function.uncurry cost) (μ.prod ν) :=
    integrable_continuous_of_compact_carriers μ ν hA hB hμ hν
      (F.continuous_distance_slack hpot)
  have hhat : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ cost x y - cost x z)) := by
    intro y z hyz
    have h := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim hμchart
      hcomplete pot one_ne_zero hyz
    simpa only [cost, one_mul, F.metricSpace_dist] using h
  obtain ⟨hcostInt, hcostBound⟩ := integral_bipartite_dirichlet_tilted_allocation_energy_le
    (S := M) (T := M) (m := n) (q := Module.finrank ℝ E - 1)
    (μ := μ) (ν := ν) hbound hcostm hcost hhat hprobeM G hprobe t allocation
    hallocM hfeas hopt
  let Ω := (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)
  let P : Measure Ω := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let k : ℝ := ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  let c : Ω → M → Fin (n + 1) → ℝ := fun z s j ↦
    k * ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s)
  have hk : 0 ≤ k := Real.rpow_nonneg (by positivity) _
  have hcn (z : Ω) (s : M) (j : Fin (n + 1)) : 0 ≤ c z s j := by
    have hle := hpot.le_add_mul (z.1 j) s
    simp only [NNReal.coe_one, one_mul, dist_comm (z.1 j) s] at hle
    exact mul_nonneg hk (by change 0 ≤ dist s (z.1 j) - pot (z.1 j) + pot s; linarith)
  have hcm (z : Ω) : Measurable (Function.uncurry (c z)) := by
    have hy : Measurable (fun e : M × Fin (n + 1) ↦ z.1 e.2) :=
      (measurable_of_finite (fun j ↦ z.1 j)).comp measurable_snd
    exact ((F.measurable_distance_slack hpot).comp (measurable_fst.prodMk hy)).const_mul k
  have hci (z : Ω) (j : Fin (n + 1)) : Integrable (fun s ↦ c z s j) μ := by
    have hcc : Continuous (fun s ↦ c z s j) :=
      ((F.continuous_distance_slack hpot).comp
        (continuous_id.prodMk continuous_const)).const_mul k
    have hi : IntegrableOn (fun s ↦ c z s j) A μ :=
      hcc.continuousOn.integrableOn_compact hA
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at hi
  have hnonneg : 0 ≤ᵐ[P] fun z ↦
      semidiscreteAllocationCost μ (c z) (allocation z.1 z.2) := by
    filter_upwards [hfeas] with z hz
    apply integral_nonneg_of_ae
    filter_upwards [hz.nonneg] with s hs
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hs j) (hcn z s j)
  have heq := lintegral_ofReal_allocationCost_eq P μ
    (fun z s ↦ allocation z.1 z.2 s) (fun z ↦ z.2) hfeas c hcm hci
    (Eventually.of_forall fun z ↦ Eventually.of_forall fun s j ↦ hcn z s j)
    hcostInt hnonneg
  change (∫⁻ z, ∫⁻ e, ENNReal.ofReal (c z e.1 e.2)
    ∂semidiscreteAllocationMeasure μ (allocation z.1 z.2) ∂P) ≤ _
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hcostBound

end OTSelector.Reconstruction
