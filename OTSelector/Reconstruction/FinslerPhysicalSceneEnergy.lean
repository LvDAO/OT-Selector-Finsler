import OTSelector.Reconstruction.FinslerPopulationDirichletEnergy
import OTSelector.Reconstruction.DirichletMarkWindowEnergy
import OTSelector.Probability.CavitySemidiscreteEscapeMass

/-!
# Original physical Dirichlet plan energy

The uniform energy theorem for the original Lipschitz Finsler populations is
converted to the nonnegative allocation-plan energy used by rooted scenes.
The potential and constant are produced from the original population data.
No quadratic bound away from the retained local coordinate cores is used.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
universe u v
namespace OTSelector.Reconstruction
open OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Actual original Lipschitz populations produce a uniform nonnegative
Dirichlet allocation-plan energy bound for every measurable tilted optimum. -/
theorem exists_finsler_lipschitz_population_dirichlet_plan_energy
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (volM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (volM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ x ∂volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), x ∈ B) :
    let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let _inst : MetricSpace M := F.metricSpace
    ∃ (pot : M → ℝ) (C : ℝ), LipschitzWith 1 pot ∧ 0 < C ∧
      ∀ (n : ℕ) (probe : M → M → ℝ) (G : ℝ≥0),
        Measurable (Function.uncurry probe) → (∀ x y, |probe x y| ≤ G) →
        ∀ t : ℝ,
        ∀ (allocation : (Fin (n + 1) → M) → (Fin (n + 1) → ℝ) →
            M → Fin (n + 1) → ℝ),
          (∀ j, Measurable (fun z : ((Fin (n + 1) → M) ×
            (Fin (n + 1) → ℝ)) × M ↦ allocation z.1.1 z.1.2 z.2 j)) →
          (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
            IsSemidiscreteAllocation μ z.2 (allocation z.1 z.2)) →
          (∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
            ∀ d, IsSemidiscreteAllocation μ z.2 d →
              semidiscreteAllocationCost μ
                (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^
                    (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                    ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                  t * probe s (z.1 j)) (allocation z.1 z.2) ≤
              semidiscreteAllocationCost μ
                (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^
                    (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                    ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                  t * probe s (z.1 j)) d) →
          (∫⁻ z, ∫⁻ e, ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^
                (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                ((F.lengthEDist e.1 (z.1 e.2)).toReal - pot (z.1 e.2) + pot e.1))
            ∂semidiscreteAllocationMeasure μ (allocation z.1 z.2)
            ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
              ENNReal.ofReal (C + 2 * |t| * (G : ℝ)) := by
  let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨pot, C, hpot, hC, henergy⟩ :=
    exists_finsler_lipschitz_population_dirichlet_energy hF hcomplete hdim m volM
      ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  refine ⟨pot, C, hpot, hC, fun n probe G hprobeM hprobe t allocation hallocM hfeas hopt ↦ ?_⟩
  obtain ⟨hcostInt, hcostBound⟩ :=
    henergy n probe G hprobeM hprobe t allocation hallocM hfeas hopt
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
