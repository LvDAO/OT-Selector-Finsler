import OTSelector.Reconstruction.FinslerPhysicalSceneEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitCountableForward

/-!
# Actual rooted scenes from original Finsler populations

The original population energy theorem produces the potential and global
energy bound for the same measurable tilted allocation optima. Their original
physical iid-target times Dirichlet environment supplies the actual target
marginals. Haar rooting then produces a common weak scene whose two plans keep
the same countable integer target carrier and are forward in the physical
clock. Source-cell restriction retains its realized random column masses.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Canonical
variable {M : Type*} [MeasurableSpace M]

/-- Each target coordinate keeps the original physical target population law. -/
theorem physicalSceneOriginalDirichlet_target_law
    (ν : Measure M) [IsProbabilityMeasure ν] (n : ℕ) (j : Fin (n + 1)) :
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)).map
      (fun z ↦ z.1 j) = ν :=
  ((measurePreserving_eval (fun _ : Fin (n + 1) ↦ ν) j).comp
    measurePreserving_fst).map_eq

/-- The original positive-dimensional pressure scale diverges with sample size. -/
theorem tendsto_physicalSceneOriginalPressureScale {d : ℕ} (hd : 1 < d) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((d - 1 : ℕ) : ℝ)))
      atTop atTop := by
  have hq : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hd
  exact (tendsto_rpow_atTop (div_pos (by norm_num) hq)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
end Canonical

variable {E : Type*} {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)

open PointProcess PointProcess.LocalConfiguration

local instance : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

set_option maxHeartbeats 1200000 in
/-- Original smooth Finsler geometry and Lipschitz populations produce a physical
potential for which every pair of measurable original tilted optimum families
with bounded tilts has an actual rooted weak scene with common countable target
carrier and forward clocks. No scene convergence or energy bound is assumed. -/
theorem exists_finsler_lipschitz_population_rooted_countable_forward_scene
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
    ∃ (pot : M → ℝ), ∃ _hpot : LipschitzWith 1 pot,
      ∀ (probe : M → M → ℝ) (G : ℝ≥0),
        Measurable (Function.uncurry probe) → (∀ x y, |probe x y| ≤ G) →
      ∀ (tplus tminus : ℕ → ℝ) (T : ℝ≥0),
        (∀ n, |tplus n| ≤ T) → (∀ n, |tminus n| ≤ T) →
      ∀ (aplus aminus : ∀ n, ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
          M → Fin (n + 1) → ℝ),
        ∀ (_hplus : ∀ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
          (Fin (n + 1) → ℝ)) × M) ↦ aplus n z.1 z.2 j)),
        ∀ (_hminus : ∀ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
          (Fin (n + 1) → ℝ)) × M) ↦ aminus n z.1 z.2 j)),
        (∀ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          IsSemidiscreteAllocation μ z.2 (aplus n z)) →
        (∀ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          IsSemidiscreteAllocation μ z.2 (aminus n z)) →
        (∀ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          ∀ d, IsSemidiscreteAllocation μ z.2 d →
            semidiscreteAllocationCost μ
              (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                tplus n * probe s (z.1 j)) (aplus n z) ≤
            semidiscreteAllocationCost μ
              (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                tplus n * probe s (z.1 j)) d) →
        (∀ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          ∀ d, IsSemidiscreteAllocation μ z.2 d →
            semidiscreteAllocationCost μ
              (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                tminus n * probe s (z.1 j)) (aminus n z) ≤
            semidiscreteAllocationCost μ
              (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
                ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
                tminus n * probe s (z.1 j)) d) →
      ∀ (H : ℕ → Set M) (_hH : ∀ n, MeasurableSet (H n))
        (coord : ℕ → M → (ι → ℝ)) (_hcoord : ∀ n, Measurable (coord n))
        (D : ℕ → Set (ι → ℝ)) (_hD : ∀ n, volume (D n) = ENNReal.ofReal ((n : ℝ) + 1)),
      ∃ Q : ProbabilityMeasure
          (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base),
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (fun k ↦ actualAllocationRootedCountableSceneLaw base
            ((Measure.pi (fun _ : Fin (φ k + 1) ↦ ν)).prod (dirichletOne (φ k))) μ
            (aplus (φ k)) (aminus (φ k)) (_hplus (φ k)) (_hminus (φ k))
            (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
            (H (φ k)) (_hH (φ k)) (coord (φ k)) (_hcoord (φ k))
            pot _hpot.continuous.measurable (D (φ k)) (_hD (φ k))) atTop (𝓝 Q) ∧
          ∀ᵐ s ∂(Q : Measure
            (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
            (Function.support (LocalConfiguration.multiplicity s.2)).Countable ∧
            (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
              e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2) ∧ e.1.2 < e.2.2) ∧
            (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
              e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2) ∧ e.1.2 < e.2.2) := by
  let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨pot, C, hpot, _hC, henergy⟩ :=
    exists_finsler_lipschitz_population_dirichlet_plan_energy hF hcomplete hdim m volM
      ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  refine ⟨pot, hpot, ?_⟩
  intro probe G hprobeM hprobe tplus tminus T htplus htminus
    aplus aminus hplus hminus hfeasplus hfeasminus hoptplus hoptminus H hH coord hcoord D hD
  let Ω := fun n ↦ (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)
  let Penv : ∀ n, Measure (Ω n) := fun n ↦
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  let scale := fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  have hsp (n : ℕ) : 0 < scale n := Real.rpow_pos_of_pos (by positivity) _
  have hsTop : Tendsto scale atTop atTop :=
    tendsto_physicalSceneOriginalPressureScale (by omega : 1 < Module.finrank ℝ E)
  have hp (n : ℕ) : (∫⁻ z, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (z.1 e.2) - pot (z.1 e.2) + pot e.1))
        ∂semidiscreteAllocationMeasure μ (aplus n z) ∂Penv n) ≤
        ENNReal.ofReal (C + 2 * (T : ℝ) * G) := by
    exact (henergy n probe G hprobeM hprobe (tplus n)
      (fun Y p ↦ aplus n (Y, p)) (hplus n) (hfeasplus n) (hoptplus n)).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [htplus n, (G : ℝ≥0).coe_nonneg]))
  have hm (n : ℕ) : (∫⁻ z, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 (z.1 e.2) - pot (z.1 e.2) + pot e.1))
        ∂semidiscreteAllocationMeasure μ (aminus n z) ∂Penv n) ≤
        ENNReal.ofReal (C + 2 * (T : ℝ) * G) := by
    exact (henergy n probe G hprobeM hprobe (tminus n)
      (fun Y p ↦ aminus n (Y, p)) (hminus n) (hfeasminus n) (hoptminus n)).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [htminus n, (G : ℝ≥0).coe_nonneg]))
  exact exists_actualAllocationRootedCountableScene_forward_limit base id Penv μ ν
    hA hB hAB hμ hν aplus aminus hplus hminus (fun _ z ↦ z.1)
    (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun n j ↦ physicalSceneOriginalDirichlet_target_law ν n j)
    (fun _ z ↦ z.2) hfeasplus hfeasminus H hH coord hcoord hpot
    scale hsp hsTop D hD _ ENNReal.ofReal_ne_top hp hm

end OTSelector.Reconstruction
