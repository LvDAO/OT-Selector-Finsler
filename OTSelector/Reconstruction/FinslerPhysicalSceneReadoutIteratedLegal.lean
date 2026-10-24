import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutGlobalEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutIterated
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitOuterClock

/-!
# Iterated actual original Finsler scenes with one positive legal clock gap

Original population data construct the same measurable opposite-tilt global
optimizers for every tilt index and every sample size, with one uniform true
slack-energy bound. Sample-size limits are taken for each fixed tilt before a
second tilt-index subsequence. The outer law retains the same countable target
carrier and a positive gap determined by the original disjoint supports.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

open PointProcess PointProcess.LocalConfiguration

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}
variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)

local instance physicalSceneIteratedLegalStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance physicalSceneIteratedLegalConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance physicalSceneIteratedLegalConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance physicalSceneIteratedLegalConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance physicalSceneIteratedLegalPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

set_option maxHeartbeats 1800000 in
/-- Original Finsler data produce both stages of actual weak scene limits,
retaining the original global allocations, their realized restricted columns,
a common countable target carrier, and one positive original clock gap. -/
theorem exists_finsler_original_iterated_legal_scene
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
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∃ t : ℕ → ℝ,
      ∃ aplus aminus : ∀ (_ℓ n : ℕ), ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
          M → Fin (n + 1) → ℝ,
      ∃ _hplus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
          (Fin (n + 1) → ℝ)) × M) ↦ aplus ℓ n z.1 z.2 j),
      ∃ _hminus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
          (Fin (n + 1) → ℝ)) × M) ↦ aminus ℓ n z.1 z.2 j),
        StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
        (∀ ℓ n, ∀ᵐ z ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
              t ℓ * probe s (z.1 j)) (aplus ℓ n z) ∧
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
              (-t ℓ) * probe s (z.1 j)) (aminus ℓ n z)) ∧
        (∀ ℓ n,
          ((∫⁻ z, ∫⁻ e, ENNReal.ofReal
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist e.1 (z.1 e.2)).toReal - pot (z.1 e.2) + pot e.1))
              ∂semidiscreteAllocationMeasure μ (aplus ℓ n z)
              ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C) ∧
          ((∫⁻ z, ∫⁻ e, ENNReal.ofReal
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist e.1 (z.1 e.2)).toReal - pot (z.1 e.2) + pot e.1))
              ∂semidiscreteAllocationMeasure μ (aminus ℓ n z)
              ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C)) ∧
        ∀ (H : ℕ → Set M) (_hH : ∀ n, MeasurableSet (H n))
          (coord : ℕ → M → (ι → ℝ)) (_hcoord : ∀ n, Measurable (coord n))
          (D : ℕ → Set (ι → ℝ)) (_hD : ∀ n, volume (D n) = ENNReal.ofReal ((n : ℝ) + 1)),
        ∃ Q : ℕ → ProbabilityMeasure
            (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base),
        ∃ φ : ℕ → ℕ → ℕ,
          (∀ ℓ, StrictMono (φ ℓ) ∧
            Tendsto (fun k ↦ actualAllocationRootedCountableSceneLaw base
              ((Measure.pi (fun _ : Fin (φ ℓ k + 1) ↦ ν)).prod (dirichletOne (φ ℓ k))) μ
              (aplus ℓ (φ ℓ k)) (aminus ℓ (φ ℓ k)) (_hplus ℓ (φ ℓ k)) (_hminus ℓ (φ ℓ k))
              (fun z ↦ z.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
              (H (φ ℓ k)) (_hH (φ ℓ k)) (coord (φ ℓ k)) (_hcoord (φ ℓ k))
              pot _hpot.continuous.measurable (D (φ ℓ k)) (_hD (φ ℓ k))) atTop (𝓝 (Q ℓ))) ∧
          ∃ R, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (Q ∘ ψ) atTop (𝓝 R) ∧
          ∃ gap > 0, ∀ᵐ s ∂(R : Measure
            (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
            (Function.support (LocalConfiguration.multiplicity s.2)).Countable ∧
            (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
              e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2) ∧
                gap / 2 ≤ e.2.2 - e.1.2) ∧
            (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
              e.2 ∈ Function.support (LocalConfiguration.multiplicity s.2) ∧
                gap / 2 ≤ e.2.2 - e.1.2) := by
  let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨pot, hpot, hmain⟩ := exists_finsler_original_opposite_global_energy
    hF hcomplete hdim m volM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg
    v hv hvnonneg hvolume hA hB hAB hμ hν
  refine ⟨pot, hpot, ?_⟩
  intro probe G hprobeM hprobe
  obtain ⟨C, hC, t, aplus, aminus, hplus, hminus, ht, htp, htlim, hopt, he⟩ :=
    hmain probe G hprobeM hprobe
  refine ⟨C, hC, t, aplus, aminus, hplus, hminus, ht, htp, htlim, hopt, he, ?_⟩
  intro H hH coord hcoord D hD
  let Ω := fun n ↦ (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)
  let Penv : ∀ n, Measure (Ω n) := fun n ↦
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
  have hfeasp (ℓ n : ℕ) : ∀ᵐ z ∂Penv n, IsSemidiscreteAllocation μ z.2 (aplus ℓ n z) :=
    (hopt ℓ n).mono fun _ h ↦ h.1.1
  have hfeasm (ℓ n : ℕ) : ∀ᵐ z ∂Penv n, IsSemidiscreteAllocation μ z.2 (aminus ℓ n z) :=
    (hopt ℓ n).mono fun _ h ↦ h.2.1
  obtain ⟨Q, φ, hinner, R, ψ, hψ, houter, hcarrier⟩ :=
    exists_iterated_actualAllocationRootedCountableSceneLaw base id Penv μ
      aplus aminus hplus hminus (fun _ z ↦ z.1)
      (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst) (fun _ z ↦ z.2)
      hfeasp hfeasm H hH coord hcoord pot hpot.continuous.measurable D hD
  let scale := fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  have hsp (n : ℕ) : 0 < scale n := Real.rpow_pos_of_pos (by positivity) _
  have hsTop : Tendsto scale atTop atTop :=
    tendsto_physicalSceneOriginalPressureScale (by omega : 1 < Module.finrank ℝ E)
  obtain ⟨gap, hgap, hclock⟩ := ae_iterated_actualAllocationRootedScene_clock_gap base
    id Penv μ ν hA hB hAB hμ hν aplus aminus hplus hminus
    (fun _ z ↦ z.1) (fun _ j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun n j ↦ physicalSceneOriginalDirichlet_target_law ν n j) (fun _ z ↦ z.2)
    hfeasp hfeasm H hH coord hcoord hpot scale hsp hsTop D hD C hC
    (fun ℓ n ↦ (he ℓ n).1) (fun ℓ n ↦ (he ℓ n).2)
    Q φ (fun ℓ ↦ (hinner ℓ).1) (fun ℓ ↦ (hinner ℓ).2) R ψ houter
  refine ⟨Q, φ, hinner, R, ψ, hψ, houter, gap, hgap, ?_⟩
  filter_upwards [hcarrier, hclock] with s hs hc
  exact ⟨hs.1, hs.2.1.and hc.1, hs.2.2.and hc.2⟩

end OTSelector.Reconstruction
