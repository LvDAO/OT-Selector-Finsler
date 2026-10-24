import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOptima

/-!
# Actual original Finsler global optimizers and rooted weak scenes

Original smooth Finsler geometry and Lipschitz physical populations produce one
potential and one deterministic positive decreasing tilt sequence. For every
tilt index and sample size, jointly measurable opposite global allocation
optima live on the exact original iid-target times Dirichlet experiment. Fixing
the tilt index first gives a common weak scene subsequence in sample size,
retaining the same actual source restriction and original integer target cloud.
Both limiting plans have forward clocks and use this same countable target
carrier. The two indices remain separate throughout.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

open PointProcess PointProcess.LocalConfiguration

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E : Type*} {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)

local instance : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

set_option maxHeartbeats 1600000 in
/-- Original physical population data construct the actual measurable opposite
global optimizer families at every pair of tilt index and sample size, and for
each fixed tilt produce a common countable-target forward rooted weak scene.
No optimizer family, energy bound, target-law identification, counting bound
or weak convergence is assumed. -/
theorem exists_finsler_original_rooted_countable_forward_scene
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
        ∀ (ℓ : ℕ) (H : ℕ → Set M) (_hH : ∀ n, MeasurableSet (H n))
          (coord : ℕ → M → (ι → ℝ)) (_hcoord : ∀ n, Measurable (coord n))
          (D : ℕ → Set (ι → ℝ)) (_hD : ∀ n, volume (D n) = ENNReal.ofReal ((n : ℝ) + 1)),
        ∃ Q : ProbabilityMeasure
            (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base),
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k ↦ actualAllocationRootedCountableSceneLaw base
              ((Measure.pi (fun _ : Fin (φ k + 1) ↦ ν)).prod (dirichletOne (φ k))) μ
              (aplus ℓ (φ k)) (aminus ℓ (φ k)) (_hplus ℓ (φ k)) (_hminus ℓ (φ k))
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
  obtain ⟨pot, hpot, hscene⟩ :=
    exists_finsler_lipschitz_population_rooted_countable_forward_scene base hF hcomplete hdim
      m volM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume
      hA hB hAB hμ hν
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density volM m hρ₀L.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density volM m hρ₁L.continuous.measurable hρ₁nonneg
      v hv hvolume
  refine ⟨pot, hpot, ?_⟩
  intro probe G hprobeM hprobe
  let scale := fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  have hsp (n : ℕ) : 0 < scale n := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨t, Aplus, Amin, ht, htp, htlim, hAp, hAm, hopt⟩ :=
    exists_finsler_original_opposite_global_allocations hF hcomplete (by omega) m μ ν
      hμchart hνchart hA hB hμ hν pot hpot scale (fun n ↦ (hsp n).ne')
      probe hprobeM G hprobe
  let aplus := fun ℓ n z s ↦ Aplus ℓ n (z, s)
  let aminus := fun ℓ n z s ↦ Amin ℓ n (z, s)
  have hplus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aplus ℓ n z.1 z.2 j) := hAp
  have hminus : ∀ ℓ n j, Measurable (fun z : (((Fin (n + 1) → M) ×
      (Fin (n + 1) → ℝ)) × M) ↦ aminus ℓ n z.1 z.2 j) := hAm
  refine ⟨t, aplus, aminus, hplus, hminus, ht, htp, htlim, hopt, ?_⟩
  intro ℓ H hH coord hcoord D hD
  let T : ℝ≥0 := ⟨t 0, (htp 0).le⟩
  have htbound (n : ℕ) : |t n| ≤ (T : ℝ) := by
    change |t n| ≤ t 0
    rw [abs_of_pos (htp n)]
    exact ht.antitone (Nat.zero_le n)
  have hmbound (n : ℕ) : |-t n| ≤ (T : ℝ) := by simpa only [abs_neg] using htbound n
  exact hscene probe G hprobeM hprobe (fun _ ↦ t ℓ) (fun _ ↦ -t ℓ) T
    (fun _ ↦ htbound ℓ) (fun _ ↦ hmbound ℓ)
    (aplus ℓ) (aminus ℓ) (hplus ℓ) (hminus ℓ)
    (fun n ↦ (hopt ℓ n).mono fun _ h ↦ h.1.1)
    (fun n ↦ (hopt ℓ n).mono fun _ h ↦ h.2.1)
    (fun n ↦ (hopt ℓ n).mono fun _ h ↦ h.1.2)
    (fun n ↦ (hopt ℓ n).mono fun _ h ↦ h.2.2)
    H hH coord hcoord D hD

end OTSelector.Reconstruction
