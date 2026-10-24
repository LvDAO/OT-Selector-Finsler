import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOptima

/-!
# Uniform actual global energy in both original indices

The original Finsler population theorem and chart atomlessness construct one
potential, a common deterministic good-tilt sequence and jointly measurable
opposite global allocation optima at every sample size. One finite bound pays
the actual original global slack energy for both signs, uniformly in both
indices on the original iid-target times Dirichlet experiment.
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

set_option maxHeartbeats 1400000 in
/-- Original physical populations produce the same measurable global opposite
optimizer families and a finite actual slack-energy bound uniform in every
pair of tilt index and sample size. -/
theorem exists_finsler_original_opposite_global_energy
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
        ∀ ℓ n,
          ((∫⁻ z, ∫⁻ e, ENNReal.ofReal
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist e.1 (z.1 e.2)).toReal - pot (z.1 e.2) + pot e.1))
              ∂semidiscreteAllocationMeasure μ (aplus ℓ n z)
              ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C) ∧
          ((∫⁻ z, ∫⁻ e, ENNReal.ofReal
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist e.1 (z.1 e.2)).toReal - pot (z.1 e.2) + pot e.1))
              ∂semidiscreteAllocationMeasure μ (aminus ℓ n z)
              ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ C) := by
  let μ := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨pot, C₀, hpot, _hC₀, henergy⟩ :=
    exists_finsler_lipschitz_population_dirichlet_plan_energy hF hcomplete hdim m volM
      ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
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
  let C := ENNReal.ofReal (C₀ + 2 * t 0 * (G : ℝ))
  refine ⟨C, ENNReal.ofReal_ne_top, t, aplus, aminus, hplus, hminus,
    ht, htp, htlim, hopt, ?_⟩
  intro ℓ n
  have htb : |t ℓ| ≤ t 0 := by rw [abs_of_pos (htp ℓ)]; exact ht.antitone (Nat.zero_le ℓ)
  have hmb : |-t ℓ| ≤ t 0 := by simpa only [abs_neg] using htb
  constructor
  · exact (henergy n probe G hprobeM hprobe (t ℓ)
      (fun Y p ↦ aplus ℓ n (Y, p)) (hplus ℓ n)
      ((hopt ℓ n).mono fun _ h ↦ h.1.1) ((hopt ℓ n).mono fun _ h ↦ h.1.2)).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [htb, G.coe_nonneg]))
  · exact (henergy n probe G hprobeM hprobe (-t ℓ)
      (fun Y p ↦ aminus ℓ n (Y, p)) (hminus ℓ n)
      ((hopt ℓ n).mono fun _ h ↦ h.2.1) ((hopt ℓ n).mono fun _ h ↦ h.2.2)).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [hmb, G.coe_nonneg]))

end OTSelector.Reconstruction
