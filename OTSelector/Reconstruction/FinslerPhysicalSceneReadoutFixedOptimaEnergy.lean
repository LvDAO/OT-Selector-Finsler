import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutFixedEnergy

/-!
# Actual opposite global optimizer families for a fixed atlas potential

A common positive tilt sequence works at every original sample size. The same
given potential and empirical energy bound produce jointly measurable original
global optimizer families and one actual plan-energy bound for all tilt and
sample indices. No sample-dependent tilt diagonal is used.
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

/-- One given original atlas potential supplies the same measurable opposite-tilt
optimizer families at every tilt and sample index, with one uniform actual global energy. -/
theorem exists_finsler_given_potential_opposite_global_energy
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
 :
    let _inst : MetricSpace M := F.metricSpace
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
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  dsimp only
  have henergy := finsler_given_potential_dirichlet_plan_energy_le
    hF hcomplete hdim m μ ν hμchart hνchart hA hB hμ hν pot hpot C₀ hbound
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
