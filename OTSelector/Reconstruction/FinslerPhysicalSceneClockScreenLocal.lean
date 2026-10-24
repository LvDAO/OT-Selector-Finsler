import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenHaar

/-!
# Actual local cores with an arbitrarily small common clock screen

A finite original Haar core is refined first to the chosen clock screen and then
to its uniform actual distance remainder. Intensity, inverse moments, original
conditional kernels and physical recovery all remain part of the produced core.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] {η₀ η₁ : Measure M}
  [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The original Haar producer constructs an actual local core at arbitrary
root accuracy with every rational clock screen below a prescribed positive
number. Its actual remainder, intensities, moments and recovery laws persist. -/
theorem PopulationHaarPressureCoreLaw.exists_local_core_small_clock_screen
    (hcore : PopulationHaarPressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hGood : ∀ᵐ z ∂lambda, Good z)
    {θ : ℝ} (hθ : 0 < θ) (hδ : δ ≠ 0) (hloss : loss ≠ 0) :
    ∃ D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss,
      ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ θ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hh : loss / 2 / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.half_pos hloss).ne').ne'
  obtain ⟨D₀⟩ := hcore Good hGood δ hδ (loss / 2 / 2) hh
  have hp := D₀.exists_small_clock_screen_refinement hrecovery hF hcomplete
    hu ha hinj hθ (ε := loss / 2 / 2) hh
  obtain ⟨D, hscreenD⟩ := hp
  obtain ⟨K, hlost, hK, hrem⟩ :=
    OriginalPopulationCoefficientCore.exists_finite_uniform_distance_refinement
      hF hcomplete hu ha hinj D.continuous.coefficient hκ (ENNReal.half_pos hloss).ne'
  have hsmall : lambda (⋃ i, K i)ᶜ < loss := by
    have hcover : (⋃ i, K i)ᶜ ⊆ D.continuous.population.rootsᶜ ∪
        ((⋃ i, (D.continuous.coefficient i).roots) \ ⋃ i, K i) := by
      intro z hz
      by_cases h : z ∈ D.continuous.population.roots
      · exact Or.inr ⟨D.continuous.union_eq.symm ▸ h, hz⟩
      · exact Or.inl h
    exact ((measure_mono hcover).trans (measure_union_le _ _)).trans_lt
      (by simpa only [ENNReal.add_halves] using
        ENNReal.add_lt_add D.continuous.population.complement_small hlost)
  refine ⟨{
    haar := D.refine hrecovery hcomplete ha hu.continuous.measurable
      (fun i ↦ (hK i).2.1) (fun i ↦ (hK i).1) hsmall
    remainder := hrem }, ?_⟩
  exact hscreenD

end OTSelector.Reconstruction
