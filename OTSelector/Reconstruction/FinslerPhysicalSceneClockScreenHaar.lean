import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenCoefficient

/-!
# Smaller clock screens on the same original cores

The rational clock gap can be placed below any positive numerical threshold,
with an arbitrarily small loss of original root mass. The original scalar
interval, seed data, conditional laws and retained recovery are preserved.
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

private theorem intensity_roots_cast {j j' : ℕ} {S : Set (ℚ → M)} {ε : ℝ≥0∞}
    (h : j = j') (I : PopulationSeedIntensityCore P a κ lambda j S ε) :
    (h ▸ I).roots = I.roots := by
  cases h
  rfl

/-- A common smaller rational clock screen is produced inside the same actual
Haar core. Only an arbitrarily small additional original root mass is lost;
original intensity, inverse-moment bounds and physical recovery are retained. -/
theorem PopulationHaarPressureCore.exists_small_clock_screen_refinement
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {θ : ℝ} (hθ : 0 < θ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ D' : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ (loss + ε),
      ∀ i, ((D'.continuous.coefficient i).window.val.2.2 : ℝ) ≤ θ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨τ, hτ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Fin D.continuous.count)
  choose C hseed hleft hright hgap hsub hloss using fun i : Fin D.continuous.count ↦
    (D.continuous.coefficient i).exists_smaller_clock_screen_refinement
      hF hcomplete hu ha hinj hθ (hτ i).ne'
  have hpop : (⋃ i, (C i).roots) ⊆ D.continuous.population.roots := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    rw [← D.continuous.union_eq]
    exact mem_iUnion.mpr ⟨i, hsub i hi⟩
  have hdiff : D.continuous.population.roots \ (⋃ i, (C i).roots) ⊆
      ⋃ i, (D.continuous.coefficient i).roots \ (C i).roots := by
    rintro z ⟨hz, hnot⟩
    rw [← D.continuous.union_eq] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i, hi, fun h ↦ hnot (mem_iUnion.mpr ⟨i, h⟩)⟩
  have htotal : lambda (D.continuous.population.roots \ (⋃ i, (C i).roots)) < ε :=
    ((measure_mono hdiff).trans (measure_iUnion_le _)).trans_lt
      ((ENNReal.tsum_le_tsum fun i ↦ (hloss i).le).trans_lt hsum)
  have hsmall : lambda (⋃ i, (C i).roots)ᶜ < loss + ε := by
    have hcover : (⋃ i, (C i).roots)ᶜ ⊆ D.continuous.population.rootsᶜ ∪
        (D.continuous.population.roots \ (⋃ i, (C i).roots)) := by
      intro z hz
      by_cases h : z ∈ D.continuous.population.roots
      · exact Or.inr ⟨h, hz⟩
      · exact Or.inl h
    exact ((measure_mono hcover).trans (measure_union_le _ _)).trans_lt
      (ENNReal.add_lt_add D.continuous.population.complement_small htotal)
  have hd : Pairwise (fun i j ↦ Disjoint (C i).roots (C j).roots) :=
    fun i j hij ↦ (D.continuous.disjoint hij).mono (hsub i) (hsub j)
  let D' : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ (loss + ε) := {
    continuous := {
      population := D.continuous.population.refine hrecovery hcomplete ha hu.continuous.measurable
        (isCompact_iUnion fun i ↦ (C i).roots_compact) hpop hsmall
      count := D.continuous.count
      coefficient := C
      disjoint := hd
      union_eq := rfl
      recovery := hrecovery.finite_recovery ha hu.continuous.measurable _
        (fun i ↦ (C i).roots_compact.measurableSet) hd }
    intensity := fun i ↦ (hseed i).symm ▸
      (D.intensity i).restrictRoots (C i).roots_compact
        (by rw [D.intensity_roots]; exact hsub i)
    intensity_roots := fun i ↦ intensity_roots_cast _ _
    moment := fun i ↦ {
      roots := (C i).roots
      subset := Subset.rfl
      compact := (C i).roots_compact
      bound := (D.moment i).bound
      bound_nonneg := (D.moment i).bound_nonneg
      envelope_le := fun z hz ↦ by
        have hb := (D.moment i).envelope_le z (by rw [D.moment_roots]; exact hsub i hz)
        simpa only [OriginalPopulationCoefficientCore.momentEnvelope, hseed i, hleft i] using hb }
    moment_roots := fun _ ↦ rfl }
  exact ⟨D', hgap⟩

end OTSelector.Reconstruction
