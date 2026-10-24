import OTSelector.Reconstruction.FinslerCoefficientCoreOscillation
import OTSelector.Finite.ResidualHallStability

/-!
Finite clock-bin masses inherit the proved original L1 continuity. Multiplying
by the actual original Haar intensity gives continuous full class profiles and
finite reference neighborhoods with pointwise domination of fixed thinnings.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

/-- Evaluation on a fixed measurable clock bin is dominated by total variation. -/
theorem abs_binMass_sub_le_totalVariation {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {B : Set X} (hB : MeasurableSet B) :
    |μ.real B - ν.real B| ≤ (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ := by
  have h := (μ.toSignedMeasure - ν.toSignedMeasure).norm_le_totalVariation B
  simp only [Real.norm_eq_abs, FunLike.coe_sub, Pi.sub_apply,
    Measure.toSignedMeasure_apply_measurable hB] at h
  exact h.trans (measureReal_mono (subset_univ B))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual bin mass is continuous on the original pressure core. This uses
its proved L1/TV continuity and requires no C0 clock-density upgrade. -/
theorem PopulationPressureCore.continuousOn_clock_bin_mass
    {ε : ℝ≥0∞}
    (D : PopulationPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good ε)
    (color : Fin 2) {B : Set ℝ} (hB : MeasurableSet B) :
    ContinuousOn (fun z ↦ (populationTwoColorClockKernel u a η₀ η₁ color z).real B) D.roots := by
  let _instActualMassMetric : MetricSpace M := F.metricSpace
  let _instActualMassRootMetric : MetricSpace (ℚ → M) :=
    TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  have hc : ContinuousOn (D.densityClass color) D.roots :=
    (continuous_apply color).comp_continuousOn D.continuous_class
  intro z₀ hz₀
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨radius, hradius, hnear⟩ := Metric.continuousWithinAt_iff.mp (hc z₀ hz₀) ε hε
  refine ⟨radius, hradius, fun {z} hz hdist ↦ ?_⟩
  have hm := abs_binMass_sub_le_totalVariation
    (populationTwoColorClockKernel u a η₀ η₁ color z)
    (populationTwoColorClockKernel u a η₀ η₁ color z₀) hB
  have htv : ((populationTwoColorClockKernel u a η₀ η₁ color z).toSignedMeasure -
      (populationTwoColorClockKernel u a η₀ η₁ color z₀).toSignedMeasure).totalVariation.real univ =
      ‖D.densityClass color z - D.densityClass color z₀‖ := by
    rw [measureReal_def, D.variation color z hz z₀ hz₀, ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [Real.dist_eq]
  exact (hm.trans_eq htv).trans_lt (by simpa only [dist_eq_norm] using hnear hz hdist)

/-- The full actual class density uses the original Haar intensity and original
conditional clock law, with no normalization of the original root marginal. -/
def PopulationLocalPressureCore.rootWeightedClockBinMass
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (color : Fin 2) (B : Set ℝ) (z : ℚ → M) : ℝ :=
  D.rootIntensity i z * (populationTwoColorClockKernel u a η₀ η₁ color z).real B

/-- The actual weighted finite clock-class profile is continuous on the same
retained coefficient roots. -/
theorem PopulationLocalPressureCore.continuousOn_rootWeightedClockBinMass
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (color : Fin 2) {B : Set ℝ} (hB : MeasurableSet B) :
    ContinuousOn (D.rootWeightedClockBinMass i color B)
      (D.haar.continuous.coefficient i).roots := by
  let C := D.haar.continuous.coefficient i
  let I := D.haar.intensity i
  have hI : I.roots = C.roots := D.haar.intensity_roots i
  have hsub : C.roots ⊆ D.haar.continuous.population.roots := fun z hz ↦
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
  have hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    rw [← hI]
    exact I.continuous_label
  have hdensity : ContinuousOn (D.rootIntensity i) C.roots := by
    apply I.continuous_density.comp hlabel
    intro z hz
    exact mem_image_of_mem _ (hI.symm ▸ hz)
  exact hdensity.mul
    ((D.haar.continuous.population.continuousOn_clock_bin_mass color hB).mono hsub)

/-- Actual original class masses produce finite reference neighborhoods that
simultaneously meet arbitrary positive referencewise accuracy targets. -/
theorem PopulationLocalPressureCore.exists_finite_clockClass_mass_cover
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {I : Type*} [Fintype I]
    (B : I → Set ℝ) (hB : ∀ c, MeasurableSet (B c))
    (tolerance : (ℚ → M) → ℝ)
    (htolerance : ∀ z ∈ (D.haar.continuous.coefficient i).roots, 0 < tolerance z) :
    ∃ (centers : Set (ℚ → M)) (U : (ℚ → M) → Set (ℚ → M)),
      centers.Finite ∧ centers ⊆ (D.haar.continuous.coefficient i).roots ∧
      (D.haar.continuous.coefficient i).roots ⊆ ⋃ z ∈ centers, U z ∧
      ∀ z₀ ∈ centers, IsOpen (U z₀) ∧ z₀ ∈ U z₀ ∧
        ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U z₀, ∀ color c,
          |D.rootWeightedClockBinMass i color (B c) z -
            D.rootWeightedClockBinMass i color (B c) z₀| < tolerance z₀ := by
  classical
  let _instActualMassMetric : MetricSpace M := F.metricSpace
  let _instActualMassRootMetric : MetricSpace (ℚ → M) :=
    TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  let C := D.haar.continuous.coefficient i
  let profile := fun z (c : Fin 2 × I) ↦ D.rootWeightedClockBinMass i c.1 (B c.2) z
  have hc : ContinuousOn profile C.roots := continuousOn_pi.mpr fun c ↦
    D.continuousOn_rootWeightedClockBinMass i c.1 (hB c.2)
  have hlocal (z₀ : C.roots) : ∃ radius > 0, ∀ z ∈ C.roots,
      dist z z₀.val < radius → ‖profile z - profile z₀.val‖ < tolerance z₀.val := by
    obtain ⟨radius, hradius, hnear⟩ := Metric.continuousWithinAt_iff.mp
      (hc z₀.val z₀.property) (tolerance z₀.val) (htolerance z₀.val z₀.property)
    exact ⟨radius, hradius, fun z hz hdist ↦ by simpa only [dist_eq_norm] using hnear hz hdist⟩
  choose radius hradius hnear using hlocal
  let U := fun z : ℚ → M ↦ if hz : z ∈ C.roots then Metric.ball z (radius ⟨z, hz⟩) else ∅
  have hopen : ∀ z ∈ C.roots, IsOpen (U z) := fun z hz ↦ by
    simp only [U, dite_eq_left hz]
    exact Metric.isOpen_ball
  have hmem : ∀ z ∈ C.roots, z ∈ U z := fun z hz ↦ by
    simp only [U, dite_eq_left hz]
    exact Metric.mem_ball_self (hradius ⟨z, hz⟩)
  obtain ⟨centers, hsub, hfinite, hcover⟩ := C.roots_compact.elim_finite_subcover_image hopen
    (show C.roots ⊆ ⋃ z ∈ C.roots, U z from fun z hz ↦ mem_iUnion₂.mpr ⟨z, hz, hmem z hz⟩)
  refine ⟨centers, U, hfinite, hsub, hcover, fun z₀ hz₀ ↦
    ⟨hopen z₀ (hsub hz₀), hmem z₀ (hsub hz₀), ?_⟩⟩
  intro z hz color c
  have hball : dist z z₀ < radius ⟨z₀, hsub hz₀⟩ := by
    simpa only [U, dite_eq_left (hsub hz₀), Metric.mem_ball] using hz.2
  have hnorm := hnear ⟨z₀, hsub hz₀⟩ z hz.1 hball
  exact (show |D.rootWeightedClockBinMass i color (B c) z -
      D.rootWeightedClockBinMass i color (B c) z₀| ≤ ‖profile z - profile z₀‖ by
    simpa only [profile, Pi.sub_apply, Real.norm_eq_abs] using
      (norm_le_pi_norm (profile z - profile z₀) (color, c))).trans_lt hnorm


/-- Arbitrarily small fixed thinnings of the exact frozen finite class weights
are pointwise dominated by the actual original weighted class populations on a
produced finite cover. Zero reference classes are included automatically. -/
theorem PopulationLocalPressureCore.exists_finite_clockClass_thinning_cover
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {I : Type*} [Fintype I]
    (B : I → Set ℝ) (hB : ∀ c, MeasurableSet (B c)) {η : ℝ} (hη : 0 < η) :
    ∃ (centers : Set (ℚ → M)) (U : (ℚ → M) → Set (ℚ → M)),
      centers.Finite ∧ centers ⊆ (D.haar.continuous.coefficient i).roots ∧
      (D.haar.continuous.coefficient i).roots ⊆ ⋃ z ∈ centers, U z ∧
      ∀ z₀ ∈ centers, IsOpen (U z₀) ∧ z₀ ∈ U z₀ ∧
        ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U z₀, ∀ color c,
          (1 - η) * D.rootWeightedClockBinMass i color (B c) z₀ ≤
            D.rootWeightedClockBinMass i color (B c) z := by
  classical
  let C := D.haar.continuous.coefficient i
  let profile := fun z (c : Fin 2 × I) ↦ D.rootWeightedClockBinMass i c.1 (B c.2) z
  have hnonneg (z : ℚ → M) (c : Fin 2 × I) : 0 ≤ profile z c :=
    mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg
  have hlocal (z : ℚ → M) := exists_tolerance_for_reference_thinning (profile z) (hnonneg z) hη
  choose tolerance htolerance hthin using hlocal
  obtain ⟨centers, U, hfinite, hsub, hcover, hclose⟩ :=
    D.exists_finite_clockClass_mass_cover i B hB tolerance (fun z _ ↦ htolerance z)
  refine ⟨centers, U, hfinite, hsub, hcover, fun z₀ hz₀ ↦
    ⟨(hclose z₀ hz₀).1, (hclose z₀ hz₀).2.1, ?_⟩⟩
  intro z hz color c
  exact hthin z₀ (profile z) (hnonneg z)
    (fun j ↦ ((hclose z₀ hz₀).2.2 z hz j.1 j.2).le) (color, c)

end OTSelector.Reconstruction
