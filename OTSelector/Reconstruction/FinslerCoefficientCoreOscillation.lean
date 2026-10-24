import OTSelector.Reconstruction.FinslerCoefficientCoreLocalPressure
import OTSelector.Reconstruction.FinslerCoefficientCorePartition

/-!
# Joint freezing of original geometry, Haar intensity and conditional laws

The same finite original root neighborhoods control the actual Taylor error,
coefficient variation, relative Haar intensity and both conditional total
variations. Their measurable subdivision preserves every original root mass.
-/

open Set Function MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

omit [BorelSpace E] in
/-- Additional continuous observations can be controlled on the very same finite
Taylor cover, with no change of root set or post hoc coercivity constant. -/
theorem OriginalPopulationCoefficientCore.exists_taylorRootCover_with_observation
    [TopologicalSpace.MetrizableSpace Z]
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    (hrem : ∀ η > 0, ∃ r > 0, ∀ z ∈ C.roots, C.SourceCoordinateRemainderBound z η r)
    {V : Type*} [NormedAddCommGroup V] {g : Z → V} (hg : ContinuousOn g C.roots)
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ D : C.TaylorRootCover ε, ∀ z₀ ∈ D.centers,
      ∀ z ∈ C.roots ∩ D.neighborhood z₀, ‖g z - g z₀‖ < τ := by
  obtain ⟨m, hm, hbound⟩ := C.exists_quadratic_lower_bound
  obtain ⟨r, hr, hrem⟩ := hrem (ε * m) (mul_pos hε hm)
  let bW := Module.finBasis ℝ (P C.seedIndex).seed.covector.ker
  let c := fun z ↦ (bW.equivFun (populationSeedRootLabelValue
    (P C.seedIndex).seed a z), g z)
  have hc : ContinuousOn c C.roots :=
    (bW.equivFunL.continuous.comp_continuousOn hlabel).prodMk hg
  obtain ⟨centers, U, hfinite, hsub, hcover, hlocal⟩ :=
    exists_finite_relative_matrixQuadratic_cover_with_coordinates
      C.roots_compact C.window.isCompact_region C.coefficient_continuous
      C.coefficient_posDef hc hε (lt_min hr hτ)
  let D : C.TaylorRootCover ε := {
    lowerBound := m
    lowerBound_pos := hm
    quadratic_lower_bound := hbound
    centers := centers
    finite := hfinite
    subset := hsub
    neighborhood := U
    covers := hcover
    open_neighborhood := fun z hz ↦ (hlocal z hz).1
    center_mem := fun z hz ↦ (hlocal z hz).2.1
    relative := fun z hz ↦ (hlocal z hz).2.2.1
    radius := r
    radius_pos := hr
    remainder := hrem
    coordinate_diameter := fun z₀ hz₀ z hz z' hz' ↦ by
      have hd := (norm_fst_le (c z' - c z)).trans_lt
        ((hlocal z₀ hz₀).2.2.2 z hz z' hz')
      have hd' : ‖bW.equivFun (populationSeedRootLabelValue (P C.seedIndex).seed a z' -
          populationSeedRootLabelValue (P C.seedIndex).seed a z)‖ < min r τ := by
        simpa only [c, Prod.fst_sub, ← map_sub] using hd
      exact hd'.trans_le (min_le_left _ _) }
  refine ⟨D, fun z₀ hz₀ z hz ↦ ?_⟩
  have hd := (norm_snd_le (c z - c z₀)).trans_lt
    ((hlocal z₀ hz₀).2.2.2 z₀ ⟨hsub hz₀, (hlocal z₀ hz₀).2.1⟩ z hz)
  exact hd.trans_le (min_le_right _ _)

section Population

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]

/-- The original Haar intensity at the actual inverse label of a retained root. -/
def PopulationLocalPressureCore.rootIntensity
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (z : ℚ → M) : ℝ :=
  (populationSeedPieceHaarDensity P a κ lambda (D.haar.continuous.coefficient i).seedIndex
    (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a z)).toReal

/-- One original finite Taylor cover simultaneously freezes the relative Haar
intensity and both original conditional clock laws in total variation. -/
theorem PopulationLocalPressureCore.exists_taylorRootCover_with_intensity_and_variation
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instOscillationMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover ε,
      ∀ z₀ ∈ T.centers,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ T.neighborhood z₀,
        |D.rootIntensity i z - D.rootIntensity i z₀| ≤ η * D.rootIntensity i z₀ ∧
        ∀ color : Fin 2,
          ((populationTwoColorClockKernel u a η₀ η₁ color z).toSignedMeasure -
            (populationTwoColorClockKernel u a η₀ η₁ color z₀).toSignedMeasure).totalVariation
              univ ≤ ENNReal.ofReal η := by
  let _instOscillationMetric : MetricSpace M := F.metricSpace
  let _instOscillationProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instOscillationPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let I := D.haar.intensity i
  let B := D.haar.continuous.population
  have hI : I.roots = C.roots := D.haar.intensity_roots i
  have hsub : C.roots ⊆ B.roots := fun z hz ↦
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
  have hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    rw [← hI]
    exact I.continuous_label
  have hdensity : ContinuousOn (D.rootIntensity i) C.roots := by
    apply I.continuous_density.comp hlabel
    intro z hz
    exact mem_image_of_mem _ (hI.symm ▸ hz)
  let g := fun z ↦ (D.rootIntensity i z, fun color ↦ B.densityClass color z)
  have hg : ContinuousOn g C.roots := hdensity.prodMk (B.continuous_class.mono hsub)
  obtain ⟨T, hT⟩ := C.exists_taylorRootCover_with_observation hlabel
    (D.source_remainder_on_piece hF hcomplete hu ha hinj i) hg hε
    (lt_min (mul_pos hη I.lower_pos) hη)
  refine ⟨T, fun z₀ hz₀ z hz ↦ ?_⟩
  have hb := hT z₀ hz₀ z hz
  have hlo : I.lower ≤ D.rootIntensity i z₀ :=
    (I.bounds _ (mem_image_of_mem _ (hI.symm ▸ T.subset hz₀))).1
  constructor
  · have hd := (norm_fst_le (g z - g z₀)).trans_lt hb
    change ‖D.rootIntensity i z - D.rootIntensity i z₀‖ < _ at hd
    rw [Real.norm_eq_abs] at hd
    exact hd.le.trans
      ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlo hη.le))
  · intro color
    rw [B.variation color z (hsub hz.1) z₀ (hsub (T.subset hz₀))]
    apply ENNReal.ofReal_le_ofReal
    have hd := (norm_le_pi_norm (fun j ↦ B.densityClass j z - B.densityClass j z₀) color).trans
      (norm_snd_le (g z - g z₀))
    exact (hd.trans hb.le).trans (min_le_right _ _)

end Population
end OTSelector.Reconstruction
