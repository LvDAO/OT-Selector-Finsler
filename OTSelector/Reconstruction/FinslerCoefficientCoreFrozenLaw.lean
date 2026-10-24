import OTSelector.MeasureTheory.DominatedKernelVariation
import OTSelector.Reconstruction.FinslerCoefficientCoreOscillation
import OTSelector.Reconstruction.FinslerPopulationHaarCellLaws

/-!
# Raw original population laws on jointly frozen Taylor cells

The finite partition preserves the actual geometry and the original masses.
Both colors satisfy the full variation estimate against the same frozen intensity.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

open Function Manifold OTSelector.Geometry
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Positive original intensity and finite original root mass imply finite Haar
mass for every retained measurable cell, even when the cell is not compact. -/
theorem PopulationLocalPressureCore.cell_haar_finite
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) :
    IsFiniteMeasure ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
      (populationSeedRootLabelValue
        (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L)) := by
  have hlo := (D.haar.cell_haar_mass_bounds hF hcomplete hu ha hinj i hL hsub).1
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top (measure_ne_top lambda L) hlo)
    (ENNReal.ofReal_pos.mpr (D.haar.intensity i).lower_pos).ne'

/-- The original weighted Haar cell has its unchanged finite root mass. -/
theorem PopulationLocalPressureCore.cell_intensity_finite
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) :
    IsFiniteMeasure (Measure.withDensity
      ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
        (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L))
      (populationSeedPieceHaarDensity P a κ lambda
        (D.haar.continuous.coefficient i).seedIndex)) := by
  refine ⟨?_⟩
  rw [(D.haar.cell_masses hF hcomplete hu ha hinj i hL hsub).1]
  exact measure_lt_top lambda L

omit hF hcomplete hu ha hinj in
/-- Full variation of the two original raw coordinate laws against the laws with
constant original intensity and conditional mark at one retained reference root. -/
def PopulationLocalPressureCore.FrozenCellVariationBound
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (L : Set (ℚ → M)) (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) (z₀ : ℚ → M) (η : ℝ) : Prop :=
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
    let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
    ∀ color : Fin 2,
      ((μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha
          (populationTwoColorClockKernel u a η₀ η₁ color)).toSignedMeasure -
        ((D.rootIntensity i z₀).toNNReal •
          μ.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)).toSignedMeasure).totalVariation
          univ ≤
        ENNReal.ofReal (2 * η * D.rootIntensity i z₀) * (κ C.seedIndex) (R '' L)

/-- The raw original coordinate law on a measurable cell differs from its frozen
intensity and mark law by at most twice their common tolerance. -/
theorem PopulationLocalPressureCore.frozen_cell_totalVariation_le
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {z₀ : ℚ → M} (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots)
    {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ z ∈ L, |D.rootIntensity i z - D.rootIntensity i z₀| ≤
      η * D.rootIntensity i z₀)
    (hmark : ∀ z ∈ L, ∀ color : Fin 2,
      ((populationTwoColorClockKernel u a η₀ η₁ color z).toSignedMeasure -
        (populationTwoColorClockKernel u a η₀ η₁ color z₀).toSignedMeasure).totalVariation
          univ ≤ ENNReal.ofReal η) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
    let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
    ∀ color : Fin 2,
      ((μ.withDensity ρ ⊗ₘ populationSeedCoordinateClockKernel S a ha
          (populationTwoColorClockKernel u a η₀ η₁ color)).toSignedMeasure -
        ((D.rootIntensity i z₀).toNNReal •
          μ.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)).toSignedMeasure).totalVariation
          univ ≤
        ENNReal.ofReal (2 * η * D.rootIntensity i z₀) * (κ C.seedIndex) (R '' L) := by
  let _instFrozenMetric : MetricSpace M := F.metricSpace
  let _instFrozenProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFrozenPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let μ := (κ C.seedIndex).restrict (R '' L)
  let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  dsimp only
  intro color
  let k := populationTwoColorClockKernel u a η₀ η₁ color
  let k' := populationSeedCoordinateClockKernel S a ha k
  let B := D.haar.continuous.population
  have hB : C.roots ⊆ B.roots := fun z hz ↦
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
  have hac (z) (hz : z ∈ C.roots) : k z ≪ (volume : Measure ℝ) := by
    rw [← (B.density z (hB hz) color).2.1]
    exact withDensity_absolutelyContinuous _ _
  have himage : MeasurableSet (R '' L) :=
    D.haar.measurable_cell_label_image hcomplete i hL hsub
  have hroot (z) (hz : z ∈ C.roots) : R z ∈ S.labels ∧ a (S.curve (R z) 0) = z := by
    have hi : z ∈ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
    exact ⟨(D.haar.intensity i).labels_subset (mem_image_of_mem _ hi),
      (D.haar.intensity i).root_identity z hi⟩
  have hk (z) (hz : z ∈ C.roots) : k' (R z) = k z := by
    rw [show k' (R z) = k (a (S.curve (R z) 0)) from
      populationSeedCoordinateClockKernel_at_label S a ha k ⟨R z, (hroot z hz).1⟩,
      (hroot z hz).2]
  have hka : ∀ᵐ w ∂μ, k' w ≪ (volume : Measure ℝ) := by
    filter_upwards [ae_restrict_mem himage] with w hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hk z (hsub hz)]
    exact hac z (hsub hz)
  have hρ : Measurable ρ :=
    measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj C.seedIndex
  have hclose' : ∀ᵐ w ∂μ, |(ρ w).toReal - D.rootIntensity i z₀| ≤
      η * D.rootIntensity i z₀ := by
    filter_upwards [ae_restrict_mem himage] with w hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact hclose z hz
  have hmark' : ∀ᵐ w ∂μ,
      ((k' w).toSignedMeasure - (k z₀).toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal η := by
    filter_upwards [ae_restrict_mem himage] with w hw
    obtain ⟨z, hz, rfl⟩ := hw
    simpa only [hk z (hsub hz)] using hmark z hz color
  have hb := totalVariation_weighted_compProd_le_of_absolutelyContinuous μ volume k' (k z₀)
    hρ hka (hac z₀ hz₀) ENNReal.toReal_nonneg hη hclose' hmark'
  simpa only [μ, C, S, R, ρ, k, k', PopulationLocalPressureCore.rootIntensity,
    Measure.restrict_apply_univ] using hb

/-- The same actual Taylor neighborhoods automatically control both original raw
color laws on every measurable subcell, with their original masses. -/
theorem PopulationLocalPressureCore.exists_taylorRootCover_frozen_cell_laws
    (i : Fin D.haar.continuous.count) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover ε,
      ∀ z₀ ∈ T.centers, ∀ (L : Set (ℚ → M)) (hL : MeasurableSet L)
        (hsub : L ⊆ (D.haar.continuous.coefficient i).roots ∩ T.neighborhood z₀),
        D.FrozenCellVariationBound hF hcomplete hu ha hinj i L hL
          (hsub.trans inter_subset_left) z₀ η := by
  obtain ⟨T, hT⟩ := D.exists_taylorRootCover_with_intensity_and_variation
    hF hcomplete hu ha hinj i hε hη
  refine ⟨T, fun z₀ hz₀ L hL hsub ↦ ?_⟩
  exact D.frozen_cell_totalVariation_le hF hcomplete hu ha hinj i hL
    (hsub.trans inter_subset_left) (T.subset hz₀) hη.le
    (fun z hz ↦ (hT z₀ hz₀ z (hsub hz)).1)
    (fun z hz ↦ (hT z₀ hz₀ z (hsub hz)).2)

/-- A single finite measurable partition retains the actual distance and matrix
freezing cover and the full raw intensity-and-mark variation bound for both colors. -/
theorem PopulationLocalPressureCore.exists_frozen_taylor_partition
    (i : Fin D.haar.continuous.count) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover ε,
      ∃ Q : FiniteRootNeighborhoodPartition (D.haar.continuous.coefficient i).roots
        T.centers T.neighborhood,
        ∀ j : Fin Q.count, D.FrozenCellVariationBound hF hcomplete hu ha hinj i
          (Q.cell j) (Q.measurable_cell j) ((Q.cell_subset j).trans inter_subset_left)
          (Q.center j) η := by
  let _instFrozenMetric : MetricSpace M := F.metricSpace
  let _instFrozenProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFrozenPolish : PolishSpace M := inferInstance
  obtain ⟨T, hT⟩ := D.exists_taylorRootCover_frozen_cell_laws hF hcomplete hu ha hinj i hε hη
  obtain ⟨Q⟩ := T.nonempty_partition
  exact ⟨T, Q, fun j ↦ hT (Q.center j) (Q.center_mem j)
    (Q.cell j) (Q.measurable_cell j) (Q.cell_subset j)⟩

end
end OTSelector.Reconstruction
