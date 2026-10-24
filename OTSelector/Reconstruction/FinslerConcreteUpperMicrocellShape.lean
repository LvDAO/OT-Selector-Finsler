import OTSelector.Probability.HaarAffineUnitPartition
import OTSelector.Reconstruction.FinslerConcreteUpperMicrocells

/-! Original measurable microcell holes, with the literal Haar Jacobian. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- Actual raw points of an original measurable cell, normalized inside one
literal half-open grid box. Only its Haar-null coordinate faces are removed. -/
def originalMicrocellShape (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) (ν : Fin q → ℤ) (s : Set E) : Set (Fin q → ℝ) :=
  affineHaarCubeCoord e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹ ''
    (s ∩ affineHaarCube e (fun l ↦ (ν l : ℝ) / n) (n : ℝ≥0)⁻¹)

/-- One original Haar Jacobian identifies every normalized microcell hole
with the original added mass, including zero retained cells. -/
theorem exists_original_microcell_shape_hole_masses
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (s : Set E), MeasurableSet s →
      ∀ (n : ℕ) [NeZero n] (ν : Fin q → ℤ),
        MeasurableSet (originalMicrocellShape e n ν s) ∧
        originalMicrocellShape e n ν s ⊆ seedUnitCube q ∧
        μ ((e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) \ s) =
          ((c * ((n : ℝ≥0)⁻¹) ^ q : ℝ≥0) : ℝ≥0∞) *
            (cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s)ᶜ := by
  obtain ⟨c, hc, hmass⟩ := exists_original_affineHaarShape_masses μ e
  refine ⟨c, hc, fun s hs n _ ν ↦ ?_⟩
  let origin : Fin q → ℝ := fun l ↦ (ν l : ℝ) / n
  let side : ℝ≥0 := (n : ℝ≥0)⁻¹
  have hside : 0 < side := inv_pos.mpr (by exact_mod_cast n.pos_of_neZero)
  let B := affineHaarCube e origin side
  let S := originalMicrocellShape e n ν s
  have hB : MeasurableSet B := measurableSet_affineHaarCube e origin side
  have hS : MeasurableSet S := measurableSet_affineHaarCubeCoord_image e origin hside (hs.inter hB)
  have hsub : S ⊆ seedUnitCube q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  refine ⟨hS, hsub, ?_⟩
  have hshape : affineHaarShape e origin side Sᶜ = B \ s := by
    have hinj : Injective (affineHaarCubeCoord e origin side) :=
      (affineHaarCubeHomeomorph e origin side hside).injective
    change B ∩ (affineHaarCubeCoord e origin side) ⁻¹'
        (affineHaarCubeCoord e origin side '' (s ∩ B))ᶜ = B \ s
    rw [preimage_compl, hinj.preimage_image]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  have hae : (e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) \ s =ᵐ[μ] B \ s := by
    filter_upwards [unitPartitionBox_ae_eq_affineHaarCube μ e n ν] with x hx
    change ((_ ∈ _) ∧ _) = ((_ ∈ B) ∧ _)
    exact congrArg (fun p : Prop ↦ p ∧ x ∉ s) hx
  calc
    _ = μ (B \ s) := measure_congr hae
    _ = _ := by simpa only [hshape] using hmass origin side hside Sᶜ hS.compl

/-- Summing the actual normalized holes counts each original added point once.
This identity uses the prescribed literal half-open partition boxes. -/
theorem exists_original_microcell_shape_filling_sum
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (s : Set E), MeasurableSet s →
      ∀ (n : ℕ) [NeZero n] (C : Finset (Fin q → ℤ)),
      (c : ℝ) * (((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) ^ q *
          (∑ ν ∈ C, ((cubeMeasure (Fin q) 1) (originalMicrocellShape e n ν s)ᶜ).toReal) =
        μ.real ((⋃ ν ∈ C, e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) \ s) := by
  classical
  obtain ⟨c, hc, hmass⟩ := exists_original_microcell_shape_hole_masses μ e
  refine ⟨c, hc, fun s hs n _ C ↦ ?_⟩
  have hmeas (ν : Fin q → ℤ) :
      MeasurableSet ((e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) \ s) :=
    ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable).diff hs
  have hdisj : PairwiseDisjoint (↑C : Set (Fin q → ℤ))
      (fun ν ↦ (e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) \ s) := by
    intro ν hν ν' hν' hne
    exact ((unitPartition.disjoint.mp hne).preimage e).mono sdiff_subset sdiff_subset
  have hset : (⋃ ν ∈ C, e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) \ s =
      ⋃ ν ∈ C, ((e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))) \ s) := by
    simp only [iUnion_sdiff]
  rw [measureReal_def, hset, measure_biUnion_finset hdisj (fun ν _ ↦ hmeas ν)]
  simp_rw [(hmass s hs n _).2.2]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow]
    rw [Finset.mul_sum]

  · intro ν hν
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)

/-- The actual normalized filling volume vanishes with the original added
Haar mass, for prescribed grids and arbitrary original measurable cells. -/
theorem tendsto_original_microcell_shape_filling_of_hole_mass
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    {s : Set E} (hs : MeasurableSet s)
    (order : ℕ → ℕ) [∀ N, NeZero (order N)] (C : ℕ → Finset (Fin q → ℤ))
    (hfill : Filter.Tendsto (fun N ↦ μ ((⋃ ν ∈ C N,
      e ⁻¹' (unitPartition.box (order N) ν : Set (Fin q → ℝ))) \ s))
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun N ↦ (((order N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) ^ q *
      ∑ ν ∈ C N, ((cubeMeasure (Fin q) 1)
        (originalMicrocellShape e (order N) ν s)ᶜ).toReal) Filter.atTop (𝓝 0) := by
  obtain ⟨c, hc, hsum⟩ := exists_original_microcell_shape_filling_sum μ e
  have hcReal : (0 : ℝ) < c := by exact_mod_cast hc
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hfill
  have h := hreal.div_const (c : ℝ)
  simp only [ENNReal.toReal_zero, zero_div] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun N ↦ by
    change μ.real ((⋃ ν ∈ C N, e ⁻¹' (unitPartition.box (order N) ν : Set (Fin q → ℝ))) \ s) / (c : ℝ) = _
    rw [← hsum s hs (order N) (C N)]
    field_simp

open Manifold OTSelector.Geometry
open scoped ContDiff
set_option linter.unusedSectionVars false

variable {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The original measurable coefficient cell itself produces prescribed
microcell shapes with uniformly small original label loss and vanishing summed
normalized hole volume. No spatial regularity of that cell is assumed. -/
theorem PopulationLocalPressureCore.exists_original_cell_microshape_filling
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin q → ℝ)) {ε : ℝ≥0∞} (hε : 0 < ε)
    (order : ℕ → ℕ) [∀ N, NeZero (order N)] (horder : Filter.Tendsto order Filter.atTop Filter.atTop) :
    let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
    let coord := atlasSeedCoord Seed e a
    let shape := fun N ν ↦ originalMicrocellShape (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ))
      (order N) ν (coord '' L)
    ∃ C : ℕ → Finset (Fin q → ℤ),
      (∀ N, Set.PairwiseDisjoint (↑(C N) : Set (Fin q → ℤ))
        (fun ν ↦ (unitPartition.box (order N) ν : Set (Fin q → ℝ)))) ∧
      (∀ N, lambda (L \ coord ⁻¹' (⋃ ν ∈ C N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ)))) < ε) ∧
      (∀ N ν, MeasurableSet (shape N ν)) ∧
      Filter.Tendsto (fun N ↦ (((order N : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) ^ q *
        ∑ ν ∈ C N, ((cubeMeasure (Fin q) 1) (shape N ν)ᶜ).toReal)
        Filter.atTop (𝓝 0) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  let coord := atlasSeedCoord Seed e a
  have hs : MeasurableSet (coord '' L) := by
    have hR := D.haar.measurable_cell_label_image hcomplete i hL hsub
    have h := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hR
    change MeasurableSet (e '' (R '' L)) at h
    change MeasurableSet ((fun z ↦ e (R z)) '' L)
    simpa only [image_image] using h
  obtain ⟨C, hdisjoint, hloss, hfill⟩ :=
    D.exists_cell_microscopic_coordinate_cubes hF hcomplete hu ha hinj i hL hsub e hε order horder
  refine ⟨C, hdisjoint, hloss, ?_, ?_⟩
  · intro N ν
    apply measurableSet_affineHaarCubeCoord_image _ _
      (inv_pos.mpr (by exact_mod_cast (order N).pos_of_neZero))
    exact hs.inter (measurableSet_affineHaarCube _ _ _)
  · apply tendsto_original_microcell_shape_filling_of_hole_mass volume
      (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ)) hs order C
    convert hfill using 1
    rfl

end OTSelector.Reconstruction
