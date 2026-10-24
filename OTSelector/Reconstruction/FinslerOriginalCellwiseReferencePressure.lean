import OTSelector.Reconstruction.FinslerStationaryPressureContinuity
import OTSelector.Reconstruction.FinslerOriginalFiniteReferencePressureConvergence

/-!
# Concrete Finsler cellwise reference pressure bounds

The finite-reference value comparison (`FinslerOriginalFiniteReferenceValue`)
controls the closed-form signed pressure value through an internally chosen
density tolerance and model/root oscillation tolerances. Its promoted
convergence form (`FinslerOriginalFiniteReferencePressureConvergence`,
`abs_finiteReferenceAggregatedPressure_sub_originalPressureReadout_lt` and
`exists_finite_reference_pressure_convergence_of_arbitrary_constants`) needs,
cell by cell, a concrete signed model pressure within an allocated budget of
the original cell pressure-readout integral.

This file produces those concrete bounds from the actual Finsler population
atlas pressure modules. The model pressure of a reference cell is the original
cell mass times the signed pressure integrand read at the retained reference
center (`finiteReferenceCellModelPressure`). For a finite measurable root
partition of a compact original intensity core the actual per-cell error is
bounded by the cell mass times the explicit cell oscillation tolerance
(`FiniteRootNeighborhoodPartition.abs_finiteReferenceCellModelPressure_sub_integral_le`).
Compact uniform continuity turns an accuracy into an explicit model/root mesh
tolerance (`exists_abs_finiteReferenceCellModelPressure_sub_integral_le`).
The capstone
`FiniteRootNeighborhoodPartition.exists_cellModelPressure_convergence` chooses
the oscillation tolerance internally from the density-accuracy budget of the
promoted convergence theorem: any model whose cell oscillation is below that
tolerance satisfies the promoted per-cell hypothesis and therefore has its
aggregated finite-reference model pressure within the prescribed accuracy of
the original pressure-readout integral. The final theorem
`PopulationSeedIntensityCore.exists_cellModelPressure_promoted_convergence`
instantiates this for the actual population atlas pressure over a family of
calibrated seed windows, with an explicit mesh tolerance `δ` (the finite
reference model/root oscillation parameter) below which the aggregated atlas
model pressure is within the prescribed accuracy of the original atlas
pressure-readout integral.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! ## Concrete cellwise model pressure -/

section GenericCell

variable {Z : Type*} [MeasurableSpace Z]

/-- The concrete finite-reference per-cell signed model pressure: the original
cell mass times the signed pressure integrand read at the retained reference
center. -/
def finiteReferenceCellModelPressure (lambda : Measure Z) (cell : Set Z) (center : Z)
    (f : Z → ℝ) : ℝ :=
  (lambda cell).toReal * f center

/-- The aggregated finite-reference model pressure is the cell-mass weighted
sum of the signed pressure integrand at the reference centers. -/
theorem finiteReferenceAggregatedPressure_cellModel_eq {N : ℕ}
    (lambda : Measure Z) (cell : Fin N → Set Z) (center : Fin N → Z) (f : Z → ℝ) :
    finiteReferenceAggregatedPressure
        (fun i ↦ finiteReferenceCellModelPressure lambda (cell i) (center i) f) =
      ∑ i, (lambda (cell i)).toReal * f (center i) := rfl

end GenericCell

/-! ## Per-cell bounds from the cell oscillation tolerance -/

section PartitionCell

variable {Z : Type*} [MeasurableSpace Z]
variable {K centers : Set Z} {U : Z → Set Z}

/-- Actual per-cell signed pressure estimate on a finite measurable root
partition: if the signed pressure integrand oscillates by at most `η` on a
cell, then the concrete cell model pressure is within `η` times the original
cell mass of the original cell pressure-readout integral. -/
theorem FiniteRootNeighborhoodPartition.abs_finiteReferenceCellModelPressure_sub_integral_le
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {η : ℝ}
    (hf : IntegrableOn f K lambda)
    (hosc : ∀ (i : Fin D.count) (z : Z), z ∈ D.cell i → |f z - f (D.center i)| ≤ η)
    (i : Fin D.count) :
    |finiteReferenceCellModelPressure lambda (D.cell i) (D.center i) f -
      ∫ z in D.cell i, f z ∂lambda| ≤ η * (lambda (D.cell i)).toReal := by
  have hcellsub : D.cell i ⊆ K := fun z hz ↦ (D.cell_subset i hz).1
  have hfcell : IntegrableOn f (D.cell i) lambda := hf.mono_set hcellsub
  have hconst : IntegrableOn (fun _ : Z ↦ f (D.center i)) (D.cell i) lambda :=
    integrable_const _
  have hconst_int : ∫ z in D.cell i, f (D.center i) ∂lambda =
      (lambda (D.cell i)).toReal * f (D.center i) := by
    rw [integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have heq : ∫ z in D.cell i, f z ∂lambda -
      (lambda (D.cell i)).toReal * f (D.center i) =
      ∫ z in D.cell i, (f z - f (D.center i)) ∂lambda := by
    rw [← hconst_int, integral_sub hfcell hconst]
  have hae : ∀ᵐ z ∂(lambda.restrict (D.cell i)), ‖f z - f (D.center i)‖ ≤ η := by
    filter_upwards [ae_restrict_mem (D.measurable_cell i)] with z hz
    rw [Real.norm_eq_abs]
    exact hosc i z hz
  have h := norm_integral_le_of_norm_le_const
    (μ := lambda.restrict (D.cell i))
    (f := fun z ↦ f z - f (D.center i)) (C := η) hae
  rw [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] at h
  rw [finiteReferenceCellModelPressure, abs_sub_comm, heq]
  exact h

/-- Mesh form of the actual per-cell pressure estimate: compact uniform
continuity of the signed pressure integrand on the retained original core
produces an explicit model/root mesh tolerance `δ` such that every reference
cell of diameter below `δ` has its concrete model pressure within `η` times its
original mass of the original cell pressure-readout integral. -/
theorem FiniteRootNeighborhoodPartition.exists_abs_finiteReferenceCellModelPressure_sub_integral_le
    {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]
    {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} (hf : IntegrableOn f K lambda)
    (hK : IsCompact K) (hcont : ContinuousOn f K)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, (∀ i : Fin D.count, D.center i ∈ K) →
      (∀ (i : Fin D.count) (z : Z), z ∈ D.cell i → dist z (D.center i) < δ) →
      ∀ i : Fin D.count,
        |finiteReferenceCellModelPressure lambda (D.cell i) (D.center i) f -
          ∫ z in D.cell i, f z ∂lambda| ≤ η * (lambda (D.cell i)).toReal := by
  obtain ⟨δ, hδ, hmod⟩ := exists_forall_abs_sub_le_of_dist_lt hK hcont hη
  refine ⟨δ, hδ, fun hcenters hdiam i ↦ ?_⟩
  exact D.abs_finiteReferenceCellModelPressure_sub_integral_le lambda hf
    (fun j z hz ↦ hmod z (D.cell_subset j hz).1 (D.center j) (hcenters j) (hdiam j z hz)) i

/-- Aggregated retained-core estimate: the sum of the concrete cellwise model
pressures of a finite reference family is within `η * λ(K)` of the original
pressure-readout integral over the retained compact core. -/
theorem FiniteRootNeighborhoodPartition.abs_finiteReferenceAggregatedPressure_cellModel_sub_integral_le
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hf : IntegrableOn f K lambda)
    (hosc : ∀ (i : Fin D.count) (z : Z), z ∈ D.cell i → |f z - f (D.center i)| ≤ η) :
    |finiteReferenceAggregatedPressure
        (fun i ↦ finiteReferenceCellModelPressure lambda (D.cell i) (D.center i) f) -
      ∫ z in K, f z ∂lambda| ≤ η * (lambda K).toReal := by
  rw [abs_sub_comm]
  simpa only [finiteReferenceAggregatedPressure, finiteReferenceCellModelPressure] using
    (D.integral_sub_weighted_sum_le lambda hf hη hosc)

end PartitionCell

/-! ## The full original atlas integral and its retained-core complement -/

section FullAtlas

variable {Z : Type*} [MeasurableSpace Z]

/-- Full-atlas estimate with the retained-core complement: the aggregated
concrete model pressure is within `η * λ(K) + B * εcomp.toReal` of the original
full pressure-readout integral, where `B` bounds the signed integrand and
`εcomp` bounds the discarded original complement mass. -/
theorem abs_finiteReferenceAggregatedPressure_cellModel_sub_full_integral_le
    {K : Set Z} (hK : MeasurableSet K) (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {B η : ℝ} (hB : 0 ≤ B)
    {ι : Type*} [Fintype ι] (cell : ι → Set Z) (center : ι → Z)
    (hint : Integrable f lambda) (hbound : ∀ z, |f z| ≤ B)
    (hcore : |∫ z in K, f z ∂lambda -
        ∑ i, finiteReferenceCellModelPressure lambda (cell i) (center i) f| ≤
      η * (lambda K).toReal)
    {εcomp : ℝ≥0∞} (hεcomp : εcomp ≠ (∞ : ℝ≥0∞)) (hsmall : lambda Kᶜ < εcomp) :
    |∫ z, f z ∂lambda -
        ∑ i, finiteReferenceCellModelPressure lambda (cell i) (center i) f| ≤
      η * (lambda K).toReal + B * εcomp.toReal := by
  simpa only [finiteReferenceCellModelPressure] using
    abs_integral_sub_weighted_sum_le_of_core_complement hK lambda hB cell center
      hint hbound hcore hεcomp hsmall

end FullAtlas

/-! ## The promoted per-cell budget and its internal oscillation tolerance -/

section PromotedBudget

variable {Z : Type*} [MeasurableSpace Z]
variable {K centers : Set Z} {U : Z → Set Z}

/-- Bridge to the promoted finite-reference convergence theorem: if the actual
cell oscillation tolerance `η` times every original cell mass is below the
allocated per-cell budget, then the concrete cell model pressures satisfy the
per-cell hypothesis of
`exists_finite_reference_pressure_convergence_of_arbitrary_constants`. -/
theorem FiniteRootNeighborhoodPartition.cellModelPressure_lt_allocated_budget
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {η budget : ℝ}
    (hf : IntegrableOn f K lambda)
    (hosc : ∀ (i : Fin D.count) (z : Z), z ∈ D.cell i → |f z - f (D.center i)| ≤ η)
    (hmass : ∀ i : Fin D.count,
      η * (lambda (D.cell i)).toReal < budget / ((D.count : ℝ) + 1)) :
    ∀ i : Fin D.count,
      |finiteReferenceCellModelPressure lambda (D.cell i) (D.center i) f -
        ∫ z in K ∩ D.cell i, f z ∂lambda| < budget / ((D.count : ℝ) + 1) := by
  intro i
  have hinter : K ∩ D.cell i = D.cell i :=
    Set.inter_eq_right.mpr (fun z hz ↦ (D.cell_subset i hz).1)
  have hbound := D.abs_finiteReferenceCellModelPressure_sub_integral_le
    lambda hf hosc i
  rw [hinter]
  exact lt_of_le_of_lt hbound (hmass i)

/-- The promoted convergence theorem applies to the concrete finite-reference
model pressure of a fixed finite reference family. The oscillation tolerance
`η` is chosen internally from the density-accuracy budget of
`exists_finite_reference_pressure_convergence_of_arbitrary_constants`: every
model whose cell oscillation is at most `η` has its aggregated concrete model
pressure within the prescribed accuracy of the original pressure-readout
integral over the retained core. -/
theorem FiniteRootNeighborhoodPartition.exists_cellModelPressure_convergence
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} (hf : IntegrableOn f K lambda)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ((∀ (i : Fin D.count) (z : Z), z ∈ D.cell i → |f z - f (D.center i)| ≤ η) →
      |finiteReferenceAggregatedPressure
          (fun i ↦ finiteReferenceCellModelPressure lambda (D.cell i) (D.center i) f) -
        originalPressureReadout lambda f K| < ε) := by
  have hKmeas : MeasurableSet K := by
    rw [← D.union_eq]
    exact MeasurableSet.iUnion D.measurable_cell
  have hcover : K ⊆ ⋃ i : Fin D.count, D.cell i := by
    rw [D.union_eq]
  obtain ⟨δv, hδv0, _hδv1, _hδvcap, hmain⟩ :=
    exists_finite_reference_pressure_convergence_of_arbitrary_constants
      (C := D.cell) (H := K) D.measurable_cell D.disjoint hKmeas hcover
      lambda f hf 0 0 hε one_pos
  obtain ⟨hbudget_pos, _hbudget_le, hpercell⟩ :=
    hmain 0 0 (le_refl 0) hδv0.le (le_refl 0) hδv0.le
  let B : ℝ := min ε (originalPressureReadout lambda f K + ε -
    finiteReferenceSignedPressureValue (originalPressureReadout lambda f K) 0 0 δv 0 0)
  have hBpos : 0 < B := hbudget_pos
  let L : ℝ := (lambda univ).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  let η : ℝ := B / ((D.count : ℝ) + 1) / (L + 1)
  have hNpos : (0 : ℝ) < (D.count : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (D.count : ℝ) := Nat.cast_nonneg D.count
    linarith
  have hηpos : 0 < η := by
    apply div_pos (div_pos hBpos hNpos)
    linarith
  refine ⟨η, hηpos, fun hosc ↦ ?_⟩
  have hmass : ∀ i : Fin D.count,
      η * (lambda (D.cell i)).toReal < B / ((D.count : ℝ) + 1) := by
    intro i
    have hLi : (lambda (D.cell i)).toReal ≤ L := by
      apply ENNReal.toReal_mono (measure_ne_top lambda univ)
      exact measure_mono (subset_univ _)
    have hBdivpos : 0 < B / ((D.count : ℝ) + 1) := div_pos hBpos hNpos
    have hstep : η * L < B / ((D.count : ℝ) + 1) := by
      have hηeq : η = (B / ((D.count : ℝ) + 1)) / (L + 1) := rfl
      rw [hηeq, div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < L + 1)]
      nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hLi hηpos.le) hstep
  have hcell := D.cellModelPressure_lt_allocated_budget lambda hf hosc hmass
  exact hpercell _ hcell

end PromotedBudget

/-! ## The actual population atlas pressure over calibrated seed windows -/

section Atlas

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [PseudoMetricSpace Z] [PolishSpace Z] [MeasurableSpace Z]
  [BorelSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The actual per-cell population atlas pressure bound: the concrete cell
model pressure (original cell mass times the atlas pressure integrand at the
retained reference center) is within the explicit oscillation tolerance `η`
times the original cell mass of the original cell atlas pressure integral, as
soon as the reference cells have diameter below the compact-uniform-continuity
mesh tolerance `δ`. -/
theorem PopulationSeedIntensityCore.exists_cellModelPressure_sub_integral_le
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (I : Z → ℝ → ℝ) {q t η : ℝ} (hq : 2 < q) (hη : 0 < η)
    (hI : ContinuousOn (fun p : Z × ℝ ↦ I p.1 p.2) (D.roots ×ˢ univ)) :
    ∃ δ > 0, ∀ {centers : Set Z} {U : Z → Set Z}
      (Q : FiniteRootNeighborhoodPartition D.roots centers U),
      (∀ i : Fin Q.count, Q.center i ∈ D.roots) →
      (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      ∀ i : Fin Q.count,
        |finiteReferenceCellModelPressure lambda (Q.cell i) (Q.center i)
            (populationAtlasIntegrand P a κ lambda I j q t) -
          ∫ z in Q.cell i, populationAtlasIntegrand P a κ lambda I j q t z ∂lambda| ≤
        η * (lambda (Q.cell i)).toReal := by
  let f := populationAtlasIntegrand P a κ lambda I j q t
  have hcont : ContinuousOn f D.roots :=
    D.continuousOn_populationAtlasIntegrand P a κ lambda I hq hI
  have hf : IntegrableOn f D.roots lambda :=
    hcont.integrableOn_of_subset_isCompact D.compact D.compact.measurableSet Subset.rfl
      (measure_ne_top lambda D.roots)
  obtain ⟨δ, hδ, hmod⟩ :=
    exists_forall_abs_sub_le_of_dist_lt D.compact hcont hη
  refine ⟨δ, hδ, fun Q hcenters hdiam i ↦ ?_⟩
  exact Q.abs_finiteReferenceCellModelPressure_sub_integral_le lambda hf
    (fun j z hz ↦ hmod z (Q.cell_subset j hz).1 (Q.center j) (hcenters j) (hdiam j z hz)) i

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Mesh convergence of the actual population atlas model pressure: for every
prescribed accuracy there is an explicit model/root mesh tolerance `δ` such
that any finite reference family of original root cells with centers on the
retained compact core and cells of diameter below `δ` has aggregated concrete
atlas model pressure within the accuracy of the original atlas pressure-readout
integral over the core. -/
theorem PopulationSeedIntensityCore.exists_cellModelPressure_convergence
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (I : Z → ℝ → ℝ) {q t : ℝ} (hq : 2 < q)
    (hI : ContinuousOn (fun p : Z × ℝ ↦ I p.1 p.2) (D.roots ×ˢ univ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {centers : Set Z} {U : Z → Set Z}
      (Q : FiniteRootNeighborhoodPartition D.roots centers U),
      (∀ i : Fin Q.count, Q.center i ∈ D.roots) →
      (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      |finiteReferenceAggregatedPressure
          (fun i ↦ finiteReferenceCellModelPressure lambda (Q.cell i) (Q.center i)
            (populationAtlasIntegrand P a κ lambda I j q t)) -
        originalPressureReadout lambda
          (populationAtlasIntegrand P a κ lambda I j q t) D.roots| < ε := by
  let f := populationAtlasIntegrand P a κ lambda I j q t
  have hcont : ContinuousOn f D.roots :=
    D.continuousOn_populationAtlasIntegrand P a κ lambda I hq hI
  have hf : IntegrableOn f D.roots lambda :=
    hcont.integrableOn_of_subset_isCompact D.compact D.compact.measurableSet Subset.rfl
      (measure_ne_top lambda D.roots)
  let L : ℝ := (lambda D.roots).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hηpos : 0 < ε / (L + 1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ :=
    exists_forall_abs_sub_le_of_dist_lt D.compact hcont hηpos
  refine ⟨δ, hδ, fun Q hcenters hdiam ↦ ?_⟩
  have hosc : ∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
      |f z - f (Q.center i)| ≤ ε / (L + 1) :=
    fun i z hz ↦ hmod z (Q.cell_subset i hz).1 (Q.center i) (hcenters i) (hdiam i z hz)
  have hbound := Q.abs_finiteReferenceAggregatedPressure_cellModel_sub_integral_le
    lambda hηpos.le hf hosc
  have hfrac : L / (L + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < L + 1)]
    linarith
  have hlt : ε / (L + 1) * (lambda D.roots).toReal < ε := by
    have hLbound : ε / (L + 1) * (lambda D.roots).toReal = ε * (L / (L + 1)) := by
      change ε / (L + 1) * L = ε * (L / (L + 1))
      rw [div_mul_eq_mul_div, ← mul_div_assoc]
    rw [hLbound]
    calc ε * (L / (L + 1)) < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := mul_one ε
  exact lt_of_le_of_lt hbound hlt

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The promoted finite-reference convergence theorem applies to the actual
population atlas model pressure of a fixed finite reference family: there is an
internally chosen model/root oscillation tolerance `η` (derived from the
density-accuracy budget) and an explicit mesh tolerance `δ` such that, whenever
the reference cells have diameter below `δ` and centers on the retained compact
core, the aggregated concrete atlas model pressure is within the prescribed
accuracy of the original atlas pressure-readout integral. -/
theorem PopulationSeedIntensityCore.exists_cellModelPressure_promoted_convergence
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (I : Z → ℝ → ℝ) {q t : ℝ} (hq : 2 < q)
    (hI : ContinuousOn (fun p : Z × ℝ ↦ I p.1 p.2) (D.roots ×ˢ univ))
    {centers : Set Z} {U : Z → Set Z}
    (Q : FiniteRootNeighborhoodPartition D.roots centers U)
    (hcenters : ∀ i : Fin Q.count, Q.center i ∈ D.roots)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      |finiteReferenceAggregatedPressure
          (fun i ↦ finiteReferenceCellModelPressure lambda (Q.cell i) (Q.center i)
            (populationAtlasIntegrand P a κ lambda I j q t)) -
        originalPressureReadout lambda
          (populationAtlasIntegrand P a κ lambda I j q t) D.roots| < ε := by
  let f := populationAtlasIntegrand P a κ lambda I j q t
  have hcont : ContinuousOn f D.roots :=
    D.continuousOn_populationAtlasIntegrand P a κ lambda I hq hI
  have hf : IntegrableOn f D.roots lambda :=
    hcont.integrableOn_of_subset_isCompact D.compact D.compact.measurableSet Subset.rfl
      (measure_ne_top lambda D.roots)
  obtain ⟨η, hηpos, himp⟩ := Q.exists_cellModelPressure_convergence lambda hf hε
  obtain ⟨δ, hδ, hmod⟩ := exists_forall_abs_sub_le_of_dist_lt D.compact hcont hηpos
  exact ⟨δ, hδ, fun hdiam ↦ himp (fun i z hz ↦
    hmod z (Q.cell_subset i hz).1 (Q.center i) (hcenters i) (hdiam i z hz))⟩

end Atlas

end OTSelector.Reconstruction
