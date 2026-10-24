import OTSelector.Reconstruction.FinslerOriginalCellwiseReferencePressure
import Mathlib.Topology.MetricSpace.Cover

/-!
# Finite measurable root partitions with small mesh and local pressure continuity

This file closes the two construction gaps reported by
`FinslerOriginalCellwiseReferencePressure`:

* the finite measurable root partition with an internal arbitrarily small mesh
  tolerance, and
* the local pressure continuity hypothesis of the cellwise atlas pressure
  convergence, derived from stationarity data instead of assumed.

## Small-mesh measurable partitions

A compact subset of a pseudo-metric Borel space is totally bounded, hence has
finite covers by balls of any radius (`Metric.exists_finite_isCover_of_totallyBounded`).
Feeding such a cover into
`exists_finiteRootNeighborhoodPartition` produces a finite measurable
`FiniteRootNeighborhoodPartition` all of whose cells lie inside the prescribed
balls, so the distance from every cell point to its retained reference center is
below any prescribed mesh tolerance `δ`. The construction also applies to the
literal root grids of the physical scene (`physicalSceneRootGridDomain`,
`exists_finite_unit_root_grid_cover`), which provide finite covers of bounded
macroscopic supports at any scale; the ball-cover construction is the mesh form
used by the cellwise pressure convergence.

## Local pressure continuity from stationarity

`FinslerStationaryPressureContinuity.continuous_stationaryPressureFamily_apply`
shows that the stationary pressure family
`stationaryPressureFamily K P Cw j` is jointly continuous in the root and tilt
when the kinetic and probe candidate data converge uniformly on the locally
constant stationary classes. Turning that global continuity into continuity on
`Kcore × univ` supplies the explicit hypothesis `hI` of
`PopulationSeedIntensityCore.exists_cellModelPressure_promoted_convergence`, so
the atlas model pressure bounds hold with the actual stationary local pressure
instead of an assumed continuous family.

## Convergence with an actual partition

Combining the two constructions with the cellwise aggregation of
`FinslerOriginalCellwiseReferencePressure`, every positive accuracy `ε` produces
an actual finite measurable root partition of the compact intensity core and a
concrete finite-reference model pressure whose aggregated value is within `ε` of
the original population atlas pressure-readout integral.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! ## Finite measurable partitions with arbitrarily small mesh -/

section RootPartition

variable {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [T2Space Z]

/-- Every compact subset of a pseudo-metric Borel space has a finite
measurable root partition whose cells are contained in prescribed balls around
their retained reference centers: for every mesh tolerance `δ > 0` the centers
lie in the compact set and every cell point is within `δ` of its center. -/
theorem exists_finiteRootNeighborhoodPartition_ball_mesh
    {K : Set Z} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (centers : Set Z) (U : Z → Set Z),
      ∃ D : FiniteRootNeighborhoodPartition K centers U,
        centers ⊆ K ∧
          ∀ (i : Fin D.count) (z : Z), z ∈ D.cell i → dist z (D.center i) < δ := by
  have hδ4 : (0 : ℝ) < δ / 4 := by linarith
  obtain ⟨N, hNK, hNfin, hcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded
      (ε := ⟨δ / 4, hδ4.le⟩) (NNReal.coe_ne_zero.mp (ne_of_gt hδ4)) hK.totallyBounded
  have hU : ∀ z ∈ N, MeasurableSet (Metric.ball z (δ / 2)) :=
    fun z _ ↦ Metric.isOpen_ball.measurableSet
  have hcoverK : K ⊆ ⋃ z ∈ N, Metric.ball z (δ / 2) := by
    intro x hx
    obtain ⟨y, hyN, hxball⟩ :=
      Set.mem_iUnion₂.mp (Metric.IsCover.subset_iUnion_closedBall hcover hx)
    have hnnd : nndist x y ≤ ⟨δ / 4, hδ4.le⟩ :=
      Metric.mem_closedBall.mp hxball
    have hdist : dist x y ≤ δ / 4 := NNReal.coe_le_coe.mpr hnnd
    exact Set.mem_iUnion₂.mpr ⟨y, hyN, Metric.mem_ball.mpr (by linarith)⟩
  obtain ⟨D⟩ :=
    exists_finiteRootNeighborhoodPartition hK.measurableSet hNfin hU hcoverK
  refine ⟨N, fun z ↦ Metric.ball z (δ / 2), D, hNK, fun i z hz ↦ ?_⟩
  have hzball : dist z (D.center i) < δ / 2 := (D.cell_subset i hz).2
  linarith

/-- Diameter form of the small-mesh partition: any two points of one cell are
within the prescribed mesh tolerance. -/
theorem exists_finiteRootNeighborhoodPartition_diam_mesh
    {K : Set Z} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (centers : Set Z) (U : Z → Set Z),
      ∃ D : FiniteRootNeighborhoodPartition K centers U,
        centers ⊆ K ∧
          ∀ (i : Fin D.count) (z w : Z), z ∈ D.cell i → w ∈ D.cell i →
            dist z w < δ := by
  obtain ⟨centers, U, D, hcenters, hball⟩ :=
    exists_finiteRootNeighborhoodPartition_ball_mesh (K := K) hK (δ := δ / 2) (by linarith)
  refine ⟨centers, U, D, hcenters, fun i z w hz hw ↦ ?_⟩
  have h1 : dist z (D.center i) < δ / 2 := hball i z hz
  have h2 : dist w (D.center i) < δ / 2 := hball i w hw
  have h2' : dist (D.center i) w < δ / 2 := by
    rw [dist_comm]
    exact h2
  linarith [dist_triangle z (D.center i) w, h1, h2']

/-- The small-mesh partition is nonempty for every mesh tolerance, so the mesh
hypotheses of the cellwise pressure convergence are never vacuous on a compact
core. -/
theorem exists_finiteRootNeighborhoodPartition_of_pos_mesh
    {K : Set Z} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (centers : Set Z) (U : Z → Set Z),
      Nonempty (FiniteRootNeighborhoodPartition K centers U) ∧ centers ⊆ K := by
  obtain ⟨centers, U, D, hcenters, _⟩ :=
    exists_finiteRootNeighborhoodPartition_ball_mesh (K := K) hK hδ
  exact ⟨centers, U, ⟨D⟩, hcenters⟩

end RootPartition

/-! ## Local pressure continuity of the stationary family -/

section StationaryPressureContinuity

variable {W Z : Type*} [TopologicalSpace Z]

/-- Joint continuity of the stationary pressure family on any core times the
full tilt line, derived from the uniform convergence of the kinetic and probe
candidate data on the locally constant stationary classes. This is the local
pressure continuity required by the cellwise atlas pressure bound, no longer
assumed. -/
theorem continuousOn_stationaryPressureFamily_of_uniform_convergence
    (K : ℕ → Z → W → ℝ) (P : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W) {G : ℝ}
    (hG : 0 ≤ G)
    (hne : ∀ j z, (Cw j z).Nonempty)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |P j z w| ≤ G)
    (hclass : ∀ j z₀, ∀ᶠ z in 𝓝 z₀, Cw j z = Cw j z₀)
    (hconv : ∀ j z₀, ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ w ∈ Cw j z₀, |K j z w - K j z₀ w| ≤ ε ∧ |P j z w - P j z₀ w| ≤ ε)
    (j : ℕ) (Kcore : Set Z) :
    ContinuousOn (fun p : Z × ℝ ↦ stationaryPressureFamily K P Cw j p.1 p.2)
      (Kcore ×ˢ univ) :=
  (continuous_stationaryPressureFamily_apply K P Cw hG hne hK hP hclass hconv
    j).continuousOn

end StationaryPressureContinuity

/-! ## Convergence with an actual constructed partition, arbitrary integrand -/

section ConstructedPartition

variable {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [T2Space Z]

/-- Convergence with an actual finite measurable reference family: for a compact
core, a finite measure, an integrable continuous signed pressure integrand and
every positive accuracy, there is a concrete finite measurable root partition
(with centers in the core) whose aggregated concrete cell model pressure is
within the accuracy of the original pressure-readout integral over the core. -/
theorem exists_finiteRootNeighborhoodPartition_cellModelPressure_convergence
    {K : Set Z} (hK : IsCompact K) (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} (hf : IntegrableOn f K lambda) (hcont : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (centers : Set Z) (U : Z → Set Z),
      ∃ Q : FiniteRootNeighborhoodPartition K centers U,
        centers ⊆ K ∧
          |finiteReferenceAggregatedPressure
              (fun i ↦ finiteReferenceCellModelPressure lambda (Q.cell i)
                (Q.center i) f) -
            originalPressureReadout lambda f K| < ε := by
  let L : ℝ := (lambda K).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hηpos : 0 < ε / (L + 1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := exists_forall_abs_sub_le_of_dist_lt hK hcont hηpos
  obtain ⟨centers, U, Q, hcenters, hball⟩ :=
    exists_finiteRootNeighborhoodPartition_ball_mesh (K := K) hK hδ
  refine ⟨centers, U, Q, hcenters, ?_⟩
  have hosc : ∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
      |f z - f (Q.center i)| ≤ ε / (L + 1) :=
    fun i z hz ↦ hmod z (Q.cell_subset i hz).1 (Q.center i)
      (hcenters (Q.center_mem i)) (hball i z hz)
  have hbound := Q.abs_finiteReferenceAggregatedPressure_cellModel_sub_integral_le
    lambda hηpos.le hf hosc
  have hfrac : L / (L + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < L + 1)]
    linarith
  have hlt : ε / (L + 1) * (lambda K).toReal < ε := by
    have hLbound : ε / (L + 1) * (lambda K).toReal = ε * (L / (L + 1)) := by
      change ε / (L + 1) * L = ε * (L / (L + 1))
      rw [div_mul_eq_mul_div, ← mul_div_assoc]
    rw [hLbound]
    calc ε * (L / (L + 1)) < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := mul_one ε
  exact lt_of_le_of_lt hbound hlt

end ConstructedPartition

/-! ## The actual population atlas pressure with stationary local pressure -/

section Atlas

variable {E M Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [PseudoMetricSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}


omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The small-mesh partition construction applied to the actual retained compact
core of a population seed intensity core: for every mesh tolerance there is a
finite measurable partition of the actual original roots with centers on the
core and every cell point within the tolerance of its center. -/
theorem PopulationSeedIntensityCore.exists_rootPartition_ball_mesh
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (centers : Set Z) (U : Z → Set Z),
      ∃ Q : FiniteRootNeighborhoodPartition D.roots centers U,
        centers ⊆ D.roots ∧
          ∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i → dist z (Q.center i) < δ :=
  exists_finiteRootNeighborhoodPartition_ball_mesh D.compact hδ

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The actual population atlas pressure with the stationary local pressure: for
every positive accuracy there is an explicit model/root mesh tolerance `δ` such
that any finite reference family of original root cells with centers on the
retained compact core and cells of diameter below `δ` has aggregated concrete
atlas model pressure within the accuracy of the original atlas
pressure-readout integral over the core. The local pressure continuity is
derived from the stationarity data, not assumed. -/
theorem PopulationSeedIntensityCore.exists_stationaryPressure_cellModelPressure_convergence
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W) {G : ℝ}
    (hG : 0 ≤ G)
    (hne : ∀ j z, (Cw j z).Nonempty)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |Ppr j z w| ≤ G)
    (hclass : ∀ j z₀, ∀ᶠ z in 𝓝 z₀, Cw j z = Cw j z₀)
    (hconv : ∀ j z₀, ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ w ∈ Cw j z₀, |K j z w - K j z₀ w| ≤ ε ∧ |Ppr j z w - Ppr j z₀ w| ≤ ε)
    {q t : ℝ} (hq : 2 < q) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {centers : Set Z} {U : Z → Set Z}
      (Q : FiniteRootNeighborhoodPartition D.roots centers U),
      (∀ i : Fin Q.count, Q.center i ∈ D.roots) →
      (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      |finiteReferenceAggregatedPressure
          (fun i ↦ finiteReferenceCellModelPressure lambda (Q.cell i) (Q.center i)
            (populationAtlasIntegrand P a κ lambda
              (stationaryPressureFamily K Ppr Cw j) j q t)) -
        originalPressureReadout lambda
          (populationAtlasIntegrand P a κ lambda
            (stationaryPressureFamily K Ppr Cw j) j q t) D.roots| < ε := by
  have hI : ContinuousOn
      (fun p : Z × ℝ ↦ stationaryPressureFamily K Ppr Cw j p.1 p.2)
      (D.roots ×ˢ univ) :=
    continuousOn_stationaryPressureFamily_of_uniform_convergence K Ppr Cw hG hne
      hK hP hclass hconv j D.roots
  exact PopulationSeedIntensityCore.exists_cellModelPressure_convergence
    (P := P) (a := a) (κ := κ) (lambda := lambda) (D := D)
    (I := stationaryPressureFamily K Ppr Cw j) (hq := hq) (hI := hI) (hε := hε)

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Convergence with an actual constructed finite reference family for the
actual population atlas pressure with stationary local pressure: for every
positive accuracy there is a concrete finite measurable root partition of the
retained compact core, with centers in the core, whose aggregated concrete atlas
model pressure is within the accuracy of the original atlas pressure-readout
integral over the core. -/
theorem PopulationSeedIntensityCore.exists_rootPartition_stationaryPressure_convergence
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W) {G : ℝ}
    (hG : 0 ≤ G)
    (hne : ∀ j z, (Cw j z).Nonempty)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |Ppr j z w| ≤ G)
    (hclass : ∀ j z₀, ∀ᶠ z in 𝓝 z₀, Cw j z = Cw j z₀)
    (hconv : ∀ j z₀, ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ w ∈ Cw j z₀, |K j z w - K j z₀ w| ≤ ε ∧ |Ppr j z w - Ppr j z₀ w| ≤ ε)
    {q t : ℝ} (hq : 2 < q) {ε : ℝ} (hε : 0 < ε) :
    ∃ (centers : Set Z) (U : Z → Set Z),
      ∃ Q : FiniteRootNeighborhoodPartition D.roots centers U,
        centers ⊆ D.roots ∧
          |finiteReferenceAggregatedPressure
              (fun i ↦ finiteReferenceCellModelPressure lambda (Q.cell i)
                (Q.center i)
                (populationAtlasIntegrand P a κ lambda
                  (stationaryPressureFamily K Ppr Cw j) j q t)) -
            originalPressureReadout lambda
              (populationAtlasIntegrand P a κ lambda
                (stationaryPressureFamily K Ppr Cw j) j q t) D.roots| < ε := by
  have hI : ContinuousOn
      (fun p : Z × ℝ ↦ stationaryPressureFamily K Ppr Cw j p.1 p.2)
      (D.roots ×ˢ univ) :=
    continuousOn_stationaryPressureFamily_of_uniform_convergence K Ppr Cw hG hne
      hK hP hclass hconv j D.roots
  have hcont : ContinuousOn
      (fun z ↦ populationAtlasIntegrand P a κ lambda
        (stationaryPressureFamily K Ppr Cw j) j q t z) D.roots :=
    D.continuousOn_populationAtlasIntegrand P a κ lambda
      (stationaryPressureFamily K Ppr Cw j) hq hI
  have hf : IntegrableOn
      (fun z ↦ populationAtlasIntegrand P a κ lambda
        (stationaryPressureFamily K Ppr Cw j) j q t z) D.roots lambda :=
    hcont.integrableOn_of_subset_isCompact D.compact D.compact.measurableSet
      Subset.rfl (measure_ne_top lambda D.roots)
  exact exists_finiteRootNeighborhoodPartition_cellModelPressure_convergence
    (K := D.roots) D.compact lambda hf hcont hε

end Atlas

end OTSelector.Reconstruction
