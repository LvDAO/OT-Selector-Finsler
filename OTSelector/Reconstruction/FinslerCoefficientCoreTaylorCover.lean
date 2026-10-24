import OTSelector.Reconstruction.FinslerCoefficientCoreCoordinates

/-!
# Finite original root neighborhoods for Taylor expansion and coefficient freezing

One finite cover controls both the actual coefficient error and every pair of
original label coordinates in a neighborhood. The coercivity constant is chosen
before the Taylor radius, so all estimates use the same original coefficient.
-/

open Set Function MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- A compact matrix field and a continuous coordinate map admit one finite cover
with relative coefficient control and small coordinate diameter. -/
theorem exists_finite_relative_matrixQuadratic_cover_with_coordinates
    {n Z T V : Type*} [Fintype n]
    [TopologicalSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
    [NormedAddCommGroup V] {K : Set Z} {H : Set T}
    (hK : IsCompact K) (hH : IsCompact H)
    {A : Z × T → Matrix n n ℝ} (hA : ContinuousOn A (K ×ˢ H))
    (hpos : ∀ z ∈ K, ∀ p ∈ H, (A (z, p)).PosDef)
    {c : Z → V} (hc : ContinuousOn c K) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ (centers : Set Z) (U : Z → Set Z), centers.Finite ∧ centers ⊆ K ∧
      K ⊆ ⋃ z ∈ centers, U z ∧ ∀ z₀ ∈ centers, IsOpen (U z₀) ∧ z₀ ∈ U z₀ ∧
        (∀ z ∈ K ∩ U z₀, ∀ p ∈ H, ∀ v : n → ℝ,
          |matrixQuadratic (A (z, p)) v - matrixQuadratic (A (z₀, p)) v| ≤
            ε * matrixQuadratic (A (z₀, p)) v) ∧
        ∀ z ∈ K ∩ U z₀, ∀ z' ∈ K ∩ U z₀, ‖c z' - c z‖ < r := by
  let : MetricSpace Z := TopologicalSpace.metrizableSpaceMetric Z
  let : MetricSpace T := TopologicalSpace.metrizableSpaceMetric T
  obtain ⟨d, hd, hfreeze⟩ := exists_uniform_relative_matrixQuadratic
    (hK.prod hH) hA (fun q hq ↦ hpos q.1 hq.1 q.2 hq.2) hε
  obtain ⟨s, hs, hcoords⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hc) r hr
  let radius := min d (s / 2)
  have hrad : 0 < radius := lt_min hd (half_pos hs)
  let U : Z → Set Z := fun z ↦ Metric.ball z radius
  have hcover : K ⊆ ⋃ z ∈ K, U z := fun z hz ↦
    mem_iUnion_of_mem z (mem_iUnion_of_mem hz (Metric.mem_ball_self hrad))
  obtain ⟨centers, hsub, hfinite, hcov⟩ := hK.elim_finite_subcover_image
    (fun z _ ↦ Metric.isOpen_ball (x := z) (ε := radius)) hcover
  refine ⟨centers, U, hfinite, hsub, hcov, fun z₀ hz₀ ↦
    ⟨Metric.isOpen_ball, Metric.mem_ball_self hrad, ?_, ?_⟩⟩
  · intro z hz p hp v
    apply hfreeze (z, p) ⟨hz.1, hp⟩ (z₀, p) ⟨hsub hz₀, hp⟩
    have hdist : dist z z₀ < d := hz.2.trans_le (min_le_left _ _)
    simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hdist
  · intro z hz z' hz'
    have hzdist : dist z z₀ < s / 2 := hz.2.trans_le (min_le_right _ _)
    have hz'dist : dist z' z₀ < s / 2 := hz'.2.trans_le (min_le_right _ _)
    have hdist : dist z' z < s := by
      have ht := dist_triangle z' z₀ z
      rw [dist_comm z₀ z] at ht
      linarith
    simpa only [dist_eq_norm] using hcoords z' hz'.1 z hz.1 hdist

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- One finite actual root cover retaining its Taylor radius and the coordinate
diameter bound for every pair of roots in each neighborhood. -/
structure TaylorRootCover (ε : ℝ) extends C.RelativeRootCover ε where
  radius : ℝ
  radius_pos : 0 < radius
  remainder : ∀ z ∈ C.roots,
    C.SourceCoordinateRemainderBound z (ε * lowerBound) radius
  coordinate_diameter : ∀ z₀ ∈ centers, ∀ z ∈ C.roots ∩ neighborhood z₀,
    ∀ z' ∈ C.roots ∩ neighborhood z₀,
      ‖(Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P C.seedIndex).seed a z' -
          populationSeedRootLabelValue (P C.seedIndex).seed a z)‖ < radius

omit [BorelSpace E] in
/-- Continuity and the actual uniform remainder produce simultaneous finite
Taylor and freezing neighborhoods, without choosing a second coercivity bound. -/
theorem exists_taylorRootCover [TopologicalSpace.MetrizableSpace Z]
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    (hrem : ∀ η > 0, ∃ r > 0, ∀ z ∈ C.roots, C.SourceCoordinateRemainderBound z η r)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (C.TaylorRootCover ε) := by
  obtain ⟨m, hm, hbound⟩ := C.exists_quadratic_lower_bound
  obtain ⟨r, hr, hrem⟩ := hrem (ε * m) (mul_pos hε hm)
  let bW := Module.finBasis ℝ (P C.seedIndex).seed.covector.ker
  have hc : ContinuousOn (fun z ↦ bW.equivFun
      (populationSeedRootLabelValue (P C.seedIndex).seed a z)) C.roots :=
    bW.equivFunL.continuous.comp_continuousOn hlabel
  obtain ⟨centers, U, hfinite, hsub, hcover, hlocal⟩ :=
    exists_finite_relative_matrixQuadratic_cover_with_coordinates
      C.roots_compact C.window.isCompact_region C.coefficient_continuous
      C.coefficient_posDef hc hε hr
  exact ⟨{
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
      simpa only [map_sub] using (hlocal z₀ hz₀).2.2.2 z hz z' hz' }⟩

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instTaylorRootMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Actual source and target roots in one retained neighborhood satisfy the frozen
quadratic comparison; small displacement and target legality are derived. -/
theorem TaylorRootCover.relative_distance
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) {z₀ z z' : Z}
    (hz₀ : z₀ ∈ D.centers) (hz : z ∈ C.roots ∩ D.neighborhood z₀)
    (hz' : z' ∈ C.roots ∩ D.neighborhood z₀)
    {p : ℝ × ℝ} (hp : p ∈ C.window.region) :
    let S := (P C.seedIndex).seed
    let w := populationSeedRootLabelValue S a
    let v := (Module.finBasis ℝ S.covector.ker).equivFun (w z' - w z)
    |populationSeedPairDeficit S p (w z, w z') - matrixQuadratic (C.matrix z₀ p) v| ≤
      (2 * ε) * matrixQuadratic (C.matrix z₀ p) v := by
  dsimp only
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a
  let bW := Module.finBasis ℝ S.covector.ker
  let v := bW.equivFun (w z' - w z)
  have heq : w z + bW.equivFun.symm v = w z' := by
    simp only [v, LinearEquiv.symm_apply_apply, add_sub_cancel]
  have hb := D.remainder z hz.1 p hp v (D.coordinate_diameter z₀ hz₀ z hz z' hz')
    (by rw [heq]; exact C.root_label_mem_window hF hcomplete hu ha hinj hz'.1)
  rw [heq] at hb
  exact D.toRelativeRootCover.relative_cost_of_quadratic_remainder hε hz₀ hz hp v hb

/-- The original Haar seed law produces an arbitrarily large compact core and its
finite actual Taylor cover. No uniform remainder or label continuity is assumed. -/
theorem exists_compact_taylorRootCover [T2Space Z] [BorelSpace Z] [PolishSpace Z]
    [IsFiniteMeasure lambda] (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    {ε : ℝ} (hε : 0 < ε) {loss : ℝ≥0∞} (hloss : loss ≠ 0) :
    ∃ (K : Set Z) (hK : IsCompact K) (hsub : K ⊆ C.roots),
      lambda (C.roots \ K) < loss ∧
        Nonempty ((C.restrictRoots hK hsub).TaylorRootCover ε) := by
  obtain ⟨K, hsub, hK, hmass, hlabel, hrem⟩ :=
    C.exists_uniform_source_coordinate_core hF hcomplete hu ha hinj hκ hloss
  exact ⟨K, hK, hsub, hmass,
    (C.restrictRoots hK hsub).exists_taylorRootCover hlabel hrem hε⟩

end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
