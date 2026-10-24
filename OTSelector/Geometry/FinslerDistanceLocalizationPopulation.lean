import OTSelector.Geometry.FinslerDistanceLocalizationCompact
import OTSelector.Reconstruction.FinslerPopulationLocalPressureCore

/-!
# Original population cores localize the actual distance slack

The retained continuous original labels give compact physical endpoint domains.
Different root pieces and separated same-piece labels have one positive cost gap.
The actual uniform quadratic remainder also supplies a common local coercivity
constant and radius, in exactly the original coefficient coordinates.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Function OTSelector.Geometry
open scoped ENNReal
namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)

/-- The actual original endpoint over one retained root and scalar time. -/
def corePoint (i : Fin D.haar.continuous.count) (z : (ℚ → M) × ℝ) : M :=
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  S.curve (populationSeedRootLabelValue S a z.1) (z.2 - S.level)

/-- The entire compact scalar window over a retained original root core. -/
def corePointDomain (i : Fin D.haar.continuous.count) : Set ((ℚ → M) × ℝ) :=
  (D.haar.continuous.coefficient i).roots ×ˢ
    Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
      ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ)

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
/-- The retained physical endpoint parameter domain is compact. -/
theorem isCompact_corePointDomain (i : Fin D.haar.continuous.count) :
    IsCompact (D.corePointDomain i) :=
  (D.haar.continuous.coefficient i).roots_compact.prod isCompact_Icc

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M] in
/-- The actual endpoint map varies continuously on the retained physical domain. -/
theorem continuousOn_corePoint (i : Fin D.haar.continuous.count) :
    ContinuousOn (D.corePoint i) (D.corePointDomain i) := by
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  have hl : ContinuousOn (populationSeedRootLabelValue S a)
      (D.haar.continuous.coefficient i).roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  have hlabels : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      populationSeedRootLabelValue S a z ∈ S.labels := by
    intro z hz
    exact (D.haar.intensity i).labels_subset ⟨z,
      by simpa only [D.haar.intensity_roots i] using hz, rfl⟩
  intro z hz
  exact (S.continuousAt_joint_curve (S.labels_subset (hlabels z.1 hz.1))).comp_continuousWithinAt
    ((hl.comp continuous_fst.continuousOn (fun q hq ↦ hq.1) z hz).prodMk
      ((continuous_snd.sub continuous_const).continuousWithinAt))

/-- Original active calibration and the atlas root identity hold at every point
of a retained physical domain, including both scalar window endpoints. -/
theorem corePoint_root_data (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count) {z : (ℚ → M) × ℝ}
    (hz : z ∈ D.corePointDomain i) :
    D.corePoint i z ∈ F.potentialRegularDomain u ∧ a (D.corePoint i z) = z.1 := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  have hzI : z.1 ∈ (D.haar.intensity i).roots := by
    simpa only [D.haar.intensity_roots i] using hz.1
  have hl : populationSeedRootLabelValue S a z.1 ∈ S.labels :=
    (D.haar.intensity i).labels_subset ⟨z.1, hzI, rfl⟩
  have ht := (D.haar.continuous.coefficient i).calibrated_label_interval
    hF hcomplete hu ha hinj hz.1
    (show z.2 - (S.level : ℝ) ∈ Icc
      (((D.haar.continuous.coefficient i).window.val.1 : ℝ) - S.level)
      (((D.haar.continuous.coefficient i).window.val.2.1 : ℝ) - S.level) from
        ⟨sub_le_sub_right hz.2.1 _, sub_le_sub_right hz.2.2 _⟩)
  obtain ⟨hreg, hroot⟩ := S.active_point_root_data hF hcomplete hu horder hl ht
  exact ⟨hreg, hroot.trans ((D.haar.intensity i).root_identity z.1 hzI)⟩

/-- The retained root and scalar window produce legal original seed data. -/
theorem corePoint_seed_data (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {z : (ℚ → M) × ℝ}
    (hz : z ∈ D.corePointDomain i) :
    let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
    populationSeedRootLabelValue S a z.1 ∈ S.labels ∧
      z.2 - S.level ∈ interior (S.calibrationTimes (populationSeedRootLabelValue S a z.1)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  have hzI : z.1 ∈ (D.haar.intensity i).roots := by
    simpa only [D.haar.intensity_roots i] using hz.1
  refine ⟨(D.haar.intensity i).labels_subset ⟨z.1, hzI, rfl⟩, ?_⟩
  exact (D.haar.continuous.coefficient i).calibrated_label_interval hF hcomplete hu ha hinj
    hz.1 ⟨sub_le_sub_right hz.2.1 _, sub_le_sub_right hz.2.2 _⟩

/-- A positive label separation inside one retained piece forces a uniform
positive original distance slack across its whole scalar window. -/
theorem exists_samePiece_distance_slack_gap (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0, ∀ x ∈ D.corePointDomain i, ∀ y ∈ D.corePointDomain i,
      radius ≤ ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a y.1 -
        populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a x.1‖ →
      gap ≤ (F.lengthEDist (D.corePoint i x) (D.corePoint i y)).toReal -
        u (D.corePoint i y) + u (D.corePoint i x) := by
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  let f : (ℚ → M) × ℝ → S.covector.ker × ℝ := fun z ↦
    (populationSeedRootLabelValue S a z.1, z.2 - S.level)
  have hl : ContinuousOn (populationSeedRootLabelValue S a)
      (D.haar.continuous.coefficient i).roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  have hf : ContinuousOn f (D.corePointDomain i) :=
    (hl.comp continuous_fst.continuousOn (fun q hq ↦ hq.1)).prodMk
      ((continuous_snd.sub continuous_const).continuousOn)
  have hK := (D.isCompact_corePointDomain i).image_of_continuousOn hf
  have hdata : ∀ q ∈ f '' D.corePointDomain i,
      q.1 ∈ S.labels ∧ q.2 ∈ interior (S.calibrationTimes q.1) := by
    rintro q ⟨z, hz, rfl⟩
    exact D.corePoint_seed_data hF hcomplete hu ha hinj i hz
  obtain ⟨gap, hgap, hbound⟩ := S.exists_uniform_distance_slack_gap hF hcomplete hu
    (hK.prod hK) (fun p hp ↦ ⟨(hdata _ hp.1).1, (hdata _ hp.2).1⟩)
    (fun p hp ↦ ⟨(hdata _ hp.1).2, (hdata _ hp.2).2⟩) hradius
  exact ⟨gap, hgap, fun x hx y hy hsep ↦
    hbound (f x, f y) ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩ hsep⟩

/-- Different retained root pieces have a positive uniform original distance
slack on their entire compact scalar windows. -/
theorem exists_crossPiece_distance_slack_gap (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {i j : Fin D.haar.continuous.count} (hij : i ≠ j) :
    ∃ gap > 0, ∀ x ∈ D.corePointDomain i, ∀ y ∈ D.corePointDomain j,
      gap ≤ (F.lengthEDist (D.corePoint i x) (D.corePoint j y)).toReal -
        u (D.corePoint j y) + u (D.corePoint i x) := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨gap, hgap, hbound⟩ := exists_distance_slack_gap_of_compact
    ((D.isCompact_corePointDomain i).prod (D.isCompact_corePointDomain j))
    ((D.continuousOn_corePoint i).comp continuous_fst.continuousOn (fun _ h ↦ h.1))
    ((D.continuousOn_corePoint j).comp continuous_snd.continuousOn (fun _ h ↦ h.2)) hu
    (s := fun _ ↦ (1 : ℝ)) continuousOn_const (fun p hp hzero ↦ by
      obtain ⟨hx, hrx⟩ := D.corePoint_root_data hF hcomplete hu ha hinj horder i hp.1
      obtain ⟨hy, hry⟩ := D.corePoint_root_data hF hcomplete hu ha hinj horder j hp.2
      simp only [Function.comp_apply] at hzero
      have heq := ((horder _ hx _ hy).mpr (by linarith)).1
      rw [hrx, hry] at heq
      exact False.elim (Set.disjoint_left.mp (D.haar.continuous.disjoint hij)
        hp.1.1 (heq.symm ▸ hp.2.1))) (r := 1) zero_lt_one
  exact ⟨gap, hgap, fun x hx y hy ↦ hbound (x, y) ⟨hx, hy⟩ le_rfl⟩
 
/-- One positive original cost gap works for all distinct retained pieces. -/
theorem exists_uniform_crossPiece_distance_slack_gap (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∃ gap > 0, ∀ i j : Fin D.haar.continuous.count, i ≠ j →
      ∀ x ∈ D.corePointDomain i, ∀ y ∈ D.corePointDomain j,
        gap ≤ (F.lengthEDist (D.corePoint i x) (D.corePoint j y)).toReal -
          u (D.corePoint j y) + u (D.corePoint i x) := by
  classical
  have hlocal (p : Fin D.haar.continuous.count × Fin D.haar.continuous.count) :
      ∃ gap > 0, p.1 ≠ p.2 → ∀ x ∈ D.corePointDomain p.1,
        ∀ y ∈ D.corePointDomain p.2,
          gap ≤ (F.lengthEDist (D.corePoint p.1 x) (D.corePoint p.2 y)).toReal -
            u (D.corePoint p.2 y) + u (D.corePoint p.1 x) := by
    by_cases hp : p.1 = p.2
    · exact ⟨1, zero_lt_one, fun hn ↦ (hn hp).elim⟩
    · obtain ⟨gap, hgap, hb⟩ := D.exists_crossPiece_distance_slack_gap
        hF hcomplete hu ha hinj horder hp
      exact ⟨gap, hgap, fun _ ↦ hb⟩
  choose gap hgap hbound using hlocal
  obtain ⟨c, hc, hle⟩ := (isCompact_univ : IsCompact
    (univ : Set (Fin D.haar.continuous.count × Fin D.haar.continuous.count))).exists_forall_le'
      (f := gap) continuous_of_discreteTopology.continuousOn (fun p _ ↦ hgap p)
  exact ⟨c, hc, fun i j hij x hx y hy ↦
    (hle (i, j) (mem_univ _)).trans (hbound (i, j) hij x hx y hy)⟩

/-- One actual cost gap controls both cross-piece edges and every separated
same-piece edge across the entire finite original population core. -/
theorem exists_uniform_far_distance_slack_gap (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ gap > 0,
      (∀ i j : Fin D.haar.continuous.count, i ≠ j →
        ∀ x ∈ D.corePointDomain i, ∀ y ∈ D.corePointDomain j,
          gap ≤ (F.lengthEDist (D.corePoint i x) (D.corePoint j y)).toReal -
            u (D.corePoint j y) + u (D.corePoint i x)) ∧
      (∀ i : Fin D.haar.continuous.count,
        ∀ x ∈ D.corePointDomain i, ∀ y ∈ D.corePointDomain i,
          radius ≤ ‖populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a y.1 -
            populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a x.1‖ →
          gap ≤ (F.lengthEDist (D.corePoint i x) (D.corePoint i y)).toReal -
            u (D.corePoint i y) + u (D.corePoint i x)) := by
  classical
  choose gap hgap hbound using fun i ↦
    D.exists_samePiece_distance_slack_gap hF hcomplete hu ha hinj i hradius
  obtain ⟨c, hc, hle⟩ := (isCompact_univ : IsCompact
    (univ : Set (Fin D.haar.continuous.count))).exists_forall_le'
      (f := gap) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hgap i)
  obtain ⟨d, hd, hcross⟩ := D.exists_uniform_crossPiece_distance_slack_gap
    hF hcomplete hu ha hinj horder
  refine ⟨min c d, lt_min hc hd, ?_, ?_⟩
  · intro i j hij x hx y hy
    exact (min_le_right c d).trans (hcross i j hij x hx y hy)
  · intro i x hx y hy hsep
    exact ((min_le_left c d).trans (hle i (mem_univ i))).trans (hbound i x hx y hy hsep)

/-- The actual source distance deficit controls the squared displacement in the
same basis as the original inverse compliance, uniformly over every retained piece. -/
theorem exists_uniform_source_coercivity (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    ∃ m > 0, ∃ radius > 0, ∀ i : Fin D.haar.continuous.count,
      let C := D.haar.continuous.coefficient i
      let S := (P C.seedIndex).seed
      let bW := Module.finBasis ℝ S.covector.ker
      ∀ z ∈ C.roots, ∀ t ∈ C.window.region, ∀ v : Fin (Module.finrank ℝ S.covector.ker) → ℝ,
        ‖v‖ < radius →
        populationSeedRootLabelValue S a z + bW.equivFun.symm v ∈
          coefficientWindowLabels S C.window →
        m * ‖v‖ ^ 2 ≤ populationSeedPairDeficit S t
          (populationSeedRootLabelValue S a z,
            populationSeedRootLabelValue S a z + bW.equivFun.symm v) := by
  classical
  choose m hm hb using fun i ↦ (D.haar.continuous.coefficient i).exists_quadratic_lower_bound
  obtain ⟨c, hc, hle⟩ := (isCompact_univ : IsCompact
    (univ : Set (Fin D.haar.continuous.count))).exists_forall_le'
      (f := m) continuous_of_discreteTopology.continuousOn (fun i _ ↦ hm i)
  obtain ⟨radius, hradius, hrem⟩ := D.source_remainder hF hcomplete hu ha hinj
    (c / 2) (half_pos hc)
  refine ⟨c / 2, half_pos hc, radius, hradius, ?_⟩
  intro i
  dsimp only
  intro z hz t ht v hv hallowed
  have he := (abs_le.mp (hrem i z hz t ht v hv hallowed)).1
  have hq := hb i z hz t ht v
  have hlow := mul_le_mul_of_nonneg_right (hle i (mem_univ i)) (sq_nonneg ‖v‖)
  linarith

end PopulationLocalPressureCore
end OTSelector.Reconstruction
