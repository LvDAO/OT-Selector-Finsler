import OTSelector.Reconstruction.FinslerOriginalCompletePath

/-! Exact active-cut, finished-target and started-source algebra with the original endpoints. -/

open Set Function MeasureTheory Module Manifold
open scoped ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A clipped prefix has its active value, reached target and strictly started source, including
the literal cases where the observation clock equals either endpoint. -/
theorem clock_clipped_prefix_decomposition
    (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (u : ℝ) :
    f (max a (min u b)) - f a =
      (if a < u ∧ u < b then f u else 0) +
        (if b ≤ u then f b else 0) - (if a < u then f a else 0) := by
  by_cases hua : u ≤ a
  · have hau : ¬a < u := not_lt.mpr hua
    have hbu : ¬b ≤ u := by linarith
    rw [max_eq_left ((min_le_left u b).trans hua)]
    simp [hau, hbu]
  · have hau : a < u := lt_of_not_ge hua
    by_cases hbu : b ≤ u
    · rw [min_eq_right hbu, max_eq_right hab.le]
      simp [hau, hbu, not_lt.mpr hbu]
    · have hub : u < b := lt_of_not_ge hbu
      rw [min_eq_left hub.le, max_eq_right hau.le]
      simp [hau, hub, hbu]

private theorem clock_finished_increment (r c : ℝ) {s t : ℝ} (hst : s ≤ t) :
    (if c ≤ t then r else 0) - (if c ≤ s then r else 0) =
      if s < c ∧ c ≤ t then r else 0 := by
  by_cases hcs : c ≤ s
  · have hct := hcs.trans hst
    simp [hcs, hct, not_lt.mpr hcs]
  · have hsc : s < c := lt_of_not_ge hcs
    by_cases hct : c ≤ t <;> simp [hcs, hsc, hct]

private theorem clock_started_increment (r c : ℝ) {s t : ℝ} (hst : s ≤ t) :
    (if c < t then r else 0) - (if c < s then r else 0) =
      if s ≤ c ∧ c < t then r else 0 := by
  by_cases hcs : c < s
  · have hct := hcs.trans_le hst
    simp [hcs, hct, not_le.mpr hcs]
  · have hsc : s ≤ c := le_of_not_gt hcs
    by_cases hct : c < t <;> simp [hcs, hsc, hct]

/-- A clipped slab is exactly active-at-t minus active-at-s, plus targets in `(s,t]`, minus
sources in `[s,t)`. No regularity, measurability or finite-atom hypothesis is required. -/
theorem clock_clipped_slab_decomposition
    (f : ℝ → ℝ) {a b s t : ℝ} (hab : a < b) (hst : s ≤ t) :
    f (max a (min t b)) - f (max a (min s b)) =
      (if a < t ∧ t < b then f t else 0) -
        (if a < s ∧ s < b then f s else 0) +
        (if s < b ∧ b ≤ t then f b else 0) -
        (if s ≤ a ∧ a < t then f a else 0) := by
  have ht := clock_clipped_prefix_decomposition f hab t
  have hs := clock_clipped_prefix_decomposition f hab s
  have htarget := clock_finished_increment (f b) b hst
  have hsource := clock_started_increment (f a) a hst
  linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The same actual original complete path has the exact four positive cut terms. Its endpoint
values are the unchanged physical source `x` and target `x + m.2`, by the real original path
endpoint identities, for any scalar test function. -/
theorem OriginalSeedConditionalMoments.original_complete_path_clock_cut_decomposition
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 < m.1.2)
    {s t : ℝ} (hst : s ≤ t) (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) :
    φ (originalSeedCompletePath S w x m (max m.1.1 (min t m.1.2))) -
        φ (originalSeedCompletePath S w x m (max m.1.1 (min s m.1.2))) =
      (if m.1.1 < t ∧ t < m.1.2 then φ (originalSeedCompletePath S w x m t) else 0) -
        (if m.1.1 < s ∧ s < m.1.2 then φ (originalSeedCompletePath S w x m s) else 0) +
        (if s < m.1.2 ∧ m.1.2 ≤ t then φ (x + m.2) else 0) -
        (if s ≤ m.1.1 ∧ m.1.1 < t then φ x else 0) := by
  have h := clock_clipped_slab_decomposition
    (fun r ↦ φ (originalSeedCompletePath S w x m r)) hab hst
  simpa only [D.originalSeedCompletePath_target hF hw x m ha hb hab,
    originalSeedCompletePath_source] using h

end OTSelector.Reconstruction
