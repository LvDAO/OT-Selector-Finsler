import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalNonproper
import OTSelector.MeasureTheory.LimitMarginalDefect

/-!
# Genuine compact exhaustions for actual projection tails

The explicit spatial and actual clock cutoffs sit inside a compact exhaustion
of the full formal point space. Its canonical compactly supported tests equal
one on those cutoffs, with constants supplied by the original compact carriers
and each compact source test.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Metric TopologicalSpace
open OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Expanding norm balls with a specified initial spatial or clock radius. -/
def physicalSceneNormBallExhaustion (X : Type*) [NormedAddCommGroup X] [ProperSpace X]
    (W : ℝ) : CompactExhaustion X where
  toFun n := closedBall 0 (|W| + n + 1)
  isCompact' n := isCompact_closedBall _ _
  subset_interior_succ' n :=
    (closedBall_subset_ball (by push_cast; linarith)).trans ball_subset_interior_closedBall
  iUnion_eq' := iUnion_eq_univ_iff.mpr fun x ↦ by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    refine ⟨n, ?_⟩
    simp only [mem_closedBall, dist_zero_right]
    linarith [abs_nonneg W]

variable {ι : Type*} [Fintype ι]

/-- A genuine compact exhaustion of the entire formal point space, with
independently specified initial spatial and clock radii. -/
def physicalSceneSpatialClockExhaustion (W C : ℝ) : CompactExhaustion ((ι → ℝ) × ℝ) where
  toFun n := physicalSceneNormBallExhaustion (ι → ℝ) W n ×ˢ
    physicalSceneNormBallExhaustion ℝ C n
  isCompact' n := (physicalSceneNormBallExhaustion _ W |>.isCompact n).prod
    (physicalSceneNormBallExhaustion ℝ C |>.isCompact n)
  subset_interior_succ' n := by
    rw [interior_prod_eq]
    exact prod_mono ((physicalSceneNormBallExhaustion _ W).subset_interior_succ n)
      ((physicalSceneNormBallExhaustion ℝ C).subset_interior_succ n)
  iUnion_eq' := iUnion_eq_univ_iff.mpr fun x ↦ by
    obtain ⟨n, hn⟩ := (physicalSceneNormBallExhaustion (ι → ℝ) W).exists_mem x.1
    obtain ⟨m, hm⟩ := (physicalSceneNormBallExhaustion ℝ C).exists_mem x.2
    exact ⟨max n m, (physicalSceneNormBallExhaustion _ W).subset (le_max_left _ _) hn,
      (physicalSceneNormBallExhaustion ℝ C).subset (le_max_right _ _) hm⟩

/-- Each actual geometric target cutoff lies inside the corresponding member
of a genuine exhaustion once the unchanged compact clock carrier is bounded. -/
theorem physicalSceneSpatialClockCutoff_subset_exhaustion
    (W C : ℝ) {J : Set ℝ} (hJ : ∀ t ∈ J, ‖t‖ ≤ |C| + 1) (n : ℕ) :
    physicalSceneSpatialClockCutoff (ι := ι) |W| (n + 1) J ⊆
      physicalSceneSpatialClockExhaustion W C n := by
  intro x hx
  refine ⟨?_, ?_⟩
  · change x.1 ∈ closedBall 0 (|W| + (n : ℝ) + 1)
    simpa only [add_assoc] using hx.1
  · change x.2 ∈ closedBall 0 (|C| + (n : ℝ) + 1)
    simp only [mem_closedBall, dist_zero_right]
    exact (hJ x.2 hx.2).trans (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)

/-- The canonical compactly supported cutoff is identically one on the actual
geometric cutoff. This is the needed connection to vague compact tests. -/
theorem physicalScene_exhaustionCutoff_eq_one_on_spatialClockCutoff
    (W C : ℝ) {J : Set ℝ} (hJ : ∀ t ∈ J, ‖t‖ ≤ |C| + 1) (n : ℕ) :
    EqOn (LocalFiniteMeasure.exhaustionCutoff (physicalSceneSpatialClockExhaustion W C) n)
      1 (physicalSceneSpatialClockCutoff (ι := ι) |W| (n + 1) J) :=
  fun _ hx ↦ LocalFiniteMeasure.exhaustionCutoff_eq_one _ _
    (physicalSceneSpatialClockCutoff_subset_exhaustion W C hJ n hx)

/-- Every compact source test and actual compact target clock image supply
finite spatial and clock constants for the explicit cutoff production. -/
theorem exists_physicalScene_compact_test_clock_bounds
    (f : C_c((ι → ℝ) × ℝ, ℝ)) {J : Set ℝ} (hJ : IsCompact J) :
    ∃ W C : ℝ, (∀ x ∈ tsupport f, ‖x.1‖ ≤ |W|) ∧
      (∀ t ∈ J, ‖t‖ ≤ |C| + 1) := by
  obtain ⟨W, hW⟩ := (f.hasCompactSupport.isCompact.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hJ.isBounded.exists_norm_le
  refine ⟨W, C, ?_, ?_⟩
  · exact fun x hx ↦ (hW x.1 (mem_image_of_mem Prod.fst hx)).trans (le_abs_self W)
  · exact fun t ht ↦ (hC t ht).trans ((le_abs_self C).trans (by linarith))

/-- The compact spatial source window of an actual compact source test. -/
def physicalSceneTestSpatialWindow (f : C_c((ι → ℝ) × ℝ, ℝ)) : Set (ι → ℝ) :=
  Prod.fst '' tsupport f

omit [Fintype ι] in
/-- The source test's entire spatial window is compact. -/
theorem isCompact_physicalSceneTestSpatialWindow (f : C_c((ι → ℝ) × ℝ, ℝ)) :
    IsCompact (physicalSceneTestSpatialWindow f) := f.hasCompactSupport.isCompact.image continuous_fst

/-- The exact nonproper escape rectangle of the canonical source test and
exhaustion is controlled by the actual full rooted long-edge window. -/
theorem physicalScene_source_test_escape_exhaustion_le_longTail
    (π : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    (f : C_c((ι → ℝ) × ℝ, ℝ)) (W C : ℝ) {J : Set ℝ}
    (hf : ∀ x ∈ tsupport f, ‖x.1‖ ≤ |W|)
    (hJ : ∀ t ∈ J, ‖t‖ ≤ |C| + 1)
    (hclock : ∀ᵐ e ∂π, e.2.2 ∈ J) (n : ℕ) :
    π (tsupport f ×ˢ (physicalSceneSpatialClockExhaustion W C n)ᶜ) ≤
      π (physicalSceneLongEdgeWindow (physicalSceneTestSpatialWindow f)
        (ENNReal.ofReal (((n : ℝ) + 1) ^ 2))) := by
  have hsub : tsupport f ×ˢ (physicalSceneSpatialClockExhaustion (ι := ι) W C n)ᶜ ⊆
      (physicalSceneTestSpatialWindow f ×ˢ (univ : Set ℝ)) ×ˢ
        (physicalSceneSpatialClockCutoff (ι := ι) |W| (n + 1) J)ᶜ := by
    intro e he
    exact ⟨⟨mem_image_of_mem Prod.fst he.1, mem_univ _⟩,
      fun h ↦ he.2 (physicalSceneSpatialClockCutoff_subset_exhaustion W C hJ n h)⟩
  exact (measure_mono hsub).trans
    (physicalScene_escape_compact_le_longTail π (by
      rintro x ⟨p, hp, rfl⟩
      exact hf p hp) (by positivity) hclock)

end OTSelector.Reconstruction
