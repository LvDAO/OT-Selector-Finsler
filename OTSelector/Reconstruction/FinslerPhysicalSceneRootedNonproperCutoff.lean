import OTSelector.Reconstruction.FinslerPhysicalSceneRootedFullDisplacement

/-!
# Compact cutoffs for nonproper scene projections

A bounded source window and the actual compact target clock carrier give
explicit compact target cutoffs. Their escape masses are bounded by full
rooted spatial long-edge tails, with a transposed geometric counterpart.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Metric
open OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/-- A compact target cutoff with explicit spatial radius and the unchanged
actual compact target clock carrier. -/
def physicalSceneSpatialClockCutoff (B R : ℝ) (J : Set ℝ) : Set ((ι → ℝ) × ℝ) :=
  closedBall 0 (B + R) ×ˢ J

/-- The full cutoff is compact, including the original target clock. -/
theorem isCompact_physicalSceneSpatialClockCutoff (B R : ℝ) {J : Set ℝ}
    (hJ : IsCompact J) : IsCompact (physicalSceneSpatialClockCutoff (ι := ι) B R J) :=
  (isCompact_closedBall 0 (B + R)).prod hJ

/-- For a measure retaining its actual target clock carrier, escape from the
explicit compact cutoff over a bounded source window forces a long spatial edge. -/
theorem physicalScene_escape_compact_le_longTail
    (π : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    {U : Set (ι → ℝ)} {J : Set ℝ} {B R : ℝ}
    (hU : ∀ x ∈ U, ‖x‖ ≤ B) (hR : 0 ≤ R)
    (hclock : ∀ᵐ e ∂π, e.2.2 ∈ J) :
    π ((U ×ˢ univ) ×ˢ (physicalSceneSpatialClockCutoff B R J)ᶜ) ≤
      π (physicalSceneLongEdgeWindow U (ENNReal.ofReal (R ^ 2))) := by
  apply measure_mono_ae
  filter_upwards [hclock] with e he hp
  refine ⟨hp.1.1, ?_⟩
  have hfar : B + R < ‖e.2.1‖ := by
    by_contra hn
    apply hp.2
    refine ⟨?_, he⟩
    simpa only [mem_closedBall, dist_zero_right] using le_of_not_gt hn
  have htri : ‖e.2.1‖ ≤ ‖e.2.1 - e.1.1‖ + ‖e.1.1‖ := by
    simpa only [sub_add_cancel] using norm_add_le (e.2.1 - e.1.1) e.1.1
  have hr : R ≤ ‖e.2.1 - e.1.1‖ := by linarith [hU e.1.1 hp.1.1]
  exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ hR (norm_nonneg _)).mpr hr)

/-- The transposed explicit compact cutoff controls nonproper target projection
tails without imposing any properness condition on the projection map. -/
theorem physicalScene_target_escape_compact_le_longTail
    (π : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
    {U : Set (ι → ℝ)} {J : Set ℝ} {B R : ℝ}
    (hU : ∀ x ∈ U, ‖x‖ ≤ B) (hR : 0 ≤ R)
    (hclock : ∀ᵐ e ∂π, e.1.2 ∈ J) :
    π ((physicalSceneSpatialClockCutoff B R J)ᶜ ×ˢ (U ×ˢ univ)) ≤
      π {e | e.2.1 ∈ U ∧ ENNReal.ofReal (R ^ 2) ≤
        ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2)} := by
  apply measure_mono_ae
  filter_upwards [hclock] with e he hp
  refine ⟨hp.2.1, ?_⟩
  have hfar : B + R < ‖e.1.1‖ := by
    by_contra hn
    apply hp.1
    refine ⟨?_, he⟩
    simpa only [mem_closedBall, dist_zero_right] using le_of_not_gt hn
  have htri : ‖e.1.1‖ ≤ ‖e.2.1 - e.1.1‖ + ‖e.2.1‖ := by
    simpa only [norm_sub_rev, sub_add_cancel] using norm_add_le (e.1.1 - e.2.1) e.2.1
  have hr : R ≤ ‖e.2.1 - e.1.1‖ := by linarith [hU e.2.1 hp.2.1]
  exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ hR (norm_nonneg _)).mpr hr)

omit [Fintype ι] in
/-- Actual physical target-clock carrying is preserved by the same physical
source restriction, scaling and rooted observation. -/
theorem ae_physicalSceneRootedPlan_target_clock
    {M : Type*} [MeasurableSpace M] (Γ : Measure (M × M))
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {J : Set ℝ} (hJ : MeasurableSet J)
    (hclock : ∀ᵐ p ∂Γ, u p.2 ∈ J) (H : Set M) (N : ℝ) (z : ι → ℝ) :
    ∀ᵐ e ∂physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z, e.2.2 ∈ J := by
  unfold physicalSceneRootedPlan
  apply Measure.ae_smul_measure
  apply (ae_map_iff
    (measurable_physicalSceneRootedObservation coord hcoord u hu z).aemeasurable
    (hJ.preimage measurable_snd.snd)).mpr
  exact ae_restrict_of_ae hclock

/-- The explicit nonproper projection cutoff is bounded by the existing full
rooted long-edge tail of that same physical source-restricted plan. -/
theorem physicalSceneRootedPlan_escape_compact_le_full_longTail
    {M : Type*} [MeasurableSpace M] (Γ : Measure (M × M))
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) {J : Set ℝ} (hJ : MeasurableSet J)
    (hclock : ∀ᵐ p ∂Γ, u p.2 ∈ J) (H : Set M) (N : ℝ) (z : ι → ℝ)
    {U : Set (ι → ℝ)} {B R : ℝ} (hU : ∀ x ∈ U, ‖x‖ ≤ B) (hR : 0 ≤ R) :
    physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      ((U ×ˢ univ) ×ˢ (physicalSceneSpatialClockCutoff B R J)ᶜ) ≤
    physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      (physicalSceneLongEdgeWindow U (ENNReal.ofReal (R ^ 2))) :=
  physicalScene_escape_compact_le_longTail _ hU hR
    (ae_physicalSceneRootedPlan_target_clock Γ coord hcoord u hu hJ hclock H N z)

end OTSelector.Reconstruction
