import OTSelector.Reconstruction.OriginalRegularClockRegionGeometry
import OTSelector.Reconstruction.OriginalOldRegularClockLegs

/-! Literal original clock masks produce compact regular strips and positive
old reference legs directly from their original paired-clock inequalities. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- All four literal regular masks lie in one internally chosen compact
original clock strip. The strip exists for every positive cutoff and gap. -/
theorem exists_original_regular_masks_compact_strip
    {ε gap : ℝ} (hε : 0 < ε) (hgap : 0 < gap) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ Ioo D.lo D.hi ∧
      ∀ {i : Fin 8}, (i = 1 ∨ i = 3 ∨ i = 5 ∨ i = 7) →
      ∀ z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ,
      originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε i z ≠ 0 →
      gap ≤ z.1.1.2 - z.1.1.1 → z.2 - (S.level : ℝ) ∈ J := by
  let d := min (min ε (gap / 2)) ((D.hi - D.lo) / 4)
  have hspan := D.support.lt
  have hd : 0 < d := lt_min (lt_min hε (half_pos hgap)) (by linarith)
  have hds : d ≤ (D.hi - D.lo) / 4 := min_le_right _ _
  have hdm : d ≤ min ε (gap / 2) := min_le_left _ _
  refine ⟨Icc (D.lo + d) (D.hi - d), isCompact_Icc,
    Icc_subset_Ioo (by linarith) (by linarith), ?_⟩
  intro i hi z hz hgz
  have hc := original_regularClock_mask_compact_strip hi hz hgz
  constructor <;> linarith [hc.1, hc.2]

/-- The actual old regular masks produce the two original positive reference
legs uniformly, including when an original source or target approaches a
focal endpoint. These bounds are consequences of the literal mask. -/
theorem exists_original_oldRegular_mask_reference_legs
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {ε gap : ℝ} (hε : 0 < ε) (hgap : 0 < gap) :
    ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧ ∀ {i : Fin 8}, (i = 3 ∨ i = 7) →
      ∀ z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ,
      originalClockTrafficRegionMask (D.lo + S.level) (D.hi + S.level) ε i z ≠ 0 →
      gap ≤ z.1.1.2 - z.1.1.1 → ∀ r : ℝ, |r - z.2| ≤ δ →
      r - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
        (originalSeedClockCompliance S w z.1.1.1 r - κ • 1).PosSemidef ∧
        (originalSeedClockCompliance S w r z.1.1.2 - κ • 1).PosSemidef := by
  let e := min ε gap / 2
  have he : 0 < e := half_pos (lt_min hε hgap)
  obtain ⟨κ, hκ, hlegs⟩ := D.exists_original_uniform_reference_legs hF hw he
  refine ⟨κ * (e / 2), e / 2, by positivity, half_pos he, ?_⟩
  intro i hi z hz hgz r hr
  obtain ⟨hl, hh, ha, hb, _⟩ :=
    (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hz
  have htimes := original_oldRegularClock_mask_leg_bounds hi hz hgz
  exact hlegs ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    htimes.1 htimes.2 hr

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
