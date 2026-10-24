import OTSelector.Reconstruction.OriginalRetainedSlabResidualOmitted

/-! The actual smoothed retained current vanishes on every original cube boundary face. -/
open Set Function Filter MeasureTheory Module Manifold Matrix
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- An inner-cube point is at least the true collar width from either corresponding face. -/
theorem collar_le_norm_sub_of_inner_cube_face {ι : Type*} [Fintype ι]
    {R ell : ℝ} {x z : ι → ℝ} (hx : x ∈ haarRootCube ι (R - ell))
    (i : ι) (hz : z i = R ∨ z i = -R) : ell ≤ ‖x - z‖ := by
  have hn := norm_le_pi_norm (x - z) i
  simp only [Real.norm_eq_abs, Pi.sub_apply] at hn
  rcases hz with hz | hz
  · have hh := neg_le_abs (x i - z i)
    have hi := hx.2 i
    dsimp at hi
    rw [hz] at hn hh
    linarith
  · have hh := le_abs_self (x i - z i)
    have hi := hx.1 i
    dsimp at hi
    rw [hz] at hn hh
    linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Literal clock current of the same unchanged length-retained original paths. -/
def originalRetainedSeedPathClockSetCurrent (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell : ℝ)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (B : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  ∫ c in B, ∫ a in originalPathLengthRetained S w R ell,
    η (a.1 + originalSeedPathOffset S w c a.2) • originalSeedClockOccupation S w c a.2
      ∂physicalScenePairKernel scene.1

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- On a single original-scene event every retained smoothed clock current is zero on all
cube faces. This follows from the actual retained paths, with no trace condition supplied. -/
theorem ae_all_originalRetainedCurrent_eq_zero_on_cube_faces
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        (∀ y, 1 ≤ ‖y‖ → η y = 0) → ∀ (B : Set ℝ)
        (z : Fin (finrank ℝ S.covector.ker) → ℝ) (i : Fin (finrank ℝ S.covector.ker)),
        z i = R ∨ z i = -R →
        originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x - z)) B scene = 0 := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hlegal
  intro η hη B z i hz
  unfold originalRetainedSeedPathClockSetCurrent
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro c
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hlegal,
    ae_restrict_mem (measurableSet_originalPathLengthRetained S hF hw R ell)] with a ha hret
  by_cases hc : c ∈ Ico a.2.1.1 a.2.1.2
  · have hpath := D.originalPathLengthRetained_path_mem_innerCube hF hw
      (show 0 ≤ ell by linarith) hR hret ha.1 ha.2.1 (Ico_subset_Icc_self hc)
    have hn := hell.trans (collar_le_norm_sub_of_inner_cube_face hpath i hz)
    rw [originalSeedCompletePath_eq_anchor_add_offset] at hn
    simp only [hη _ hn, zero_smul, Pi.zero_apply]
  · simp only [originalSeedClockOccupation_eq_indicator_velocity, indicator_of_notMem hc,
      smul_zero, Pi.zero_apply]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
