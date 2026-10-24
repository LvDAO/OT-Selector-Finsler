import OTSelector.Reconstruction.OriginalMinimizerPrefixCurrentCentering
import OTSelector.Reconstruction.OriginalTargetPortCountExpectation

/-! Actual clock occupation, clipped path intervals, and the original one-path FTC. -/
open Set Function Filter MeasureTheory Module Manifold Matrix
open scoped ENNReal Topology ContDiff Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A real clock slab restricted to the actual half-open edge lifetime is exactly the
clipped original interval. Endpoint conventions agree under the true Lebesgue integral. -/
theorem integral_Ioc_Ico_indicator_eq_clipped
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t) :
    (∫ c in Ioc s t, (Ico a b).indicator f c) =
      ∫ c in max a (min s b)..max a (min t b), f c := by
  have hclip : max a (min s b) ≤ max a (min t b) :=
    max_le_max_left a (min_le_min_right b hst)
  have hsets : Ioc s t ∩ Ioc a b =
      Ioc (max a (min s b)) (max a (min t b)) := by
    ext c
    simp only [mem_inter_iff, mem_Ioc]
    grind
  calc
    _ = ∫ c in Ico a b, (Ioc s t).indicator f c := by
      rw [integral_indicator measurableSet_Ico, integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ico,
        Measure.restrict_restrict measurableSet_Ioc, inter_comm]
    _ = ∫ c in Ioc a b, (Ioc s t).indicator f c := integral_Ico_eq_integral_Ioc
    _ = ∫ c in Ioc (max a (min s b)) (max a (min t b)), f c := by
      rw [integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc, hsets]
    _ = _ := (intervalIntegral.integral_of_le hclip).symm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual indicator clock occupation gives exactly the original clipped path derivative
integral. The full path position and unchanged pair momentum both remain literal. -/
theorem integral_originalClockOccupation_testDerivative_eq_clipped
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (hab : m.1.1 ≤ m.1.2) {s t : ℝ} (hst : s ≤ t)
    (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) :
    (∫ c in Ioc s t, fderiv ℝ φ (originalSeedCompletePath S w x m c)
        (originalSeedClockOccupation S w c m)) =
      ∫ c in max m.1.1 (min s m.1.2)..max m.1.1 (min t m.1.2),
        fderiv ℝ φ (originalSeedCompletePath S w x m c)
          (originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m) := by
  have heq : (fun c ↦ fderiv ℝ φ (originalSeedCompletePath S w x m c)
      (originalSeedClockOccupation S w c m)) = (Ico m.1.1 m.1.2).indicator
        (fun c ↦ fderiv ℝ φ (originalSeedCompletePath S w x m c)
          (originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ originalSeedPairMomentum S w m)) := by
    funext c
    rw [originalSeedClockOccupation_eq_indicator_velocity]
    by_cases hc : c ∈ Ico m.1.1 m.1.2 <;> simp [hc]
  rw [heq]
  exact integral_Ioc_Ico_indicator_eq_clipped _ hab hst

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The unchanged original indicator occupation satisfies the true one-path FTC between its
actual clipped clock cuts, using the original compliance velocity and endpoint positions. -/
theorem integral_originalClockOccupation_testDerivative_eq_endpoints
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : m.1.1 ≤ m.1.2)
    {s t : ℝ} (hst : s ≤ t)
    {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ c in Ioc s t, fderiv ℝ φ (originalSeedCompletePath S w x m c)
      (originalSeedClockOccupation S w c m)) =
      φ (originalSeedCompletePath S w x m (max m.1.1 (min t m.1.2))) -
        φ (originalSeedCompletePath S w x m (max m.1.1 (min s m.1.2))) := by
  rw [integral_originalClockOccupation_testDerivative_eq_clipped S w x m hab hst]
  exact D.integral_originalSeedCompletePath_slab_eq_endpoints hF hw x m ha hb hab hst hφ

/-- The original infinite scene pair kernel's actual clock-occupation readout is exactly its
previous weak slab readout. The first plan is not required to be a finite edge family. -/
theorem ae_all_originalClockSlab_testDerivative_eq_weakSlab
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (s t : ℝ), s ≤ t →
        (∫ a, (∫ c in Ioc s t,
          fderiv ℝ φ (a.1 + originalSeedPathOffset S w c a.2)
            (originalSeedClockOccupation S w c a.2) ∂volume)
          ∂physicalScenePairKernel scene.1) = originalSeedPathWeakSlabReadout S w φ s t scene := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hscene
  intro φ s t hst
  unfold originalSeedPathWeakSlabReadout
  apply integral_congr_ae
  filter_upwards [hscene] with a ha
  simpa only [originalSeedCompletePath_eq_anchor_add_offset] using
    integral_originalClockOccupation_testDerivative_eq_clipped S w a.1 a.2 ha.2.2.le hst φ

/-- On one full-measure set of genuine original scenes, every C¹ weak clock slab is the
actual clipped target-minus-source path evaluation integrated over the same infinite pair
kernel. All cut positions remain on the unchanged original complete paths. -/
theorem ae_all_originalClockSlab_testDerivative_eq_endpoints
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ), ContDiff ℝ 1 φ →
        ∀ (s t : ℝ), s ≤ t →
        (∫ a, (∫ c in Ioc s t,
          fderiv ℝ φ (a.1 + originalSeedPathOffset S w c a.2)
            (originalSeedClockOccupation S w c a.2) ∂volume)
          ∂physicalScenePairKernel scene.1) =
          ∫ a, (φ (originalSeedCompletePath S w a.1 a.2 (max a.2.1.1 (min t a.2.1.2))) -
            φ (originalSeedCompletePath S w a.1 a.2 (max a.2.1.1 (min s a.2.1.2))))
            ∂physicalScenePairKernel scene.1 := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hscene
  intro φ hφ s t hst
  apply integral_congr_ae
  filter_upwards [hscene] with a ha
  simpa only [originalSeedCompletePath_eq_anchor_add_offset] using
    D.integral_originalClockOccupation_testDerivative_eq_endpoints hF hw a.1 a.2
      ha.1 ha.2.1 ha.2.2.le hst hφ

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
