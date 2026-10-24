import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell
import OTSelector.MeasureTheory.Integral.WeightedCountSquare

/-! The actual complete-path kernel's contributor count produces its traffic-square
majorant. No finiteness of weighted traffic is assumed before Campbell/Tonelli. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A literal same-scene original contributor count and bounded per-edge traffic
produce the complete-path weighted square bound. The weight is its own original
Palm mark and need not be independent of either endpoint or displacement. -/
theorem originalCompletePath_traffic_sq_le_of_count
    {q : ℕ} (s : LegalMarkedOptimalInputScene q)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (h : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (p : PhysicalPairPalmMark (Fin q) → ℝ≥0∞) (hp : ∀ m, p m ≠ ∞)
    (V : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))
    {B K W C : ℝ≥0∞} (hW : W ≠ ∞) (hC : C ≠ ∞)
    (hsupport : (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume).support ⊆ V)
    (huB : ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict V,
      (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ B)
    (hcount : physicalScenePairKernel s.1 V ≤ K * W)
    (hweight : ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict V, W ≤ C * p a.2) :
    (legalMarkedCompletePathTraffic q d h f s) ^ 2 ≤ B * K * C *
      legalMarkedCompletePathTraffic q d h (fun m ↦ p m.1 * f m) s := by
  have hbound := OTSelector.Probability.setLIntegral_sq_le_of_count_and_weight
    (p := fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦ p a.2)
    hW hC huB hcount hweight
  rw [setLIntegral_eq_of_support_subset hsupport] at hbound
  have hmono : (∫⁻ a in V, p a.2 *
      (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume)
      ∂physicalScenePairKernel s.1) ≤
      ∫⁻ a, p a.2 * (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume)
        ∂physicalScenePairKernel s.1 :=
    lintegral_mono' Measure.restrict_le_self (fun _ ↦ le_rfl)
  have heq : (∫⁻ a, p a.2 *
      (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume)
      ∂physicalScenePairKernel s.1) =
      legalMarkedCompletePathTraffic q d h (fun m ↦ p m.1 * f m) s := by
    apply lintegral_congr
    intro a
    rw [← lintegral_const_mul' _ _ (hp a.2)]
    apply lintegral_congr
    intro r
    ac_rfl
  change (legalMarkedCompletePathTraffic q d h f s) ^ 2 ≤ _ at hbound
  calc
    _ ≤ _ := hbound
    _ ≤ B * K * C *
        (∫⁻ a, p a.2 * (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume)
          ∂physicalScenePairKernel s.1) := by gcongr
    _ = _ := by rw [heq]

end OTSelector.Reconstruction
