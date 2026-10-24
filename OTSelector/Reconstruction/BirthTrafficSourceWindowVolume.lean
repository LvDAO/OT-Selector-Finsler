import OTSelector.Reconstruction.BirthTrafficPhysicalHaarScale
import OTSelector.Reconstruction.PhaseSourceCellPullback

/-! The deterministic original source window for bounded birth-phase traffic
has the exact physical Haar Jacobian and its same-residue rank power. -/
open Set Function Matrix MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual bounded-phase source window in original physical spatial
coordinates, using the same canonical birth frame and physical radius. -/
def birthTrafficSpatialWindow (G : Matrix ι ι ℝ) (t s R : ℝ) : Set (ι → ℝ) :=
  (Matrix.toLin' (birthTrafficSpatialFrame G t s)) '' Metric.closedBall 0 R

/-- The actual physical source window is compact at every fixed scale. -/
theorem isCompact_birthTrafficSpatialWindow (G : Matrix ι ι ℝ) (t s R : ℝ) :
    IsCompact (birthTrafficSpatialWindow G t s R) :=
  (isCompact_closedBall _ _).image (Matrix.toLin' (birthTrafficSpatialFrame G t s)).continuous_of_finiteDimensional

/-- Its original Haar volume is exactly its own canonical frame Jacobian. -/
theorem volume_birthTrafficSpatialWindow (G : Matrix ι ι ℝ) (t s R : ℝ) :
    volume (birthTrafficSpatialWindow G t s R) =
      ENNReal.ofReal |(birthTrafficSpatialFrame G t s).det| *
        volume (Metric.closedBall (0 : ι → ℝ) R) := by
  rw [birthTrafficSpatialWindow, Measure.addHaar_image_linearMap, LinearMap.det_toLin']

/-- The physical birth source-window volume is bounded by the same original
residue-rank power, uniformly in the elapsed-time scale `s`. -/
theorem exists_birthTrafficSpatialWindow_volume_bound
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) (hq : 0 < Fintype.card ι) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t s : ℝ}, 0 < t → t ≤ 1 → 0 < s →
      volume (birthTrafficSpatialWindow G t s R) ≤
        ENNReal.ofReal (C * (t ^ (G.rank + 1))⁻¹) := by
  obtain ⟨Cf, hCf, hframe⟩ := exists_birthTrafficSpatialFrame_det_bound hG hq
  let V : ℝ := (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hVfin : volume (Metric.closedBall (0 : ι → ℝ) R) ≠ ∞ :=
    (isCompact_closedBall _ _).measure_ne_top
  have hVeq : volume (Metric.closedBall (0 : ι → ℝ) R) = ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal hVfin).symm
  refine ⟨Cf * V + 1, by positivity, fun {t s} ht ht1 hs ↦ ?_⟩
  rw [volume_birthTrafficSpatialWindow, hVeq, ← ENNReal.ofReal_mul (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Cf * (t ^ (G.rank + 1))⁻¹) * V :=
      mul_le_mul_of_nonneg_right (hframe t s ht ht1 hs) hV
    _ ≤ _ := by nlinarith [inv_nonneg.mpr (pow_nonneg ht.le (G.rank + 1))]

end OTSelector.Reconstruction
