import OTSelector.Reconstruction.BirthNormalizedShortLegs

/-! # The enlarged opposite focal segment dominates the same birth matrix -/
open Set Matrix MeasureTheory
open scoped Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuine relative segment beyond every birth cut has focal-scale compliance.
This is the actual integral on [4t,8t], before any extension to a full original leg. -/
theorem positivePole_opposite_segment_lower
    {W : ℝ → Matrix ι ι ℝ} {G : Matrix ι ι ℝ} {ε c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (htε : 8 * t < ε)
    (hW : ContinuousOn W (Ioo 0 ε))
    (hlower : ∀ r ∈ Ioo 0 ε, (W r - c • ((r ^ 2)⁻¹ • G + 1)).PosSemidef) :
    ((∫ r in (4 * t)..(8 * t), W r) - (c / 8) • focalResidueScale G t).PosSemidef := by
  have h := intervalIntegral_positivePole_lower (G := G)
    (by linarith : 0 < 4 * t) (by linarith : 4 * t ≤ 8 * t) htε hW hlower
  have hinv : (4 * t)⁻¹ - (8 * t)⁻¹ = t⁻¹ / 8 := by field_simp; ring
  have hlen : 8 * t - 4 * t = 4 * t := by ring
  rw [hinv, hlen] at h
  have hp := h.add (Matrix.PosSemidef.one.smul
    (show 0 ≤ (31 / 8 : ℝ) * c * t by positivity))
  convert hp using 1
  unfold focalResidueScale
  module

end OTSelector.Reconstruction
