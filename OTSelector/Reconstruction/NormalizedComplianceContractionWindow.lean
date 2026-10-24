import OTSelector.Reconstruction.OriginalFocalComplianceOperatorCurve

/-!
# An internally chosen contractive relative clock window

The original mobility bound and the produced field Lipschitz constant determine
a positive relative window. Its actual operator family is uniformly contractive;
no independent small-mobility assumption remains.
-/

open Set
noncomputable section
namespace OTSelector.Reconstruction

/-- A positive relative window chosen from the actual mobility and field constants. -/
def normalizedComplianceWindowFraction (B L : ℝ) : ℝ := 1 / (2 * (B * L + 1))

/-- This explicit relative window is positive, at most one half, and contractive. -/
theorem normalizedComplianceWindowFraction_spec {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) :
    0 < normalizedComplianceWindowFraction B L ∧
      normalizedComplianceWindowFraction B L ≤ 1 / 2 ∧
      (normalizedComplianceWindowFraction B L * B) * L ≤ 1 / 2 := by
  have hBL := mul_nonneg hB hL
  have hden : 0 < 2 * (B * L + 1) := by positivity
  have hpos : 0 < normalizedComplianceWindowFraction B L := one_div_pos.mpr hden
  have heq : normalizedComplianceWindowFraction B L * (2 * (B * L + 1)) = 1 := by
    unfold normalizedComplianceWindowFraction
    field_simp
  exact ⟨hpos, by nlinarith, by nlinarith⟩

/-- The unchanged actual mobility bounds imply contraction on this chosen unit window. -/
theorem normalizedComplianceWindowFraction_contractive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    {R : ℝ → V →L[ℝ] V}
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖R r‖ ≤ normalizedComplianceWindowFraction B L * B) :
    ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ) := by
  intro r hr
  exact (mul_le_mul_of_nonneg_right (hR r hr) hL).trans
    (normalizedComplianceWindowFraction_spec hB hL).2.2

end OTSelector.Reconstruction
