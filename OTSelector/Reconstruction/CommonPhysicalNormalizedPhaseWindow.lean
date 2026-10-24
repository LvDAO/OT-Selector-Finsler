import OTSelector.Reconstruction.NormalizedComplianceContractionWindow

/-! One positive relative clock window satisfies both the actual physical
velocity cone and the actual normalized contraction bound. -/
open Set
noncomputable section
namespace OTSelector.Reconstruction

/-- The same relative fraction respects the physical collar and normalized mobility. -/
def commonPhysicalNormalizedWindowFraction (cap B L : ℝ) : ℝ :=
  min cap (normalizedComplianceWindowFraction B L)

theorem commonPhysicalNormalizedWindowFraction_le_cap (cap B L : ℝ) :
    commonPhysicalNormalizedWindowFraction cap B L ≤ cap := min_le_left _ _

theorem commonPhysicalNormalizedWindowFraction_spec {cap B L : ℝ}
    (hcap : 0 < cap) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    0 < commonPhysicalNormalizedWindowFraction cap B L ∧
      commonPhysicalNormalizedWindowFraction cap B L ≤ 1 / 2 ∧
      (commonPhysicalNormalizedWindowFraction cap B L * B) * L ≤ 1 / 2 := by
  have hf := normalizedComplianceWindowFraction_spec hB hL
  refine ⟨lt_min hcap hf.1, (min_le_right _ _).trans hf.2.1, ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_right cap _) hB) hL).trans hf.2.2

theorem commonPhysicalNormalizedWindowFraction_contractive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {cap B L : ℝ} (hcap : 0 < cap) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {R : ℝ → V →L[ℝ] V}
    (hR : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖R r‖ ≤ commonPhysicalNormalizedWindowFraction cap B L * B) :
    ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ) := by
  intro r hr
  exact (mul_le_mul_of_nonneg_right (hR r hr) hL).trans
    (commonPhysicalNormalizedWindowFraction_spec hcap hB hL).2.2

end OTSelector.Reconstruction
