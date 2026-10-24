import OTSelector.Reconstruction.BirthTrafficSourceWindowVolume

/-! The actual bounded-phase source or target window has original intensity
O(s/t) directly from physical Haar volume and the same original residue density. -/
open Set Matrix MeasureTheory
open scoped ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A deterministic actual canonical spatial window times an original clock
band has its true product intensity bound, with no auxiliary leg determinant. -/
theorem exists_birthSpatialClockWindow_intensity_bound
    {q : ℕ} {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0 < q) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Measure ℝ) [SFinite σ],
      ∀ {t s K : ℝ}, 0 < t → t ≤ 1 → 0 < s → 0 ≤ K →
      ∀ {A : Set ℝ}, MeasurableSet A →
      σ A ≤ ENNReal.ofReal (K * t ^ G.rank * s) →
      ((volume : Measure (Fin q → ℝ)).prod σ)
        (birthTrafficSpatialWindow G t s R ×ˢ A) ≤ ENNReal.ofReal (C * K * (s / t)) := by
  obtain ⟨C, hC, hvol⟩ := exists_birthTrafficSpatialWindow_volume_bound hG
    (by simpa using hq) R
  refine ⟨C, hC, fun σ _ {t s K} ht ht1 hs hK {A} _hA hmass ↦ ?_⟩
  rw [Measure.prod_prod]
  calc
    _ ≤ ENNReal.ofReal (C * (t ^ (G.rank + 1))⁻¹) *
        ENNReal.ofReal (K * t ^ G.rank * s) := mul_le_mul' (hvol ht ht1 hs) hmass
    _ = ENNReal.ofReal ((C * (t ^ (G.rank + 1))⁻¹) * (K * t ^ G.rank * s)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ = _ := by
      congr 1
      rw [pow_succ]
      field_simp

end OTSelector.Reconstruction
