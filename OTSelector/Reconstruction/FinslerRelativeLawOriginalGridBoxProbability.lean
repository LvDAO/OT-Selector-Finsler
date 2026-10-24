import OTSelector.Reconstruction.FinslerRelativeLawPositiveMicrogrid

/-! The literal Haar/class full-box probabilities eventually require no truncation. -/
open Filter
open scoped Topology ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Reconstruction

/-- On the actual positive microscopic grid, every fixed original Haar/class
density eventually gives a genuine full-box probability and agrees exactly
with the probability used by the homogeneous binomial model. -/
theorem eventually_positiveMicroscopicCubeProbability_eq_original_box
    {q : ℕ} (hq : 0 < q) (density : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ N : ℕ in atTop,
      density * (((positiveMicroscopicGridOrder q L N : ℝ≥0)⁻¹) ^ q) ≤ 1 ∧
      (positiveMicroscopicCubeProbability q density L N : ℝ) =
        ((density * (((positiveMicroscopicGridOrder q L N : ℝ≥0)⁻¹) ^ q) : ℝ≥0) : ℝ) := by
  filter_upwards [positiveMicroscopicCubeProbability_eventually_eq q density hL,
    microscopicCubeProbability_eventually_eq hq density hL,
    positiveMicroscopicGridSide_eventually_eq q hL] with N hprob hraw hside
  have heq : (positiveMicroscopicCubeProbability q density L N : ℝ) =
      (density : ℝ) * positiveMicroscopicGridSide q L N ^ q := by
    rw [hprob, hraw, hside]
  have hbox : density * (((positiveMicroscopicGridOrder q L N : ℝ≥0)⁻¹) ^ q) ≤ 1 := by
    have h := (positiveMicroscopicCubeProbability q density L N).property.2
    rw [heq] at h
    exact_mod_cast h
  exact ⟨hbox, heq⟩

end OTSelector.Reconstruction
