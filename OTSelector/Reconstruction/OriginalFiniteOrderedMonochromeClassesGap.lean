import OTSelector.Reconstruction.FiniteScalarBins
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation
import OTSelector.Finite.ThresholdClockHallFlow

/-! Actual cross-support separation determines single colours and ordered bins. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 400000

/-- Positive mass in an actual measurable bin supplies a point in the true
support; the other marginal and any chosen coupling are irrelevant. -/
theorem scalarBin_exists_mem_support_of_mass_ne_zero
    (μ : Measure ℝ) {A : Set ℝ} (hμ : μ A ≠ 0) :
    ∃ x ∈ A, x ∈ μ.support := by
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hμ (ae_restrict_of_ae μ.support_mem_ae)

/-- A small bin cannot have positive mass from both original colours when all
opposite-colour support points have the genuine physical scalar separation. -/
theorem FiniteScalarBins.cell_mass_monochrome
    {I : Set ℝ} {δ D : ℝ} (Q : FiniteScalarBins I δ)
    {μ ν : Measure ℝ} (hδ : 0 < δ) (hsep : ConditionalClockSupportBounds μ ν δ D)
    (i : Fin Q.count) : μ (Q.cell i) = 0 ∨ ν (Q.cell i) = 0 := by
  by_cases hμ : μ (Q.cell i) = 0
  · exact Or.inl hμ
  · right
    by_contra hν
    obtain ⟨x, hx, hxs⟩ := scalarBin_exists_mem_support_of_mass_ne_zero μ hμ
    obtain ⟨y, hy, hys⟩ := scalarBin_exists_mem_support_of_mass_ne_zero ν hν
    have hgap := hsep.separated x hxs y hys
    rw [Real.dist_eq] at hgap
    have hsmall := Q.diameter i x hx y hy
    linarith

/-- The lower threshold of a nonempty bounded bin is within one bin width of
all of its points. No interval shape or positive density is assumed. -/
theorem FiniteScalarBins.mem_lower_bounds
    {I : Set ℝ} {δ : ℝ} (Q : FiniteScalarBins I δ) (hI : IsCompact I)
    (i : Fin Q.count) {x : ℝ} (hx : x ∈ Q.cell i) :
    sInf (Q.cell i) ≤ x ∧ x - δ / 4 ≤ sInf (Q.cell i) := by
  have hb : BddBelow (Q.cell i) := hI.bddBelow.mono (Q.subset i)
  refine ⟨csInf_le hb hx, le_csInf ⟨x, hx⟩ ?_⟩
  intro y hy
  have hd := (abs_le.mp (Q.diameter i x hx y hy)).2
  linarith

/-- Sorting genuine positive source and target bins by their lower thresholds
orders every point of their full rectangles, with half the original gap. -/
theorem FiniteScalarBins.gap_of_positive_mass_lower_order
    {I : Set ℝ} {δ D : ℝ} (Q : FiniteScalarBins I δ) (hI : IsCompact I)
    {μ ν : Measure ℝ} (hδ : 0 < δ) (hsep : ConditionalClockSupportBounds μ ν δ D)
    {i j : Fin Q.count} (hμ : μ (Q.cell i) ≠ 0) (hν : ν (Q.cell j) ≠ 0)
    (horder : sInf (Q.cell i) ≤ sInf (Q.cell j)) :
    ∀ x ∈ Q.cell i, ∀ y ∈ Q.cell j, δ / 2 ≤ y - x := by
  obtain ⟨a, ha, has⟩ := scalarBin_exists_mem_support_of_mass_ne_zero μ hμ
  obtain ⟨b, hb, hbs⟩ := scalarBin_exists_mem_support_of_mass_ne_zero ν hν
  have hsepab := hsep.separated a has b hbs
  have hforward : a ≤ b := by
    by_contra h
    have hba : b < a := lt_of_not_ge h
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hba)] at hsepab
    have hai := (Q.mem_lower_bounds hI i ha).2
    have hbj := (Q.mem_lower_bounds hI j hb).1
    linarith
  have hgap : δ ≤ b - a := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hforward)] at hsepab
    linarith
  exact fun x hx y hy ↦ Q.gap_of_same_bins ha hb hgap hx hy

/-- A uniform scalar rectangle gap extends to both closures. This preserves the
support points added by restriction or by closing half-open grid cells. -/
theorem scalarRectangle_gap_closure {A B : Set ℝ} {gap : ℝ}
    (hgap : ∀ x ∈ A, ∀ y ∈ B, gap ≤ y - x) :
    ∀ x ∈ closure A, ∀ y ∈ closure B, gap ≤ y - x := by
  intro x hx y hy
  have hA : ∀ b ∈ B, gap ≤ b - x := by
    intro b hb
    exact closure_minimal (fun a ha ↦ hgap a ha b hb)
      (isClosed_le continuous_const (continuous_const.sub continuous_id)) hx
  exact closure_minimal hA
    (isClosed_le continuous_const (continuous_id.sub continuous_const)) hy

end OTSelector.Reconstruction
