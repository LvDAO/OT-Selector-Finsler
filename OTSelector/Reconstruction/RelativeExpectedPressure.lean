import OTSelector.Reconstruction.RelativePressureComparison
import OTSelector.Probability.CavitySemidiscretePressureSampling

/-!
# Relative comparison of the original expected finite pressures

Relative edge control transfers both integrability and the expectation error from
the reference pressure. The same sample environment is kept throughout; no new
optimizer selection or displacement-moment assumption is introduced.
-/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- Relative pointwise comparison transfers integrability and controls the difference
of expected values by the original reference expectation. -/
theorem integrable_expected_abs_sub_le_of_relative_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable f P) (hg : Integrable g P)
    {ε C B : ℝ} (hbound : ∀ᵐ ω ∂P, |f ω - g ω| ≤ ε * (g ω + C) + B) :
    Integrable f P ∧ |(∫ ω, f ω ∂P) - ∫ ω, g ω ∂P| ≤
      ε * ((∫ ω, g ω ∂P) + C) + B := by
  have hgC : Integrable (fun ω ↦ g ω + C) P := hg.add (integrable_const C)
  have hi : Integrable (fun ω ↦ ε * (g ω + C) + B) P :=
    (hgC.const_mul ε).add (integrable_const B)
  have hfint : Integrable f P := (hg.norm.add hi).mono' hf (by
    filter_upwards [hbound] with ω hω
    change ‖f ω‖ ≤ ‖g ω‖ + (ε * (g ω + C) + B)
    calc
      ‖f ω‖ = ‖g ω + (f ω - g ω)‖ := by congr 1; ring
      _ ≤ ‖g ω‖ + ‖f ω - g ω‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hω)
  refine ⟨hfint, ?_⟩
  rw [← integral_sub hfint hg, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have hle := integral_mono_ae (hfint.sub hg).norm hi hbound
  have hright : (∫ ω, ε * (g ω + C) + B ∂P) = ε * ((∫ ω, g ω ∂P) + C) + B := by
    rw [integral_add (hgC.const_mul ε) (integrable_const B),
      integral_const_mul, integral_add hg (integrable_const C)]
    simp
  exact hle.trans_eq hright

/-- Measurable original edge arrays give measurable actual tilted finite pressure. -/
theorem measurable_perturbedAssignmentValue_div {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (c g : Ω → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hc : ∀ i j, Measurable (fun ω ↦ c ω i j))
    (hg : ∀ i j, Measurable (fun ω ↦ g ω i j)) :
    Measurable (fun ω ↦ perturbedAssignmentValue (c ω) (g ω) t / (n : ℝ)) := by
  have hm := Probability.measurable_assignmentValue
    (fun ω ↦ perturbedEdgeCost (c ω) (g ω) t)
    (fun i j ↦ (hc i j).add ((hg i j).const_mul t))
  simpa only [perturbedAssignmentValue, perturbedEdgeCost_zero] using hm.div_const (n : ℝ)

/-- The actual finite sample pressure has the relative expected-pressure error supplied
by coefficient freezing. Integrability of the compared pressure is derived. -/
theorem expected_perturbedAssignmentValue_div_abs_sub_le_relative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (c g d h : Ω → Matrix (Fin n) (Fin n) ℝ)
    (t ε G B : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : ∀ i j, Measurable (fun ω ↦ c ω i j))
    (hg : ∀ i j, Measurable (fun ω ↦ g ω i j))
    (hdi : Integrable (fun ω ↦ perturbedAssignmentValue (d ω) (h ω) t / (n : ℝ)) P)
    (hrelative : ∀ᵐ ω ∂P, ∀ i j, |c ω i j - d ω i j| ≤ ε * d ω i j)
    (hh : ∀ᵐ ω ∂P, ∀ i j, |h ω i j| ≤ G)
    (hgh : ∀ᵐ ω ∂P, ∀ i j, |g ω i j - h ω i j| ≤ B) :
    Integrable (fun ω ↦ perturbedAssignmentValue (c ω) (g ω) t / (n : ℝ)) P ∧
      |(∫ ω, perturbedAssignmentValue (c ω) (g ω) t / (n : ℝ) ∂P) -
        ∫ ω, perturbedAssignmentValue (d ω) (h ω) t / (n : ℝ) ∂P| ≤
      ε * ((∫ ω, perturbedAssignmentValue (d ω) (h ω) t / (n : ℝ) ∂P) + |t| * G) +
        |t| * B := by
  apply integrable_expected_abs_sub_le_of_relative_bound
    (measurable_perturbedAssignmentValue_div c g t hc hg).aestronglyMeasurable hdi
  filter_upwards [hrelative, hh, hgh] with ω hω hhω hghω
  exact perturbedAssignmentValue_div_abs_sub_le_relative hn (c ω) (g ω) (d ω) (h ω)
    t ε G B hε0 hε1 hω hhω hghω

end OTSelector.Reconstruction
