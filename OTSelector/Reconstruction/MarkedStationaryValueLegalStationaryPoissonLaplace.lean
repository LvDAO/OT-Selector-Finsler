import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonLaplaceFormula

/-!
# Global compact Poisson Laplace functional of the actual original input

An actual finite original spatial cube contains any compact test. The exact
original finite-array formula and vanishing off that cube produce the global
Haar-times-original-clock Laplace exponent of any genuine original matching.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Spatial support removes the window restriction exactly in the analytic
Laplace exponent of the original physical Poisson arrays. -/
theorem integral_legalInputPoissonWindowLaw_laplace_eq_global_exp
    (q : ℕ) {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {f g : LegalMarkedPhysicalPoint q → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (hfzero : ∀ x, x.1 ∉ U → f x = 0) (hgzero : ∀ x, x.1 ∉ U → g x = 0) :
    (∫ z, legalInputBlockLaplace f g z ∂legalInputPoissonWindowLaw q U α β) =
      Real.exp ((∫ x, (Real.exp (-f x) - 1) ∂(volume : Measure (Fin q → ℝ)).prod α) +
        ∫ y, (Real.exp (-g y) - 1) ∂(volume : Measure (Fin q → ℝ)).prod β) := by
  have hexact (γ : Measure ℝ) [IsProbabilityMeasure γ]
      (h : LegalMarkedPhysicalPoint q → ℝ) (hz : ∀ x, x.1 ∉ U → h x = 0) :
      (∫ x, (Real.exp (-h x) - 1) ∂((volume : Measure (Fin q → ℝ)).restrict U).prod γ) =
        ∫ x, (Real.exp (-h x) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ := by
    rw [Measure.restrict_prod_eq_prod_univ]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxU : x.1 ∉ U := fun hmem ↦ hx ⟨hmem, mem_univ _⟩
    simp only [hz x hxU, neg_zero, Real.exp_zero, sub_self]
  rw [integral_legalInputPoissonWindowLaw_laplace_eq_exp q hUfin hUpos α β hf hg hfn hgn,
    hexact α f hfzero, hexact β g hgzero]

/-- Every compact colored test has a finite original spatial cube containing
its support, including in zero spatial dimension. -/
theorem exists_cube_support_legalColoredInputTest (q : ℕ)
    (F : C_c(LegalColoredInputPoint q, ℝ)) :
    ∃ S > 0, ∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0 := by
  obtain ⟨S, hS, hbound⟩ := (F.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  refine ⟨S, hS, fun x c hx ↦ ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hsupp
  apply hx
  have hn : ‖x.1‖ < S := hbound _ ⟨(x, c), hsupp, rfl⟩
  have hi (i : Fin q) : |x.1 i| ≤ S := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.1 i).trans hn.le
  exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩

/-- The entire compact Poisson Laplace functional is produced from the
original finite-window input field of the same genuine matching. -/
theorem LegalWeightedStationaryPoissonMatching.input_laplace_eq_global_exp
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      Real.exp ((∫ x, (Real.exp (-F (x, 0)) - 1)
        ∂(volume : Measure (Fin q → ℝ)).prod α) +
          ∫ y, (Real.exp (-F (y, 1)) - 1)
            ∂(volume : Measure (Fin q → ℝ)).prod β) := by
  obtain ⟨S, hS, hz⟩ := exists_cube_support_legalColoredInputTest q F
  have hfin : volume (haarRootCube (Fin q) S) ≠ ∞ := by
    rw [volume_haarRootCube (Fin q) hS.le]
    exact ENNReal.ofReal_ne_top
  have hpos : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) _)).ne'
  rw [M.input_laplace S hS F hF hz]
  apply integral_legalInputPoissonWindowLaw_laplace_eq_global_exp q hfin hpos α β
    (F.continuous.measurable.comp (measurable_id.prodMk measurable_const))
    (F.continuous.measurable.comp (measurable_id.prodMk measurable_const))
    (fun x ↦ hF (x, 0)) (fun x ↦ hF (x, 1))
  · exact fun x hx ↦ hz x 0 hx
  · exact fun x hx ↦ hz x 1 hx

end OTSelector.Reconstruction
