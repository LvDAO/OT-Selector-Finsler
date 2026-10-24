import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowLaw

/-!
# The full original input law is shared by every genuine matching

Compact original Laplace data determine the entire immutable input measure law.
This permits one fixed reference window to control all candidate scene laws,
without choosing a window size separately for each later candidate.
-/
open Set Function MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
local instance inputLawEqualityInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance inputLawEqualityPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Equal compact original input Laplace readouts identify the complete input
law even when either scene has not yet been proved full or stationary. -/
theorem originalInputLaw_eq_of_compact_laplace_eq
    {q : ℕ} (Q P : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ S : ℝ, 0 < S →
      ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ s, legalMarkedInputSceneLaplace q F hF s
          ∂(P : Measure (LegalMarkedOptimalInputScene q))) :
    (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (P : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd := by
  have : IsProbabilityMeasure
      ((Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have : IsProbabilityMeasure
      ((P : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  apply measure_eq_of_legalInput_compact_laplace
  intro F
  rw [integral_map measurable_snd.aemeasurable (legalInputMeasureLaplace F).continuous.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable (legalInputMeasureLaplace F).continuous.aestronglyMeasurable]
  change (∫ s, legalMarkedInputSceneLaplace q F.1 F.2 s
    ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ s, legalMarkedInputSceneLaplace q F.1 F.2 s
        ∂(P : Measure (LegalMarkedOptimalInputScene q))
  obtain ⟨S, hS, hbound⟩ := (F.1.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  have hzero (x : LegalMarkedPhysicalPoint q) (c : Fin 2)
      (hx : x.1 ∉ haarRootCube (Fin q) S) : F.1 (x, c) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupp
    apply hx
    have hn : ‖x.1‖ < S := hbound _ ⟨(x, c), hsupp, rfl⟩
    have hi (i : Fin q) : |x.1 i| ≤ S := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.1 i).trans hn.le
    exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩
  exact hLaplace S hS F.1 F.2 hzero


/-- Every pair of genuine matchings with the same original scalar populations
has exactly the same complete colored input law, independently of its edge plan. -/
theorem LegalWeightedStationaryPoissonMatching.inputLaw_eq
    {q : ℕ} {α β : Measure ℝ}
    {kin₁ kin₂ : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g₁ g₂ : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin₁ g₁)
    (N : LegalWeightedStationaryPoissonMatching q α β kin₂ g₂) :
    (M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (N.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd := by
  apply originalInputLaw_eq_of_compact_laplace_eq M.law N.law
  intro S hS F hF hzero
  rw [M.input_laplace S hS F hF hzero, N.input_laplace S hS F hF hzero]

end OTSelector.Reconstruction
