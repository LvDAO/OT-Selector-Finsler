import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilation
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonLaplace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The actual Poisson input intensity under spatial dilation

The original joint scene is pushed by a deterministic physical dilation. Its
full compact Laplace functional is derived from the original input field and
the Haar Jacobian; its original scalar populations and colors remain unchanged.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance markedStationaryValueLegalStationaryDilationPoissonInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryDilationPoissonPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The same full original scene, at its actual dilated physical intensity. -/
def legalMarkedInputDilationLaw (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  Q.map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable

/-- The literal original input test is pulled back by the same dilation. -/
theorem legalMarkedInputSceneDilation_testIntegral (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (s : LegalMarkedOptimalInputScene q) (F : C_c(LegalColoredInputPoint q, ℝ)) :
    LocalFiniteMeasure.testIntegral (legalMarkedInputSceneDilation q c hc s).2 F =
      LocalFiniteMeasure.testIntegral s.2 (F.comp (legalColoredInputDilation q c hc).toCocompactMap) := by
  exact integral_map (legalColoredInputDilation q c hc).continuous.measurable.aemeasurable
    F.continuous.measurable.aestronglyMeasurable

/-- The original scalar intensity is unchanged; the spatial Haar intensity
has the exact dimension-dependent inverse Jacobian. -/
theorem map_physicalIntensity_legalMarkedPointDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (γ : Measure ℝ) [SFinite γ] :
    ((volume : Measure (Fin q → ℝ)).prod γ).map (legalMarkedPointDilation q c hc) =
      ENNReal.ofReal |(c ^ q)⁻¹| • ((volume : Measure (Fin q → ℝ)).prod γ) := by
  have hvol : (volume : Measure (Fin q → ℝ)).map (fun x ↦ c • x) =
      ENNReal.ofReal |(c ^ q)⁻¹| • (volume : Measure (Fin q → ℝ)) := by
    simpa using Measure.map_addHaar_smul (volume : Measure (Fin q → ℝ)) hc
  change ((volume : Measure (Fin q → ℝ)).prod γ).map (Prod.map (fun x ↦ c • x) id) = _
  calc
    _ = ((volume : Measure (Fin q → ℝ)).map (fun x ↦ c • x)).prod (γ.map id) :=
      (Measure.map_prod_map _ _ (measurable_id.const_smul c) measurable_id).symm
    _ = _ := by rw [hvol, Measure.map_id, Measure.prod_smul_left]

/-- The actual dilated matching has independent original Poisson inputs with
its true Haar-scaled intensity, produced from the original compact input law. -/
theorem LegalWeightedStationaryPoissonMatching.dilation_input_laplace_eq_global_exp
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (c : ℝ) (hc : c ≠ 0)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(legalMarkedInputDilationLaw q c hc M.law : Measure (LegalMarkedOptimalInputScene q))) =
      Real.exp (|(c ^ q)⁻¹| *
        ((∫ x, (Real.exp (-F (x, 0)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod α) +
          ∫ y, (Real.exp (-F (y, 1)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod β)) := by
  let G := F.comp (legalColoredInputDilation q c hc).toCocompactMap
  have hG : ∀ x, 0 ≤ G x := fun x ↦ hF _
  have hread : (fun s ↦ legalMarkedInputSceneLaplace q F hF
      (legalMarkedInputSceneDilation q c hc s)) = fun s ↦ legalMarkedInputSceneLaplace q G hG s := by
    funext s
    change Real.exp (-LocalFiniteMeasure.testIntegral (legalMarkedInputSceneDilation q c hc s).2 F) = _
    rw [legalMarkedInputSceneDilation_testIntegral]
    rfl
  change (∫ s, legalMarkedInputSceneLaplace q F hF s
    ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map (legalMarkedInputSceneDilation q c hc)) = _
  rw [integral_map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable
    (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable, hread,
    M.input_laplace_eq_global_exp G hG]
  have hI (γ : Measure ℝ) [IsProbabilityMeasure γ] (k : Fin 2) :
      (∫ x, (Real.exp (-G (x, k)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ) =
        |(c ^ q)⁻¹| * ∫ x, (Real.exp (-F (x, k)) - 1) ∂(volume : Measure (Fin q → ℝ)).prod γ := by
    have hm : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ Real.exp (-F (x, k)) - 1) := by
      fun_prop
    change (∫ x, (Real.exp (-F (legalMarkedPointDilation q c hc x, k)) - 1)
      ∂(volume : Measure (Fin q → ℝ)).prod γ) = _
    calc
      _ = ∫ x, (Real.exp (-F (x, k)) - 1)
          ∂((volume : Measure (Fin q → ℝ)).prod γ).map (legalMarkedPointDilation q c hc) :=
        (integral_map (legalMarkedPointDilation q c hc).continuous.measurable.aemeasurable
          hm.aestronglyMeasurable).symm
      _ = _ := by
        rw [map_physicalIntensity_legalMarkedPointDilation q c hc γ, integral_smul_measure]
        simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
  rw [hI α 0, hI β 1]
  congr 1
  ring

end OTSelector.Reconstruction
