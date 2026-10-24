import OTSelector.Reconstruction.OriginalReserveUnitInputReadouts

/-! Preserve the original main scene while adding a whole reserve at any positive intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance originalReserveMainIntensityInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveMainIntensityPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The complete original main matching and input, plus the independently
intensity-scaled reserve input. The resulting input has intensity one plus theta. -/
def originalReserveMainIntensityScene (q : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (p : LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) :
    LegalMarkedOptimalInputScene q :=
  legalMarkedReserveInputScene q
    (p.1, legalMarkedInputSceneDilation q (legalIntensityDilation q θ)
      (legalIntensityDilation_pos q hθ).ne' p.2)

theorem measurable_originalReserveMainIntensityScene (q : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    Measurable (originalReserveMainIntensityScene q θ hθ) :=
  (measurable_legalMarkedReserveInputScene q).comp
    (measurable_fst.prodMk
      ((continuous_legalMarkedInputSceneDilation q _ _).measurable.comp measurable_snd))

/-- The actual working input is read from the original main and whole reserve;
the finite reserve sampler remains an identity witness. -/
def originalReserveMainIntensityInputReadout (q : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (p : LegalMarkedOptimalInputScene q ×
      (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)) :
    LegalMarkedOptimalInputScene q :=
  originalReserveMainIntensityScene q θ hθ (p.1, p.2.1)

theorem measurable_originalReserveMainIntensityInputReadout
    (q : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    Measurable (originalReserveMainIntensityInputReadout q θ hθ) :=
  (measurable_originalReserveMainIntensityScene q θ hθ).comp
    (measurable_fst.prodMk measurable_snd.fst)

/-- The working window consists of exactly the unchanged main and the whole
intensity-scaled reserve, for every spatial set. -/
theorem originalReserveMainIntensityInputReadout_window_decomposition
    (q : ℕ) (θ : ℝ) (hθ : 0 < θ) (K : Set (Fin q → ℝ))
    (p : LegalMarkedOptimalInputScene q ×
      (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)) :
    ((originalReserveMainIntensityInputReadout q θ hθ p).2 :
      Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) =
      (p.1.2 : Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) +
      ((legalMarkedInputSceneDilation q (legalIntensityDilation q θ)
        (legalIntensityDilation_pos q hθ).ne' p.2.1).2 :
          Measure (LegalColoredInputPoint q)).restrict ((Prod.fst ∘ Prod.fst) ⁻¹' K) :=
  Measure.restrict_add _ _ _

/-- Mapping the original independent pair produces the literal reserve
superposition law, with the original main law intact. -/
theorem map_originalPair_eq_mainIntensityReserveLaw (q : ℕ)
    (Q N : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (θ : ℝ) (hθ : 0 < θ) :
    ((Q : Measure (LegalMarkedOptimalInputScene q)).prod (N : Measure _)).map
      (originalReserveMainIntensityScene q θ hθ) =
        (legalMarkedReserveInputLaw q Q (legalMarkedInputDilationLaw q
          (legalIntensityDilation q θ) (legalIntensityDilation_pos q hθ).ne' N) :
            Measure (LegalMarkedOptimalInputScene q)) := by
  change ((Q : Measure (LegalMarkedOptimalInputScene q)).prod (N : Measure _)).map
    ((legalMarkedReserveInputScene q) ∘ Prod.map id
      (legalMarkedInputSceneDilation q (legalIntensityDilation q θ)
        (legalIntensityDilation_pos q hθ).ne')) = _
  rw [← Measure.map_map (measurable_legalMarkedReserveInputScene q)
    (measurable_id.prodMap (continuous_legalMarkedInputSceneDilation q _ _).measurable),
    ← Measure.map_prod_map _ _ measurable_id
      (continuous_legalMarkedInputSceneDilation q _ _).measurable, Measure.map_id]
  rfl

end OTSelector.Reconstruction
