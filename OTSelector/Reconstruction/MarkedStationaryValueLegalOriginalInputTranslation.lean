import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-! # The actual spatial translation action on complete original colored inputs -/

open Set Function MeasureTheory ProbabilityTheory Topology TopologicalSpace

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option linter.unusedSectionVars false

/-- Translate every original colored input point, preserving its clock and its immutable color. -/
def legalOriginalInputTranslation (q : ℕ) (v : Fin q → ℝ) :
    LocalFiniteMeasure (LegalColoredInputPoint q) → LocalFiniteMeasure (LegalColoredInputPoint q) :=
  localFiniteMapHomeomorph (legalColoredInputPointReroot q v)

theorem continuous_legalOriginalInputTranslation (q : ℕ) (v : Fin q → ℝ) :
    Continuous (legalOriginalInputTranslation q v) := continuous_localFiniteMapHomeomorph _

theorem legalOriginalInputTranslation_zero (q : ℕ) :
    legalOriginalInputTranslation q 0 = id := by
  funext μ
  apply Subtype.ext
  change (μ : Measure (LegalColoredInputPoint q)).map _ = _
  have hz : (legalColoredInputPointReroot q 0 : LegalColoredInputPoint q →
      LegalColoredInputPoint q) = id := by
    funext p
    ext <;> simp [legalColoredInputPointReroot, physicalScenePointReroot_apply]
  rw [hz, Measure.map_id]
  rfl

theorem legalOriginalInputTranslation_add (q : ℕ) (v w : Fin q → ℝ) :
    legalOriginalInputTranslation q v ∘ legalOriginalInputTranslation q w =
      legalOriginalInputTranslation q (w + v) := by
  funext μ
  apply Subtype.ext
  change ((μ : Measure (LegalColoredInputPoint q)).map _).map _ =
    (μ : Measure (LegalColoredInputPoint q)).map _
  rw [Measure.map_map (legalColoredInputPointReroot q v).continuous.measurable
    (legalColoredInputPointReroot q w).continuous.measurable]
  congr 1
  funext p
  ext <;> simp [legalColoredInputPointReroot, physicalScenePointReroot_apply, sub_sub]

theorem legalOriginalInputTranslation_iterate (q : ℕ) (v : Fin q → ℝ) (k : ℕ) :
    (legalOriginalInputTranslation q v)^[k] =
      legalOriginalInputTranslation q ((k : ℝ) • v) := by
  induction k with
  | zero => simpa using (legalOriginalInputTranslation_zero q).symm
  | succ k hk =>
    rw [Function.iterate_succ', hk, legalOriginalInputTranslation_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

/-- Stationarity of one actual joint scene passes to its complete original input law. -/
theorem measurePreserving_legalOriginalInputTranslation
    {q : ℕ} (Q : Measure (LegalMarkedOptimalInputScene q)) (v : Fin q → ℝ)
    (hQ : MeasurePreserving (legalMarkedInputSceneReroot q v) Q Q) :
    MeasurePreserving (legalOriginalInputTranslation q v)
      (Q.map Prod.snd) (Q.map Prod.snd) := by
  exact MeasurePreserving.of_semiconj
    (MeasureTheory.MeasurePreserving.mk measurable_snd rfl) hQ
    (show Semiconj Prod.snd (legalMarkedInputSceneReroot q v)
      (legalOriginalInputTranslation q v) from fun s ↦ rfl)
    (continuous_legalOriginalInputTranslation q v).measurable

end OTSelector.Reconstruction
