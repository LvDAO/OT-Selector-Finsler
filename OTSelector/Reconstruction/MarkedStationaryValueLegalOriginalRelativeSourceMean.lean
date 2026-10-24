import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalJointSceneReroot
import OTSelector.Probability.CavityGridPhaseSignedPeriodization
import OTSelector.MeasureTheory.MarkDependentHaarTranslation

/-! Exact source-cell means keep the same actual stationary original scene. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

variable {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
  {g : ℝ → ℝ → ℝ}

/-- Simultaneously moving each observation root and the entire original scene
preserves their actual Haar/original-law product. -/
theorem LegalWeightedStationaryPoissonMatching.measurePreserving_sourceRootSkew
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    MeasurePreserving (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      (p.1, legalMarkedInputSceneReroot q p.1 p.2))
      ((volume : Measure (Fin q → ℝ)).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q)))
      ((volume : Measure (Fin q → ℝ)).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q))) := by
  exact (MeasurePreserving.id (volume : Measure (Fin q → ℝ))).skew_product
    (measurable_legalMarkedInputSceneReroot_joint q)
    (Eventually.of_forall (fun b ↦ (M.stationary b).map_eq))

/-- A selected original source is allowed to depend on the whole scene.
Its exact signed mean only uses stationarity and its actual L1 gain. -/
theorem LegalWeightedStationaryPoissonMatching.relativeSourceAtom_integrable_and_integral
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (x : LegalMarkedOptimalInputScene q → Fin q → ℝ) (hx : Measurable x)
    (a : LegalMarkedOptimalInputScene q → ℝ)
    (ha : Integrable a (M.law : Measure (LegalMarkedOptimalInputScene q)))
    {w : (Fin q → ℝ) → ℝ} (hw : Integrable w (volume : Measure (Fin q → ℝ))) :
    Integrable (fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      w (p.1 + x (legalMarkedInputSceneReroot q p.1 p.2)) *
        a (legalMarkedInputSceneReroot q p.1 p.2))
      ((volume : Measure (Fin q → ℝ)).prod
        (M.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∫ p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q,
        w (p.1 + x (legalMarkedInputSceneReroot q p.1 p.2)) *
          a (legalMarkedInputSceneReroot q p.1 p.2)
        ∂(volume : Measure (Fin q → ℝ)).prod
          (M.law : Measure (LegalMarkedOptimalInputScene q))) =
        (∫ b, w b) * ∫ s, a s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let P : Measure (LegalMarkedOptimalInputScene q) := M.law
  let F : (Fin q → ℝ) × LegalMarkedOptimalInputScene q → ℝ :=
    fun p ↦ w (p.1 + x p.2) * a p.2
  have hFi : Integrable F ((volume : Measure (Fin q → ℝ)).prod P) :=
    integrable_markDependentAnchorTranslation P x hx hw ha
  have hmp := M.measurePreserving_sourceRootSkew
  refine ⟨hmp.integrable_comp_of_integrable hFi, ?_⟩
  have hm : AEStronglyMeasurable F
      (((volume : Measure (Fin q → ℝ)).prod P).map
        (fun p ↦ (p.1, legalMarkedInputSceneReroot q p.1 p.2))) := by
    rw [hmp.map_eq]
    exact hFi.aestronglyMeasurable
  have he := integral_map hmp.measurable.aemeasurable hm
  rw [hmp.map_eq] at he
  exact he.symm.trans (integral_markDependentAnchorTranslation P x hx hw ha)

end OTSelector.Reconstruction
