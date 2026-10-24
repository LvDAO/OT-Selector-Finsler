import OTSelector.Probability.MarkSelectedIIDPositions
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingPhysical

/-! Marks-only selection of original reserve positions feeds the actual
sample-to-population coupling without changing any selected original point. -/
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {I Z X : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace Z] [MeasurableSpace X] {n q : ℕ}

/-- The unchanged original positions chosen by the actual auxiliary-only index map. -/
def originalMarkSelectedPositions (e : Z → Fin n ↪ I) (p : Z × (I → X)) : Fin n → X :=
  fun j ↦ p.2 (e p.1 j)

/-- The selected original-position array is measurable, including repeated positions. -/
theorem measurable_originalMarkSelectedPositions (e : Z → Fin n ↪ I)
    (he : ∀ j, Measurable (fun z ↦ e z j)) :
    Measurable (originalMarkSelectedPositions (X := X) e) := by
  apply measurable_pi_lambda
  intro j
  have heval : Measurable (fun p : (I → X) × I ↦ p.1 p.2) :=
    measurable_from_prod_countable_left (fun i ↦ measurable_pi_apply i)
  exact heval.comp (measurable_snd.prodMk ((he j).comp measurable_fst))

/-- Marks-only injection selects the exact original iid position law. -/
theorem measurePreserving_originalMarkSelectedPositions
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Measure Z) [IsProbabilityMeasure P]
    (e : Z → Fin n ↪ I) (he : ∀ j, Measurable (fun z ↦ e z j)) :
    MeasurePreserving (originalMarkSelectedPositions (X := X) e)
      (P.prod (Measure.pi (fun _ : I ↦ μ))) (Measure.pi (fun _ : Fin n ↦ μ)) := by
  have hm := measurable_originalMarkSelectedPositions (X := X) e he
  refine ⟨hm, ?_⟩
  have h := congrArg (fun ν : Measure (Z × (Fin n → X)) ↦ ν.map Prod.snd)
    (OTSelector.Probability.map_mark_selected_original_iid_positions μ P e he)
  change ((P.prod (Measure.pi (fun _ : I ↦ μ))).map
    (fun p ↦ (p.1, originalMarkSelectedPositions e p))).map Prod.snd = _ at h
  rw [Measure.map_map measurable_snd (measurable_fst.prodMk hm)] at h
  simpa only [Function.comp_def, Measure.map_snd_prod, measure_univ, one_smul] using h

/-- The actual physical population plan starts at the selected original positions. -/
def originalMarkSelectedPhysicalCubePopulationCoupling
    (μ : Measure (DyadicUnitCube q)) (e : Z → Fin n ↪ I)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (p : Z × (I → DyadicUnitCube q)) :=
  originalIIDPhysicalCubePopulationCoupling μ z L (originalMarkSelectedPositions e p)

/-- This real plan retains every selected original atom, its exact population
marginal and finite mass; it depends measurably on the original experiment. -/
theorem originalMarkSelectedPhysicalCubePopulationCoupling_spec
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (e : Z → Fin n ↪ I) (he : ∀ j, Measurable (fun z ↦ e z j))
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (originalMarkSelectedPhysicalCubePopulationCoupling μ e z L) ∧
    ∀ p : Z × (I → DyadicUnitCube q),
      let Γ := originalMarkSelectedPhysicalCubePopulationCoupling μ e z L p
      IsFiniteMeasure Γ ∧
        Γ.map Prod.fst = ∑ j, Measure.dirac (originalIIDCubePhysicalMap z L (p.2 (e p.1 j))) ∧
        Γ.map Prod.snd = (n : ℝ≥0∞) • μ.map (originalIIDCubePhysicalMap z L) :=
  ⟨(measurable_originalIIDPhysicalCubePopulationCoupling μ z L).comp
      (measurable_originalMarkSelectedPositions e he),
    fun p ↦ originalIIDPhysicalCubePopulationCoupling_marginals μ z L
      (originalMarkSelectedPositions e p)⟩

/-- The true original-index selected reserve transport inherits the physical
expected square-cost rate under the actual marks/positions product experiment. -/
theorem expected_originalMarkSelectedPhysicalCubePopulationCoupling_squareCost_rate
    (hq : 4 < q) (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (P : Measure Z) [IsProbabilityMeasure P]
    (e : Z → Fin n ↪ I) (he : ∀ j, Measurable (fun z ↦ e z j))
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Integrable (fun p : Z × (I → DyadicUnitCube q) ↦
      ∫ v, ‖v.1 - v.2‖ ^ 2 ∂originalMarkSelectedPhysicalCubePopulationCoupling μ e z L p)
      (P.prod (Measure.pi (fun _ : I ↦ μ))) ∧
    (∫ p, ∫ v, ‖v.1 - v.2‖ ^ 2
      ∂originalMarkSelectedPhysicalCubePopulationCoupling μ e z L p
      ∂P.prod (Measure.pi (fun _ : I ↦ μ))) ≤
        ((q : ℝ) * L ^ 2) * dyadicMatchingConstant q *
          (n : ℝ) ^ (1 - 2 / (q : ℝ)) := by
  have hp := measurePreserving_originalMarkSelectedPositions μ P e he
  have h := expected_originalIIDPhysicalCubePopulationCoupling_squareCost_rate (n := n) hq μ z L
  have hmapI := h.1.aestronglyMeasurable
  rw [← hp.map_eq] at hmapI
  have heq := integral_map hp.measurable.aemeasurable hmapI
  rw [hp.map_eq] at heq
  exact ⟨hp.integrable_comp_of_integrable h.1, heq.symm.trans_le h.2⟩

end OTSelector.Reconstruction
