import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowCoupling
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowColors
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalBlockRestriction

/-!
# Every genuine stationary candidate supplies an actual original finite core

The complete stationary scene and the literal original Poisson finite arrays
are joined through their unchanged input window. The actual integer edge
restriction is then extracted in the original retained indices with its exact
signed cost and its actual source-to-outside-target deficiency.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
local instance markedStationaryValueLegalStationaryOriginalWindowCoreColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance markedStationaryValueLegalStationaryOriginalWindowCoreInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryOriginalWindowCorePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Every original weighted stationary matching has an exact legal finite
window core on literal original Poisson arrays. All domination, simplicity,
window identities and finite signed costs are produced internally. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalPoisson_legal_windowCore
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : IsCompact U)
    (cost : LegalMarkedPhysicalEdge q → ℝ) :
    ∃ S > 0, ∃ R : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.fst =
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.snd =
        legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        let source := legalOriginalBlockRestriction U p.2.1
        let target := legalOriginalBlockRestriction U p.2.2
        ∃ σ : OTSelector.PartialMatching source.1 target.1,
          PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (source.2 i).2)
            (fun j ↦ (target.2 j).2)) σ ∧
          (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U) =
            ∑ e ∈ σ.edges, Measure.dirac (source.2 e.1, target.2 e.2) ∧
          (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ U) = (σ.card : ℝ≥0∞) ∧
          Integrable cost ((p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U)) ∧
          (∫ e in U ×ˢ U, cost e ∂(p.1.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
            σ.cost (fun i j ↦ cost (source.2 i, target.2 j)) ∧
          ((source.1 - σ.card : ℕ) : ℝ) =
            ((p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)).toReal := by
  obtain ⟨S, hS, R, hleft, hright, hread⟩ :=
    M.exists_originalPoisson_windowCoupling (hU.prod isCompact_univ)
  have hfull : ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))), IsFullOriginalInputMatching q p.1 := by
    have h : ∀ᵐ s ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.fst, IsFullOriginalInputMatching q s := by
      rw [hleft]
      exact M.full_matching
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hforward : ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
      ∀ e ∈ (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
    have h : ∀ᵐ s ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.fst,
        ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
      rw [hleft]
      exact M.forward
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hinj : ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))), Injective p.2.1.2 ∧ Injective p.2.2.2 := by
    have h : ∀ᵐ b ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.snd, Injective b.1.2 ∧ Injective b.2.2 := by
      rw [hright]
      exact ae_injective_legalInputPoissonWindowLaw q hq hS α β
    exact ae_of_ae_map measurable_snd.aemeasurable h
  refine ⟨S, hS, R, hleft, hright, ?_⟩
  filter_upwards [hfull, hforward, hinj, hread] with p hp hf hi hr
  let source := legalOriginalBlockRestriction U p.2.1
  let target := legalOriginalBlockRestriction U p.2.2
  have hm := original_window_marginals_eq_of_colored_readout q p.1 hp p.2 hU.measurableSet hr
  have hs : (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst.restrict U =
      ∑ i : Fin source.1, Measure.dirac (source.2 i) := by
    exact hm.1.trans (legalInputBlockMeasure_legalOriginalBlockRestriction p.2.1 hU.measurableSet).symm
  have ht : (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd.restrict U =
      ∑ j : Fin target.1, Measure.dirac (target.2 j) := by
    exact hm.2.trans (legalInputBlockMeasure_legalOriginalBlockRestriction p.2.2 hU.measurableSet).symm
  have hc := ((isLegalSimpleCountingMeasure_iff (0 : LegalMarkedPhysicalEdge q) p.1.1.1).mp
    hp.simple_edges).1
  have ha : ∀ᵐ e ∂(p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2 := by
    filter_upwards [Measure.support_mem_ae (μ := (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)))] with e he
    exact hf e he
  obtain ⟨σ, hσ, hmeasure, hmass, hcost, hvalue⟩ := exists_originalIndex_legal_windowCore_cost
    (0 : LegalMarkedPhysicalEdge q) p.1.1.1 hc hU.measurableSet hU.measurableSet
    source.2 target.2 (legalOriginalBlockRestriction_injective U p.2.1 hi.1)
    (legalOriginalBlockRestriction_injective U p.2.2 hi.2) hs ht
    (fun x y : LegalMarkedPhysicalPoint q ↦ x.2 < y.2) ha cost
  exact ⟨σ, hσ, hmeasure, hmass, hcost, hvalue,
    originalIndex_windowCore_source_deficit_eq_target_escape p.1.1.1 hU.measurableSet
      hU.measurableSet source.2 σ hs hmass⟩

end OTSelector.Reconstruction
