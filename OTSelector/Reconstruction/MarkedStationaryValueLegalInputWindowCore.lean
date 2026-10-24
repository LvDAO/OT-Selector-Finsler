import OTSelector.Reconstruction.MarkedStationaryValueLegalInputFiniteMatching

/-!
# Actual stationary-window restrictions in original finite indices

The full source and target input restrictions dominate the two marginals of
the same original edge restriction. The integer-plan extraction consequently
produces its actual legal partial matching on those finite arrays, with exact
measure, retained cardinality and signed cost. Its source deficiency is exactly
the actual source-window flux to targets outside the retained target window.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

section Projection
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Restricting both actual endpoints loses only target partners; the entire
original restricted source input still dominates the retained source measure. -/
theorem fst_restrict_prod_le_input_window (μ : Measure (X × Y))
    {U : Set X} (hU : MeasurableSet U) (V : Set Y) :
    (μ.restrict (U ×ˢ V)).fst ≤ μ.fst.restrict U := by
  change (μ.restrict (U ×ˢ V)).map Prod.fst ≤ (μ.map Prod.fst).restrict U
  rw [Measure.restrict_map measurable_fst hU]
  exact Measure.map_mono (Measure.restrict_mono (fun _ he ↦ he.1) le_rfl) measurable_fst

/-- The symmetric domination uses the same original edge restriction. -/
theorem snd_restrict_prod_le_input_window (μ : Measure (X × Y))
    (U : Set X) {V : Set Y} (hV : MeasurableSet V) :
    (μ.restrict (U ×ˢ V)).snd ≤ μ.snd.restrict V := by
  change (μ.restrict (U ×ˢ V)).map Prod.snd ≤ (μ.map Prod.snd).restrict V
  rw [Measure.restrict_map measurable_snd hV]
  exact Measure.map_mono (Measure.restrict_mono (fun _ he ↦ he.2) le_rfl) measurable_snd
end Projection

variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MetricSpace Y] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- The actual integer window core is represented on the original input
arrays. Its domination, legal graph, cardinality and original cost are all
proved from that same restriction, without an extension-capacity assumption. -/
theorem exists_originalIndex_legal_windowCore_cost
    {m n : ℕ} (base : X × Y) (μ : LocalFiniteMeasure (X × Y))
    (hc : IsLegalCountingMeasure base μ)
    {U : Set X} (hU : MeasurableSet U) {V : Set Y} (hV : MeasurableSet V)
    (source : Fin m → X) (target : Fin n → Y) (hs : Injective source) (ht : Injective target)
    (hsource : (μ : Measure (X × Y)).fst.restrict U = ∑ i, Measure.dirac (source i))
    (htarget : (μ : Measure (X × Y)).snd.restrict V = ∑ j, Measure.dirac (target j))
    (allowed : X → Y → Prop) (ha : ∀ᵐ e ∂(μ : Measure (X × Y)), allowed e.1 e.2)
    (cost : X × Y → ℝ) :
    ∃ σ : OTSelector.PartialMatching m n,
      PartialMatching.IsLegal (Finset.univ.filter (fun e ↦ allowed (source e.1) (target e.2))) σ ∧
      (μ : Measure (X × Y)).restrict (U ×ˢ V) =
        ∑ e ∈ σ.edges, Measure.dirac (source e.1, target e.2) ∧
      (μ : Measure (X × Y)) (U ×ˢ V) = (σ.card : ℝ≥0∞) ∧
      Integrable cost ((μ : Measure (X × Y)).restrict (U ×ˢ V)) ∧
      (∫ e in U ×ˢ V, cost e ∂(μ : Measure (X × Y))) = σ.cost (fun i j ↦ cost (source i, target j)) := by
  let core := legalInputRestrictionLocal (U ×ˢ V) μ
  have hcore : IsLegalCountingMeasure base core := isLegalCountingMeasure_restrict base μ hc _
  have hsrc : (core : Measure (X × Y)).fst ≤ ∑ i, Measure.dirac (source i) := by
    rw [← hsource]
    exact fst_restrict_prod_le_input_window (μ : Measure (X × Y)) hU V
  have htgt : (core : Measure (X × Y)).snd ≤ ∑ j, Measure.dirac (target j) := by
    rw [← htarget]
    exact snd_restrict_prod_le_input_window (μ : Measure (X × Y)) U hV
  obtain ⟨σ, hlegal, hmeasure, hmass, hi, hvalue⟩ :=
    exists_originalIndex_legal_partialMatching_cost_of_integer_plan base core hcore source target hs ht
      hsrc htgt allowed (ae_restrict_of_ae ha) cost
  refine ⟨σ, hlegal, hmeasure, ?_, hi, hvalue⟩
  simpa only [core, legalInputRestrictionLocal, Measure.restrict_apply_univ] using hmass

/-- Source-window deficiency is the actual retained plan's target escape
count, including all original dependence of the matching. -/
theorem originalIndex_windowCore_source_deficit_eq_target_escape
    {m n : ℕ} (μ : LocalFiniteMeasure (X × Y))
    {U : Set X} (hU : MeasurableSet U) {V : Set Y} (hV : MeasurableSet V)
    (source : Fin m → X) (σ : OTSelector.PartialMatching m n)
    (hsource : (μ : Measure (X × Y)).fst.restrict U = ∑ i, Measure.dirac (source i))
    (hmass : (μ : Measure (X × Y)) (U ×ˢ V) = (σ.card : ℝ≥0∞)) :
    ((m - σ.card : ℕ) : ℝ) = ((μ : Measure (X × Y)) (U ×ˢ Vᶜ)).toReal := by
  have hs : (μ : Measure (X × Y)).fst U = (m : ℝ≥0∞) := by
    have h := congrArg (fun ν : Measure X ↦ ν univ) hsource
    simpa only [Measure.restrict_apply_univ, Measure.finsetSum_apply, Measure.dirac_apply_of_mem,
      mem_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h
  have hsplit : (μ : Measure (X × Y)).fst U =
      (μ : Measure (X × Y)) (U ×ˢ V) + (μ : Measure (X × Y)) (U ×ˢ Vᶜ) := by
    rw [Measure.fst, Measure.map_apply measurable_fst hU]
    have heq : (Prod.fst ⁻¹' U : Set (X × Y)) = (U ×ˢ V) ∪ (U ×ˢ Vᶜ) := by
      ext e
      simp only [mem_preimage, mem_union, mem_prod, mem_compl_iff]
      tauto
    rw [heq]
    exact measure_union (by
      apply disjoint_left.mpr
      intro e he he'
      exact he'.2 he.2) (hU.prod hV.compl)
  have hfinite : (μ : Measure (X × Y)) (U ×ˢ Vᶜ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top m)
    rw [← hs, hsplit]
    exact le_add_left le_rfl
  rw [hs, hmass] at hsplit
  have h := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_natCast, ENNReal.toReal_add (ENNReal.natCast_ne_top _) hfinite,
    ENNReal.toReal_natCast] at h
  rw [Nat.cast_sub (σ.card_le.trans (min_le_left _ _))]
  linarith

end OTSelector.Reconstruction
