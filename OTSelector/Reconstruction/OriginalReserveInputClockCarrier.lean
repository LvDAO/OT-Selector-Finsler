import OTSelector.Reconstruction.OriginalStageClockSlabsSupport

/-! The whole unchanged input inherits the actual compact clock carrier from its true Palm clocks. -/
open Set Function MeasureTheory Filter
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The two immutable color readouts exhaust the whole original input measure. -/
theorem originalColoredInput_ae_clock_of_color_readouts {q : ℕ}
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) {A : Set ℝ}
    (hsource : ∀ᵐ p ∂legalInputColorMeasure q μ 0, p.2 ∈ A)
    (htarget : ∀ᵐ p ∂legalInputColorMeasure q μ 1, p.2 ∈ A) :
    ∀ᵐ p ∂(μ : Measure (LegalColoredInputPoint q)), p.1.2 ∈ A := by
  have hs : ∀ᵐ p ∂(μ : Measure (LegalColoredInputPoint q)).restrict {p | p.2 = 0},
      p.1.2 ∈ A := ae_of_ae_map measurable_fst.aemeasurable hsource
  have ht : ∀ᵐ p ∂(μ : Measure (LegalColoredInputPoint q)).restrict {p | p.2 = 1},
      p.1.2 ∈ A := ae_of_ae_map measurable_fst.aemeasurable htarget
  have hcolor : ({p : LegalColoredInputPoint q | p.2 = 0} : Set _)ᶜ = {p | p.2 = 1} := by
    ext p
    have hp : p.2 = 0 ∨ p.2 = 1 := by omega
    rcases hp with h | h <;> simp [h]
  have hset : MeasurableSet {p : LegalColoredInputPoint q | p.2 = 0} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hsplit := Measure.restrict_add_restrict_compl hset
    (μ := (μ : Measure (LegalColoredInputPoint q)))
  rw [hcolor] at hsplit
  rw [← hsplit, ae_add_measure_iff]
  exact ⟨hs, ht⟩

/-- The actual full matching and its unchanged Palm marginals put every original
input clock in its common Borel carrier. No law is asserted for selected ports. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_originalInput_clockCarrier
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A : Set ℝ} (hA : MeasurableSet A) (hα : α.support ⊆ A) (hβ : β.support ⊆ A) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ p ∂(scene.2 : Measure (LegalColoredInputPoint q)), p.1.2 ∈ A := by
  filter_upwards [Q.full_matching, Q.ae_ae_originalEdges_clock_support]
    with scene hfull hedge
  apply originalColoredInput_ae_clock_of_color_readouts
  · rw [← hfull.source_marginal]
    apply (ae_map_iff measurable_fst.aemeasurable (hA.preimage measurable_snd)).mpr
    exact hedge.mono fun e he ↦ hα he.1
  · rw [← hfull.target_marginal]
    apply (ae_map_iff measurable_snd.aemeasurable (hA.preimage measurable_snd)).mpr
    exact hedge.mono fun e he ↦ hβ he.2

end OTSelector.Reconstruction
