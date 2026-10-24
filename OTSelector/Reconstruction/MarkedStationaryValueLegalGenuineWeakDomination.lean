import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-!
# Whole input domination for actual weak laws of genuine stationary matchings

The existing closed compact-test carrier applies to every genuine full input
matching, independently of finite-optimum provenance. Actual weak limits
therefore retain both complete endpoint marginal inequalities on their own
unchanged colored inputs, including nonproper endpoint projections.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance markedStationaryValueLegalGenuineWeakDominationInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalGenuineWeakDominationPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Exact whole same-input marginals imply every existing compact endpoint
comparison, without any finite sample or optimizer provenance. -/
theorem IsFullOriginalInputMatching.testDomination
    {q : ℕ} {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s) :
    legalMarkedInputTestDomination q s := by
  intro f hf g hg
  have hsI : Integrable f (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst := by
    rw [hs.source_marginal]
    exact f.integrable
  have htI : Integrable f (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd := by
    rw [hs.target_marginal]
    exact f.integrable
  have hscomp : Integrable (fun e : LegalMarkedPhysicalEdge q ↦ f e.1)
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) :=
    (integrable_map_measure f.continuous.aestronglyMeasurable measurable_fst.aemeasurable).mp hsI
  have htcomp : Integrable (fun e : LegalMarkedPhysicalEdge q ↦ f e.2)
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) :=
    (integrable_map_measure f.continuous.aestronglyMeasurable measurable_snd.aemeasurable).mp htI
  have hsource : (∫ e, cavityProductTest f g e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) ≤
      ∫ e, f e.1 ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) :=
    integral_mono (cavityProductTest f g).integrable hscomp
      (fun e ↦ mul_le_of_le_one_right (hf _) (hg _).2)
  have htarget : (∫ e, cavityProductTest g f e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) ≤
      ∫ e, f e.2 ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) :=
    integral_mono (cavityProductTest g f).integrable htcomp
      (fun e ↦ mul_le_of_le_one_left (hf _) (hg _).2)
  constructor
  · change (∫ e, cavityProductTest f g e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) ≤ _
    rw [← integral_legalInputColorMeasure, ← hs.source_marginal,
      Measure.fst, integral_map (f := fun x ↦ f x)
        measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    exact hsource
  · change (∫ e, cavityProductTest g f e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) ≤ _
    rw [← integral_legalInputColorMeasure, ← hs.target_marginal,
      Measure.snd, integral_map (f := fun x ↦ f x)
        measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    exact htarget

/-- The existing simultaneous closed carrier survives weak convergence of
arbitrary genuine fixed-input laws, independently of original finite optima. -/
theorem ae_testDomination_of_genuineStationary_tendsto
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hweak : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)), legalMarkedInputTestDomination q s := by
  let K : Set (LegalMarkedOptimalInputScene q) := {s | legalMarkedInputTestDomination q s}
  have hK : IsClosed K := isClosed_legalMarkedInputTestDomination q
  have hn (n : ℕ) : ((M n).law : Measure (LegalMarkedOptimalInputScene q)) Kᶜ = 0 :=
    ae_iff.mp ((M n).full_matching.mono (fun _ hs ↦ hs.testDomination))
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl
  simp only [hn, liminf_const] at hport
  exact le_antisymm hport bot_le

/-- Both whole endpoint marginals of the same actual limiting scene are
dominated by their own full original input colors, on one common AE event. -/
theorem ae_marginals_le_input_of_genuineStationary_tendsto
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hweak : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst ≤ legalInputColorMeasure q s.2 0 ∧
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd ≤ legalInputColorMeasure q s.2 1 := by
  filter_upwards [ae_testDomination_of_genuineStationary_tendsto M Q hweak] with s hs
  exact legalMarkedInput_marginals_le_of_testDomination q s hs

end OTSelector.Reconstruction
