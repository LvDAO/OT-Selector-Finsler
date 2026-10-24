import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-!
# Tight original scalar cuts carry no stationary matching edges

Forwardness and the two exact original clock marginals identify the crossing
mass at each deterministic scalar cut. A tight cut therefore has zero crossing
Palm mass, without ordering the original supports or changing their inputs.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance markedStationaryValueLegalStationaryTightCutInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryTightCutPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Actual forward clock crossing mass is the difference between the two
original prefix masses, expressed without subtracting extended infinities. -/
theorem measure_forward_clock_crossing_add_target_prefix
    (q : ℕ) (η : Measure (PhysicalPairPalmMark (Fin q))) (α β : Measure ℝ)
    (hsource : η.map (fun m ↦ m.1.1) = α) (htarget : η.map (fun m ↦ m.1.2) = β)
    (hforward : ∀ᵐ m ∂η, m.1.1 ≤ m.1.2) (c : ℝ) :
    η {m | m.1.1 ≤ c ∧ c < m.1.2} + β (Iic c) = α (Iic c) := by
  have hs : η {m | m.1.1 ≤ c} = α (Iic c) := by
    rw [← hsource, Measure.map_apply measurable_fst.fst measurableSet_Iic]
    rfl
  have ht : η {m | m.1.2 ≤ c} = β (Iic c) := by
    rw [← htarget, Measure.map_apply measurable_fst.snd measurableSet_Iic]
    rfl
  rw [← hs, ← ht, ← measure_union]
  · apply measure_congr
    filter_upwards [hforward] with m hm
    change ((m.1.1 ≤ c ∧ c < m.1.2) ∨ m.1.2 ≤ c) = (m.1.1 ≤ c)
    apply propext
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hm.trans h
    · intro h
      by_cases ht : m.1.2 ≤ c
      · exact Or.inr ht
      · exact Or.inl ⟨h, lt_of_not_ge ht⟩
  · apply disjoint_left.mpr
    intro m hm hn
    exact (not_lt_of_ge hn) hm.2
  · exact measurableSet_le measurable_fst.snd measurable_const

/-- A tight original prefix cut has zero forward crossing mass. -/
theorem measure_forward_clock_crossing_eq_zero_of_tight
    (q : ℕ) (η : Measure (PhysicalPairPalmMark (Fin q))) (α β : Measure ℝ) [IsFiniteMeasure β]
    (hsource : η.map (fun m ↦ m.1.1) = α) (htarget : η.map (fun m ↦ m.1.2) = β)
    (hforward : ∀ᵐ m ∂η, m.1.1 ≤ m.1.2) (c : ℝ)
    (hcut : α (Iic c) = β (Iic c)) : η {m | m.1.1 ≤ c ∧ c < m.1.2} = 0 := by
  have h := measure_forward_clock_crossing_add_target_prefix q η α β hsource htarget hforward c
  rw [hcut] at h
  exact (ENNReal.add_left_inj (measure_ne_top β (Iic c))).mp (by simpa only [zero_add] using h)

/-- Strict forwardness of the genuine full original matching also holds in
its own actual full-displacement Palm law. -/
theorem LegalWeightedStationaryPoissonMatching.ae_palm_forward
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ m ∂legalMarkedJointPalm q M.law, m.1.1 < m.1.2 := by
  have hplan : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2 := by
    filter_upwards [M.forward] with s hs
    filter_upwards [Measure.support_mem_ae (μ := (s.1.1 : Measure (LegalMarkedPhysicalEdge q)))] with e he
    exact hs e he
  have hbad : MeasurableSet {e : LegalMarkedPhysicalEdge q | ¬ e.1.2 < e.2.2} :=
    (measurableSet_lt measurable_fst.snd measurable_snd.snd).compl
  have hm : Measurable (fun scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      (scene.1 : Measure (LegalMarkedPhysicalEdge q)) {e | ¬ e.1.2 < e.2.2}) :=
    (Measure.measurable_coe hbad).comp (measurable_localFiniteMeasure_coe.comp measurable_fst)
  have hS : MeasurableSet {scene : CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) |
      ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2} := by
    simpa only [ae_iff] using measurableSet_eq_fun hm (measurable_const (a := (0 : ℝ≥0∞)))
  have hpair : ∀ᵐ scene ∂(legalMarkedInputPairLaw q M.law : Measure
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))),
      ∀ᵐ e ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2 := by
    exact (ae_map_iff measurable_fst.aemeasurable hS).mpr hplan
  exact ae_cubePalm_physicalScene_forward _ hpair

/-- Every original weighted stationary competitor stays on one side of every
tight scalar cut in its own Palm law, including interleaved populations. -/
theorem LegalWeightedStationaryPoissonMatching.palm_crossing_eq_zero_of_tight
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c : ℝ) (hcut : α (Iic c) = β (Iic c)) :
    legalMarkedJointPalm q M.law {m | m.1.1 ≤ c ∧ c < m.1.2} = 0 := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have : IsProbabilityMeasure ((legalMarkedJointPalm q M.law).map (fun m ↦ m.1.2)) :=
    Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have : IsProbabilityMeasure β := M.target_clock ▸ this
  exact measure_forward_clock_crossing_eq_zero_of_tight q _ α β M.source_clock M.target_clock
    (M.ae_palm_forward.mono (fun _ h ↦ h.le)) c hcut

end OTSelector.Reconstruction
