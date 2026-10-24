import OTSelector.Reconstruction.MarkedStationaryValueLegalCanonicalInputCompactness

/-! # Actual first matching/input readouts of canonical weak limits -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local instance canonicalFirstInputWeakReadoutColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance canonicalFirstInputWeakReadoutInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance canonicalFirstInputWeakReadoutPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Canonical scene convergence gives weak convergence of the original
unchanged first-matching/input joint law, without resampling either object. -/
theorem tendsto_originalFirstInputLaw_of_canonical_tendsto
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hw : Tendsto (fun n ↦ legalMarkedCanonicalFirstInputLaw q (M n).law) atTop (𝓝 Q)) :
    Tendsto (fun n ↦ (M n).law.map (measurable_fst.fst.prodMk measurable_snd).aemeasurable)
      atTop (𝓝 (Q.map (measurable_fst.fst.prodMk measurable_snd).aemeasurable)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ Q hw
    (continuous_fst.fst.prodMk continuous_snd)
  have he (n : ℕ) :
      (legalMarkedCanonicalFirstInputLaw q (M n).law).map
        (measurable_fst.fst.prodMk measurable_snd).aemeasurable =
      (M n).law.map (measurable_fst.fst.prodMk measurable_snd).aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    exact map_canonicalFirstInputLaw_first_input q (M n).law
  simpa only [he] using ht

/-- The unused second slot stays equal to the same first matching in every
actual canonical weak limit. No endpoint-marginal fullness is inferred. -/
theorem ae_diagonal_of_canonicalFirstInputLaw_tendsto
    {q : ℕ} (P : ℕ → ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hw : Tendsto (fun n ↦ legalMarkedCanonicalFirstInputLaw q (P n)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)), s.1.1 = s.1.2 := by
  let K : Set (LegalMarkedOptimalInputScene q) := {s | s.1.1 = s.1.2}
  have hK : IsClosed K := isClosed_eq continuous_fst.fst continuous_fst.snd
  have hn (n : ℕ) :
      (legalMarkedCanonicalFirstInputLaw q (P n) : Measure (LegalMarkedOptimalInputScene q)) Kᶜ = 0 := by
    change ∀ᵐ s ∂(P n : Measure (LegalMarkedOptimalInputScene q)).map
      (legalMarkedCanonicalFirstInputScene q), s ∈ K
    apply (ae_map_iff (continuous_legalMarkedCanonicalFirstInputScene q).measurable.aemeasurable
      hK.measurableSet).mpr
    exact .of_forall fun s ↦ rfl
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hw hK.isOpen_compl
  change (Q : Measure (LegalMarkedOptimalInputScene q)) Kᶜ ≤
    atTop.liminf (fun n ↦ (legalMarkedCanonicalFirstInputLaw q (P n) :
      Measure (LegalMarkedOptimalInputScene q)) Kᶜ) at hle
  simp only [hn, liminf_const] at hle
  exact le_antisymm hle bot_le

/-- Actual first matching and complete input measures stay integer counting
under weak limits of arbitrary genuine original matching laws. Simplicity and
full endpoint marginals are separate nonproper-projection assertions. -/
theorem ae_counting_of_genuineStationary_tendsto
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hw : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1 ∧
        IsLegalCountingMeasure (0 : LegalColoredInputPoint q) s.2 := by
  let K : Set (LegalMarkedOptimalInputScene q) := {s |
    IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1 ∧
      IsLegalCountingMeasure (0 : LegalColoredInputPoint q) s.2}
  have hK : IsClosed K :=
    ((isClosed_isLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)).preimage
      continuous_fst.fst).inter
        ((isClosed_isLegalCountingMeasure (0 : LegalColoredInputPoint q)).preimage continuous_snd)
  have hn (n : ℕ) : ((M n).law : Measure (LegalMarkedOptimalInputScene q)) Kᶜ = 0 := by
    filter_upwards [(M n).full_matching] with s hs
    exact ⟨((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1,
      ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_inputs).1⟩
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hw hK.isOpen_compl
  change (Q : Measure (LegalMarkedOptimalInputScene q)) Kᶜ ≤
    atTop.liminf (fun n ↦ ((M n).law : Measure (LegalMarkedOptimalInputScene q)) Kᶜ) at hle
  simp only [hn, liminf_const] at hle
  exact le_antisymm hle bot_le

end OTSelector.Reconstruction
