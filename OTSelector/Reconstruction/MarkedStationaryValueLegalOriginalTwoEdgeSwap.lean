import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual legal two-edge swaps of the original full matching

A swap deletes the two selected unit edge atoms and inserts their crossed
partners. Its complete original input, source projection and target projection
are unchanged. The new plan remains an actual full integer matching.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false

private theorem originalCycleFiniteOnCompactsAdd
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (μ + ν) where
  lt_top_of_isCompact K hK := by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩

section Counting
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- Addition of two actual integer plans retains their actual integer carrier. -/
theorem isLegalCountingMeasure_add (base : X) (μ ν : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (hν : IsLegalCountingMeasure base ν) :
    IsLegalCountingMeasure base ⟨(μ : Measure X) + ν, originalCycleFiniteOnCompactsAdd _ _⟩ := by
  obtain ⟨c, hc⟩ := hμ
  obtain ⟨d, hd⟩ := hν
  refine ⟨fun n ↦ c n + d n, ?_⟩
  apply Subtype.ext
  change LocalConfiguration.countingMeasure (fun n ↦ c n + d n) =
    (μ : Measure X) + (ν : Measure X)
  have hsum : LocalConfiguration.countingMeasure (fun n ↦ c n + d n) =
      LocalConfiguration.countingMeasure c + LocalConfiguration.countingMeasure d := by
    calc
      _ = Measure.sum (fun n ↦ LocalConfiguration.shellMeasure c n +
          LocalConfiguration.shellMeasure d n) := by
        apply congrArg Measure.sum
        funext n
        simp only [LocalConfiguration.shellMeasure, Multiset.map_add, Multiset.sum_add]
      _ = _ := (Measure.sum_add_sum _ _).symm
  exact hsum.trans (congrArg₂ (fun a b : Measure X ↦ a + b)
    (congrArg Subtype.val hc) (congrArg Subtype.val hd))

/-- A newly inserted edge is its actual unit Dirac atom. -/
theorem isLegalCountingMeasure_dirac (base x : X) :
    IsLegalCountingMeasure base ⟨Measure.dirac x, inferInstance⟩ := by
  refine ⟨LocalConfiguration.ofTuple base (fun _ : Fin 1 ↦ x), ?_⟩
  apply Subtype.ext
  change LocalConfiguration.countingMeasure
    (LocalConfiguration.ofTuple base (fun _ : Fin 1 ↦ x)) = Measure.dirac x
  simp only [LocalConfiguration.countingMeasure_ofTuple, Fin.sum_univ_one]

/-- Two distinct occupied unit atoms split off the same original measure exactly. -/
theorem measure_eq_restrict_compl_add_two_dirac (μ : Measure X) {e f : X}
    (hne : e ≠ f) (he : μ {e} = 1) (hf : μ {f} = 1) :
    μ = μ.restrict ({e, f} : Set X)ᶜ + Measure.dirac e + Measure.dirac f := by
  have hpair : μ.restrict ({e, f} : Set X) = Measure.dirac e + Measure.dirac f := by
    rw [show ({e, f} : Set X) = {e} ∪ {f} by ext x; simp [or_comm],
      Measure.restrict_union (disjoint_singleton.mpr hne) (measurableSet_singleton f),
      Measure.restrict_singleton, Measure.restrict_singleton, he, hf, one_smul, one_smul]
  calc
    μ = μ.restrict ({e, f} : Set X)ᶜ + μ.restrict ({e, f} : Set X) :=
      (Measure.restrict_compl_add_restrict (by measurability)).symm
    _ = _ := by rw [hpair, add_assoc]
end Counting

/-- The actual new matching plan after exchanging the two selected targets. -/
def originalTwoEdgeSwapPlan {q : ℕ}
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (e f : LegalMarkedPhysicalEdge q) : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨(μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
    Measure.dirac (e.1, f.2) + Measure.dirac (f.1, e.2), by
      have h₁ := originalCycleFiniteOnCompactsAdd
        ((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ)
        (Measure.dirac (e.1, f.2))
      let : IsFiniteMeasureOnCompacts
        ((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
          Measure.dirac (e.1, f.2)) := h₁
      exact originalCycleFiniteOnCompactsAdd _ _⟩

/-- The joint scene retains its complete original colored input pointwise. -/
def originalTwoEdgeSwapScene {q : ℕ} (s : LegalMarkedOptimalInputScene q)
    (e f : LegalMarkedPhysicalEdge q) : LegalMarkedOptimalInputScene q :=
  ((originalTwoEdgeSwapPlan s.1.1 e f, s.1.2), s.2)

@[simp] theorem originalTwoEdgeSwapScene_input {q : ℕ}
    (s : LegalMarkedOptimalInputScene q) (e f : LegalMarkedPhysicalEdge q) :
    (originalTwoEdgeSwapScene s e f).2 = s.2 := rfl

/-- Occupied edge atoms of an actual full matching have exactly unit mass. -/
theorem IsFullOriginalInputMatching.edge_singleton_eq_one {q : ℕ}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    {e : LegalMarkedPhysicalEdge q} (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) {e} = 1 := by
  obtain ⟨hc, hunit⟩ := (isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges
  exact le_antisymm (hunit e) (one_le_singleton_of_mem_support_of_legalCounting _ _ hc he)

/-- The swap remains integer without invoking a new random input law. -/
theorem isLegalCountingMeasure_originalTwoEdgeSwapPlan {q : ℕ}
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    (hμ : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) μ)
    (e f : LegalMarkedPhysicalEdge q) :
    IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) (originalTwoEdgeSwapPlan μ e f) := by
  let μ₀ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
    ⟨(μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ, inferInstance⟩
  let μ₁ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
    ⟨Measure.dirac (e.1, f.2), inferInstance⟩
  let μ₂ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
    ⟨Measure.dirac (f.1, e.2), inferInstance⟩
  have h₀ : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) μ₀ :=
    isLegalCountingMeasure_restrict _ μ hμ _
  have h₁ : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) μ₁ :=
    isLegalCountingMeasure_dirac _ _
  have h₂ : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) μ₂ :=
    isLegalCountingMeasure_dirac _ _
  have hadd := isLegalCountingMeasure_add (0 : LegalMarkedPhysicalEdge q) μ₀ μ₁ h₀ h₁
  exact isLegalCountingMeasure_add (0 : LegalMarkedPhysicalEdge q)
    ⟨(μ₀ : Measure (LegalMarkedPhysicalEdge q)) + μ₁,
      originalCycleFiniteOnCompactsAdd _ _⟩ μ₂ hadd h₂

/-- Exchanging two targets preserves the entire original source and target marginals. -/
theorem originalTwoEdgeSwapPlan_marginals {q : ℕ}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    {e f : LegalMarkedPhysicalEdge q} (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support)
    (hf : f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) (hne : e ≠ f) :
    (originalTwoEdgeSwapPlan s.1.1 e f : Measure (LegalMarkedPhysicalEdge q)).fst = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst ∧
      (originalTwoEdgeSwapPlan s.1.1 e f : Measure (LegalMarkedPhysicalEdge q)).snd = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd := by
  have hdec := measure_eq_restrict_compl_add_two_dirac (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
    hne (hs.edge_singleton_eq_one he) (hs.edge_singleton_eq_one hf)
  constructor
  · change (((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
      Measure.dirac (e.1, f.2)) + Measure.dirac (f.1, e.2)).fst = _
    conv_rhs => rw [hdec]
    simp only [Measure.fst_add]
    simp only [Measure.fst, Measure.map_dirac]
  · change (((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
      Measure.dirac (e.1, f.2)) + Measure.dirac (f.1, e.2)).snd = _
    conv_rhs => rw [hdec]
    simp only [Measure.snd_add]
    simp only [Measure.snd, Measure.map_dirac]
    abel


/-- An actual two-edge swap is still a full one-to-one matching of precisely
all the same original input atoms and immutable colors. -/
theorem IsFullOriginalInputMatching.twoEdgeSwap {q : ℕ}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    {e f : LegalMarkedPhysicalEdge q} (he : e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support)
    (hf : f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support) (hne : e ≠ f) :
    IsFullOriginalInputMatching q (originalTwoEdgeSwapScene s e f) := by
  obtain ⟨hc, _⟩ := (isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges
  obtain ⟨hmS, hmT⟩ := originalTwoEdgeSwapPlan_marginals hs he hf hne
  apply isFullOriginalInputMatching_of_counting_simple_marginals
  · exact isLegalCountingMeasure_originalTwoEdgeSwapPlan s.1.1 hc e f
  · exact hs.simple_inputs
  · exact ⟨hmS.trans hs.source_marginal, hmT.trans hs.target_marginal⟩

/-- The only possible new support edges are the two chosen crossed partners. -/
theorem support_originalTwoEdgeSwapPlan_subset {q : ℕ}
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) (e f : LegalMarkedPhysicalEdge q) :
    (originalTwoEdgeSwapPlan μ e f : Measure (LegalMarkedPhysicalEdge q)).support ⊆
      (μ : Measure (LegalMarkedPhysicalEdge q)).support ∪ {(e.1, f.2), (f.1, e.2)} := by
  have hdir (x : LegalMarkedPhysicalEdge q) : (Measure.dirac x).support ⊆ {x} :=
    Measure.support_subset_of_isClosed isClosed_singleton (by simp)
  intro x hx
  change x ∈ (((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
    Measure.dirac (e.1, f.2)) + Measure.dirac (f.1, e.2)).support at hx
  rw [Measure.support_add, Measure.support_add] at hx
  rcases hx with (hx | hx) | hx
  · exact Or.inl (Measure.support_mono Measure.restrict_le_self hx)
  · exact Or.inr (by simp only [mem_insert_iff, mem_singleton_iff]; exact Or.inl (hdir _ hx))
  · exact Or.inr (by simp only [mem_insert_iff, mem_singleton_iff]; exact Or.inr (hdir _ hx))

/-- Legal crossed clock pairs preserve strict forward matching on the whole new plan. -/
theorem forward_originalTwoEdgeSwapScene {q : ℕ} (s : LegalMarkedOptimalInputScene q)
    (hforward : ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (e f : LegalMarkedPhysicalEdge q) (hcross₁ : e.1.2 < f.2.2)
    (hcross₂ : f.1.2 < e.2.2) :
    ∀ x ∈ ((originalTwoEdgeSwapScene s e f).1.1 : Measure (LegalMarkedPhysicalEdge q)).support, x.1.2 < x.2.2 := by
  intro x hx
  rcases support_originalTwoEdgeSwapPlan_subset s.1.1 e f hx with hx | hx
  · exact hforward x hx
  · simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hcross₁
    · exact hcross₂

/-- Every integrable original edge observable stays integrable after the finite swap. -/
theorem integrable_originalTwoEdgeSwapPlan {q : ℕ}
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) (e f : LegalMarkedPhysicalEdge q)
    {c : LegalMarkedPhysicalEdge q → ℝ} (hc : Integrable c (μ : Measure (LegalMarkedPhysicalEdge q))) :
    Integrable c (originalTwoEdgeSwapPlan μ e f : Measure (LegalMarkedPhysicalEdge q)) := by
  change Integrable c (((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
    Measure.dirac (e.1, f.2)) + Measure.dirac (f.1, e.2))
  exact (hc.restrict.add_measure (integrable_dirac (by finiteness))).add_measure
    (integrable_dirac (by finiteness))

/-- The exact signed cost change is the actual two-edge exchange gain. -/
theorem integral_originalTwoEdgeSwapPlan {q : ℕ}
    (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) {e f : LegalMarkedPhysicalEdge q}
    (hne : e ≠ f) (he : (μ : Measure (LegalMarkedPhysicalEdge q)) {e} = 1) (hf : (μ : Measure (LegalMarkedPhysicalEdge q)) {f} = 1)
    {c : LegalMarkedPhysicalEdge q → ℝ} (hc : Integrable c (μ : Measure (LegalMarkedPhysicalEdge q))) :
    (∫ x, c x ∂(originalTwoEdgeSwapPlan μ e f : Measure (LegalMarkedPhysicalEdge q))) =
      (∫ x, c x ∂(μ : Measure (LegalMarkedPhysicalEdge q))) - c e - c f + c (e.1, f.2) + c (f.1, e.2) := by
  have hold := congrArg (fun ν : Measure (LegalMarkedPhysicalEdge q) ↦ ∫ x, c x ∂ν)
    (measure_eq_restrict_compl_add_two_dirac (μ : Measure (LegalMarkedPhysicalEdge q)) hne he hf)
  have hbase : Integrable c ((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ) := hc.restrict
  rw [integral_add_measure (hbase.add_measure (integrable_dirac (by finiteness))) (integrable_dirac (by finiteness)),
    integral_add_measure hbase (integrable_dirac (by finiteness)), integral_dirac, integral_dirac] at hold
  change (∫ x, c x ∂(((μ : Measure (LegalMarkedPhysicalEdge q)).restrict ({e, f} : Set _)ᶜ +
    Measure.dirac (e.1, f.2)) + Measure.dirac (f.1, e.2))) = _
  rw [integral_add_measure (hbase.add_measure (integrable_dirac (by finiteness))) (integrable_dirac (by finiteness)),
    integral_add_measure hbase (integrable_dirac (by finiteness)), integral_dirac, integral_dirac]
  linarith

end OTSelector.Reconstruction
