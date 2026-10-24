import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCountingPairSelection

/-! Borel completion of the actual option-valued original atom code.
Absent slots repeat a genuinely occupied atom; the empty case is kept separate. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

private theorem originalActualAnchorSelection (base : X) :
    ∃ choose : LocalFiniteMeasure X → X × X, Measurable choose ∧
      ∀ μ, IsLegalCountingMeasure base μ →
        (∃ x ∈ (μ : Measure X).support, ∃ y ∈ (μ : Measure X).support, True) →
          (choose μ).1 ∈ (μ : Measure X).support ∧
            (choose μ).2 ∈ (μ : Measure X).support ∧ True :=
  exists_measurable_originalCountingPair_selection base id measurable_id
    (fun _ _ ↦ True) MeasurableSet.univ

/-- The actual event that the original option code contains an occupied atom. -/
def originalCountingSupportActive (base : X) : Set (LocalFiniteMeasure X) :=
  {μ | ∃ n, originalCountingPairWitness base μ (fun _ ↦ True) n}

theorem measurableSet_originalCountingSupportActive (base : X) :
    MeasurableSet (originalCountingSupportActive base) :=
  measurableSet_exists_originalCountingPairWitness base id measurable_id
    (fun _ _ ↦ True) MeasurableSet.univ

theorem originalCountingSupportActive_iff (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) :
    μ ∈ originalCountingSupportActive base ↔ (μ : Measure X).support.Nonempty := by
  change (∃ n, originalCountingPairWitness base μ (fun _ ↦ True) n) ↔ _
  rw [exists_originalCountingPairWitness_iff base μ hμ (fun _ ↦ True)]
  constructor
  · rintro ⟨x, hx, _, _, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx, x, hx, trivial⟩

/-- On a nonempty actual integer measure this Borel anchor is an occupied atom. -/
def originalCountingActualAnchor (base : X) (μ : LocalFiniteMeasure X) : X :=
  ((originalActualAnchorSelection base).choose μ).1

theorem measurable_originalCountingActualAnchor (base : X) :
    Measurable (originalCountingActualAnchor base) :=
  (originalActualAnchorSelection base).choose_spec.1.fst

theorem originalCountingActualAnchor_mem_support (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (ha : μ ∈ originalCountingSupportActive base) :
    originalCountingActualAnchor base μ ∈ (μ : Measure X).support := by
  have hw := (exists_originalCountingPairWitness_iff base μ hμ (fun _ ↦ True)).mp ha
  exact ((originalActualAnchorSelection base).choose_spec.2 μ hμ hw).1

/-- Present slots retain their actual original atom. Every absent slot repeats
the same actual occupied anchor, so it never inserts a dummy spatial node. -/
def originalCountingCompletedAtom (base : X) (μ : LocalFiniteMeasure X) (n : ℕ) : X :=
  if originalCountingAtom base μ n = none then originalCountingActualAnchor base μ
  else originalCountingAtomPoint base μ n

theorem measurable_originalCountingCompletedAtom (base : X) (n : ℕ) :
    Measurable (fun μ ↦ originalCountingCompletedAtom base μ n) := by
  apply Measurable.ite
    (measurableSet_eq_fun (measurable_originalCountingAtom base n) measurable_const)
  · exact measurable_originalCountingActualAnchor base
  · exact measurable_originalCountingAtomPoint base n

theorem originalCountingCompletedAtom_eq_of_some (base : X) (μ : LocalFiniteMeasure X)
    {n : ℕ} {x : X} (hn : originalCountingAtom base μ n = some x) :
    originalCountingCompletedAtom base μ n = x := by
  rw [originalCountingCompletedAtom, ite_eq_right (by rw [hn]; simp)]
  exact originalCountingAtomPoint_eq_of_some base μ hn

theorem originalCountingCompletedAtom_mem_support (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (ha : μ ∈ originalCountingSupportActive base)
    (n : ℕ) : originalCountingCompletedAtom base μ n ∈ (μ : Measure X).support := by
  cases hn : originalCountingAtom base μ n with
  | none =>
    rw [originalCountingCompletedAtom, ite_eq_left hn]
    exact originalCountingActualAnchor_mem_support base μ hμ ha
  | some x =>
    rw [originalCountingCompletedAtom_eq_of_some base μ hn]
    exact originalCountingAtom_mem_support base μ hμ hn

/-- The completed code enumerates exactly the actual occupied support, with
only harmless repetitions and with no dummy or absent point in its range. -/
theorem range_originalCountingCompletedAtom (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (ha : μ ∈ originalCountingSupportActive base) :
    Set.range (originalCountingCompletedAtom base μ) = (μ : Measure X).support := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact originalCountingCompletedAtom_mem_support base μ hμ ha n
  · intro hx
    obtain ⟨n, hn⟩ := exists_originalCountingAtom base μ hμ hx
    exact ⟨n, originalCountingCompletedAtom_eq_of_some base μ hn⟩

end OTSelector.Reconstruction
