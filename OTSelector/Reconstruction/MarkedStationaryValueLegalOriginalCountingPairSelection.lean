import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCounting
import OTSelector.PointProcess.LocalConfiguration.CloudTopology

/-!
# Measurable selection of actual original edge pairs

The existing shell multiset code enumerates the very integer measure already
present in a scene. A countable first-witness construction selects a pair for
any Borel local exchange certificate; it does not resample its endpoints.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [StandardBorelSpace X]
local instance originalPairSelectionConfigurationTopology (base : X) :
    TopologicalSpace (LocalConfiguration base) := LocalConfiguration.vagueTopology base
local instance originalPairSelectionConfigurationBorel (base : X) :
    BorelSpace (LocalConfiguration base) := LocalConfiguration.vagueBorelSpace

/-- Decode the actual integer measure through its established measurable embedding. -/
def originalCountingDecode (base : X) : LocalFiniteMeasure X → LocalConfiguration base :=
  LocalConfiguration.isClosedEmbedding_toLocalFiniteMeasure.measurableEmbedding.invFun

@[fun_prop] theorem measurable_originalCountingDecode (base : X) :
    Measurable (originalCountingDecode base) :=
  LocalConfiguration.isClosedEmbedding_toLocalFiniteMeasure.measurableEmbedding.measurable_invFun

/-- On the actual integer carrier, decoding loses no original point or multiplicity. -/
theorem originalCountingDecode_eq_of_counting (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) :
    LocalConfiguration.toLocalFiniteMeasure (originalCountingDecode base μ) = μ := by
  obtain ⟨c, rfl⟩ := hμ
  congr 1
  exact LocalConfiguration.isClosedEmbedding_toLocalFiniteMeasure.measurableEmbedding.leftInverse_invFun c

/-- The countable actual atom code has an explicit absent slot, so an empty
shell never creates an artificial edge at the base point. -/
private def originalCountingAtomAtPair (base : X) (μ : LocalFiniteMeasure X)
    (p : ℕ × ℕ) : Option X :=
  ((MultisetEncoding.paddedCode (originalCountingDecode base μ p.1)).2 p.2).elim
    none (fun x ↦ some x.val)

def originalCountingAtom (base : X) (μ : LocalFiniteMeasure X) (n : ℕ) : Option X :=
  originalCountingAtomAtPair base μ (Nat.unpair n)

@[fun_prop] theorem measurable_originalCountingAtom (base : X) (n : ℕ) :
    Measurable (fun μ ↦ originalCountingAtom base μ n) := by
  exact (MeasureTheory.Option.measurable_elim none
    (MeasureTheory.Option.measurable_some.comp measurable_subtype_coe)).comp
      ((measurable_pi_apply (Nat.unpair n).2).comp (measurable_snd.comp
        (MultisetEncoding.measurable_paddedCode.comp
          ((measurable_pi_apply (Nat.unpair n).1).comp (measurable_originalCountingDecode base)))))

/-- Every occupied original integer atom occurs in the measurable code. -/
theorem exists_originalCountingAtom (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) {x : X} (hx : x ∈ (μ : Measure X).support) :
    ∃ n, originalCountingAtom base μ n = some x := by
  let c := originalCountingDecode base μ
  have heq : LocalConfiguration.countingMeasure c = (μ : Measure X) :=
    congrArg Subtype.val (originalCountingDecode_eq_of_counting base μ hμ)
  rw [← heq, LocalConfiguration.support_countingMeasure] at hx
  let j := LocalConfiguration.shellIndex base x
  let p : LocalConfiguration.Shell base j := ⟨x, rfl⟩
  have hp : p ∈ c j := Multiset.count_ne_zero.mp hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
    ((Multiset.mem_sort (MultisetEncoding.codingLE _)).mpr hp)
  refine ⟨Nat.pair j k, ?_⟩
  rw [originalCountingAtom, Nat.unpair_pair]
  change ((MultisetEncoding.paddedCode (c j)).2 k).elim none (fun x ↦ some x.val) = some x
  rw [show (MultisetEncoding.paddedCode (c j)).2 k = some p from hk]
  rfl

/-- Every present code slot is an actually occupied original atom. -/
theorem originalCountingAtom_mem_support (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) {n : ℕ} {x : X}
    (hn : originalCountingAtom base μ n = some x) : x ∈ (μ : Measure X).support := by
  let c := originalCountingDecode base μ
  have heq : LocalConfiguration.countingMeasure c = (μ : Measure X) :=
    congrArg Subtype.val (originalCountingDecode_eq_of_counting base μ hμ)
  rw [← heq, LocalConfiguration.support_countingMeasure]
  unfold originalCountingAtom originalCountingAtomAtPair at hn
  cases hp : (MultisetEncoding.paddedCode
      (originalCountingDecode base μ (Nat.unpair n).1)).2 (Nat.unpair n).2 with
  | none => simp [hp] at hn
  | some p =>
    simp only [hp, Option.elim_some, Option.some.injEq] at hn
    subst x
    change LocalConfiguration.multiplicity c p.val ≠ 0
    rw [LocalConfiguration.multiplicity_shell]
    exact Multiset.count_ne_zero.mpr ((Multiset.mem_sort (MultisetEncoding.codingLE _)).mp
      (List.mem_iff_getElem?.mpr ⟨(Nat.unpair n).2, hp⟩))

/-- The corresponding measurable point readout; absent slots return the explicit base. -/
def originalCountingAtomPoint (base : X) (μ : LocalFiniteMeasure X) (n : ℕ) : X :=
  (originalCountingAtom base μ n).elim base id

@[fun_prop] theorem measurable_originalCountingAtomPoint (base : X) (n : ℕ) :
    Measurable (fun μ ↦ originalCountingAtomPoint base μ n) :=
  (MeasureTheory.Option.measurable_elim base measurable_id).comp
    (measurable_originalCountingAtom base n)

/-- A present atom readout returns its original physical endpoint exactly. -/
theorem originalCountingAtomPoint_eq_of_some (base : X) (μ : LocalFiniteMeasure X)
    {n : ℕ} {x : X} (hn : originalCountingAtom base μ n = some x) :
    originalCountingAtomPoint base μ n = x := by simp [originalCountingAtomPoint, hn]

/-- A present slot returns an actually occupied original atom, including at the base. -/
theorem originalCountingAtomPoint_mem_support_of_present
    (base : X) (μ : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ)
    (n : ℕ) (hn : (originalCountingAtom base μ n).isSome = true) :
    originalCountingAtomPoint base μ n ∈ (μ : Measure X).support := by
  cases h : originalCountingAtom base μ n with
  | none => simp [h] at hn
  | some x =>
    rw [originalCountingAtomPoint_eq_of_some base μ h]
    exact originalCountingAtom_mem_support base μ hμ h

/-- All ordered pairs in the original atom code, with an explicit countable index. -/
def originalCountingPair (base : X) (μ : LocalFiniteMeasure X) (n : ℕ) : X × X :=
  (originalCountingAtomPoint base μ (Nat.unpair n).1,
    originalCountingAtomPoint base μ (Nat.unpair n).2)

@[fun_prop] theorem measurable_originalCountingPair (base : X) (n : ℕ) :
    Measurable (fun μ ↦ originalCountingPair base μ n) :=
  (measurable_originalCountingAtomPoint base _).prodMk
    (measurable_originalCountingAtomPoint base _)

/-- Both slots must be occupied original atoms before a pair is eligible. -/
def originalCountingPairWitness (base : X) (μ : LocalFiniteMeasure X)
    (R : X × X → Prop) (n : ℕ) : Prop :=
  (originalCountingAtom base μ (Nat.unpair n).1).isSome = true ∧
    (originalCountingAtom base μ (Nat.unpair n).2).isSome = true ∧
      R (originalCountingPair base μ n)

/-- A Borel exchange certificate on the original support has a countable coded witness. -/
theorem exists_originalCountingPairWitness_iff (base : X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (R : X × X → Prop) :
    (∃ n, originalCountingPairWitness base μ R n) ↔
      ∃ x ∈ (μ : Measure X).support, ∃ y ∈ (μ : Measure X).support, R (x, y) := by
  constructor
  · rintro ⟨n, h₁, h₂, hR⟩
    exact ⟨_, originalCountingAtomPoint_mem_support_of_present base μ hμ _ h₁,
      _, originalCountingAtomPoint_mem_support_of_present base μ hμ _ h₂, hR⟩
  · rintro ⟨x, hx, y, hy, hR⟩
    obtain ⟨i, hi⟩ := exists_originalCountingAtom base μ hμ hx
    obtain ⟨j, hj⟩ := exists_originalCountingAtom base μ hμ hy
    refine ⟨Nat.pair i j, ?_⟩
    simp only [originalCountingPairWitness, Nat.unpair_pair, hi, hj, Option.isSome_some,
      originalCountingPair, originalCountingAtomPoint_eq_of_some base μ hi,
      originalCountingAtomPoint_eq_of_some base μ hj, true_and]
    exact hR

/-- A fixed code index gives a Borel actual edge-pair certificate. -/
theorem measurableSet_originalCountingPairWitness
    {Ω : Type*} [MeasurableSpace Ω] (base : X)
    (μ : Ω → LocalFiniteMeasure X) (hμ : Measurable μ)
    (R : Ω → X × X → Prop)
    (hR : MeasurableSet {p : Ω × (X × X) | R p.1 p.2}) (n : ℕ) :
    MeasurableSet {ω | originalCountingPairWitness base (μ ω) (R ω) n} := by
  apply MeasurableSet.inter
    (measurableSet_eq_fun ((MeasureTheory.Option.measurable_isSome.comp
      (measurable_originalCountingAtom base _)).comp hμ) measurable_const)
  apply MeasurableSet.inter
    (measurableSet_eq_fun ((MeasureTheory.Option.measurable_isSome.comp
      (measurable_originalCountingAtom base _)).comp hμ) measurable_const)
  exact hR.preimage (measurable_id.prodMk
    ((measurable_originalCountingPair base n).comp hμ))

/-- Existence of an original coded exchange pair is a Borel event. On the actual
integer carrier it is exactly existence of an occupied support pair. -/
theorem measurableSet_exists_originalCountingPairWitness
    {Ω : Type*} [MeasurableSpace Ω] (base : X)
    (μ : Ω → LocalFiniteMeasure X) (hμ : Measurable μ)
    (R : Ω → X × X → Prop)
    (hR : MeasurableSet {p : Ω × (X × X) | R p.1 p.2}) :
    MeasurableSet {ω | ∃ n, originalCountingPairWitness base (μ ω) (R ω) n} := by
  convert MeasurableSet.iUnion
    (fun n ↦ measurableSet_originalCountingPairWitness base μ hμ R hR n) using 1
  ext ω
  simp only [mem_iUnion, mem_ofPred_eq]

/-- Measurable selection from a Borel local edge-pair certificate on an actual
integer input. The default outside the witness event is harmless and explicit. -/
theorem exists_measurable_originalCountingPair_selection
    {Ω : Type*} [MeasurableSpace Ω] (base : X)
    (μ : Ω → LocalFiniteMeasure X) (hμ : Measurable μ)
    (R : Ω → X × X → Prop)
    (hR : MeasurableSet {p : Ω × (X × X) | R p.1 p.2}) :
    ∃ choose : Ω → X × X, Measurable choose ∧
      ∀ ω, IsLegalCountingMeasure base (μ ω) →
        (∃ x ∈ (μ ω : Measure X).support,
          ∃ y ∈ (μ ω : Measure X).support, R ω (x, y)) →
        (choose ω).1 ∈ (μ ω : Measure X).support ∧
          (choose ω).2 ∈ (μ ω : Measure X).support ∧ R ω (choose ω) := by
  classical
  let A : Ω → ℕ → Prop := fun ω n ↦ originalCountingPairWitness base (μ ω) (R ω) n
  have hA (n : ℕ) : MeasurableSet {ω | A ω n} :=
    measurableSet_originalCountingPairWitness base μ hμ R hR n
  have hnone : MeasurableSet {ω | ¬ ∃ n, A ω n} := by
    convert (MeasurableSet.iUnion hA).compl using 1
    ext ω
    simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
  let B : Ω → ℕ → Prop := fun ω n ↦ A ω n ∨ (¬ ∃ m, A ω m) ∧ n = 0
  have hB (n : ℕ) : MeasurableSet {ω | B ω n} := by
    apply (hA n).union
    by_cases hn : n = 0
    · convert hnone using 1
      ext ω
      change ((¬ ∃ m, A ω m) ∧ n = 0) ↔ ¬ ∃ m, A ω m
      simp [hn]
    · convert (MeasurableSet.empty : MeasurableSet (∅ : Set Ω)) using 1
      ext ω
      change ((¬ ∃ m, A ω m) ∧ n = 0) ↔ False
      simp [hn]
  have hex (ω : Ω) : ∃ n, B ω n := by
    by_cases h : ∃ n, A ω n
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr ⟨h, rfl⟩⟩
  let choose : Ω → X × X := fun ω ↦ originalCountingPair base (μ ω) (Nat.find (hex ω))
  refine ⟨choose, ?_, ?_⟩
  · exact Measurable.find (fun n ↦ (measurable_originalCountingPair base n).comp hμ) hB hex
  · intro ω hcount hgood
    have hgood' : ∃ n, A ω n :=
      (exists_originalCountingPairWitness_iff base (μ ω) hcount (R ω)).mpr hgood
    have hselected : A ω (Nat.find (hex ω)) := by
      rcases Nat.find_spec (hex ω) with ha | ⟨hnone, _⟩
      · exact ha
      · exact (hnone hgood').elim
    exact ⟨originalCountingAtomPoint_mem_support_of_present base (μ ω) hcount _ hselected.1,
      originalCountingAtomPoint_mem_support_of_present base (μ ω) hcount _ hselected.2.1,
      hselected.2.2⟩

end OTSelector.Reconstruction
