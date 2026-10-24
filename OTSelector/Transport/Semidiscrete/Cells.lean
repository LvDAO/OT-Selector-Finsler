import OTSelector.Finite.AssignmentCavity
import OTSelector.Transport.Semidiscrete.Calibration
import OTSelector.Transport.Semidiscrete.CavityCells
import OTSelector.Transport.Semidiscrete.MeanPlan
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteCells.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteCells`; the selected original proof blocks follow. -/
section

/-!
Conditions: Measurable finite cavity scores with pairwise null ties; comparison allocations have exactly the same cavity-cell masses and the actual costs are integrable.

Objects: The cell indicator is a strictly calibrated semidiscrete optimum, and its allocation/readouts agree for equal mass vectors.

Proof detail: Use no-tie unique minima for strict calibration, integrate cell indicators for masses and compare both allocations through the common-mass optimum/equality criterion.

Sources: Gabriel Peyré, Section 5.2, equations (5.6)–(5.8), pp. 94–96 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=98); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31).
Relation: Derived finite-cell uniqueness and mass-fiber constancy. No regularity of a map selecting prices as a function of mass is assumed.
-/

/-!
# The unique semidiscrete optimum supplied by actual cavity cells

The whole collection of measurable cavity cells gives the allocation. Null score ties
make it a probability allocation, and its own vacancy prices prove optimality and
uniqueness among all feasible fractional allocations with the same label masses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]

/-- Actual cavity cell indicators as source-to-target allocation weights. -/
def cavityAllocation (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ) (i : Fin (m + 1))
    (w : W) (s : S) (j : Fin (m + 1)) : ℝ :=
  (cavityCell retained row i j).indicator (fun _ ↦ 1) (w, s)

omit [MeasurableSpace S] [MeasurableSpace W] in
/-- Unique cell membership gives its actual strict price calibration and unit allocation. -/
theorem cavityAllocation_strictly_calibrated_of_unique
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ) (i : Fin (m + 1)) (w : W) (s : S)
    (huniq : ∃! j, (w, s) ∈ cavityCell retained row i j) :
    ∃ k, (∀ j, j ≠ k →
      row (w, s) k + assignmentCavityValue (retained w) i k <
        row (w, s) j + assignmentCavityValue (retained w) i j) ∧
      ∀ j, cavityAllocation retained row i w s j = if j = k then 1 else 0 := by
  classical
  obtain ⟨k, hk, hu⟩ := huniq
  refine ⟨k, ?_, ?_⟩
  · intro j hj
    apply lt_of_le_of_ne (hk j)
    intro he
    have hjcell : (w, s) ∈ cavityCell retained row i j := by
      intro l
      exact he ▸ hk l
    exact hj (hu j hjcell)
  · intro j
    by_cases hj : j = k
    · subst j
      simp [cavityAllocation, hk]
    · have hjnot : (w, s) ∉ cavityCell retained row i j := fun h ↦ hj (hu j h)
      simp [cavityAllocation, hj, hjnot]

omit [MeasurableSpace W] in
/-- Null score ties provide strict calibration almost everywhere for every retained input. -/
theorem ae_cavityAllocation_strictly_calibrated
    (μ : Measure S) (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ) (i : Fin (m + 1)) (w : W)
    (hno : ∀ j l, j ≠ l →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) l} = 0) :
    ∀ᵐ s ∂μ, ∃ k, (∀ j, j ≠ k →
      row (w, s) k + assignmentCavityValue (retained w) i k <
        row (w, s) j + assignmentCavityValue (retained w) i j) ∧
      ∀ j, cavityAllocation retained row i w s j = if j = k then 1 else 0 :=
  (ae_existsUnique_mem_cavityCell μ retained row i w hno).mono fun s hs ↦
    cavityAllocation_strictly_calibrated_of_unique retained row i w s hs

/-- Actual cell indicators have exactly their cell masses as label marginals. -/
theorem isSemidiscreteAllocation_cavityAllocation
    (μ : Measure S) [IsFiniteMeasure μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (m + 1)) (w : W)
    (hno : ∀ j l, j ≠ l →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) l} = 0) :
    IsSemidiscreteAllocation μ (fun j ↦ (cavityCellMass μ retained row i j w).toReal)
      (cavityAllocation retained row i w) := by
  classical
  have hm j : MeasurableSet {s | (w, s) ∈ cavityCell retained row i j} :=
    (measurableSet_cavityCell retained row hret hrow i j).preimage measurable_prodMk_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    exact (integrable_const (1 : ℝ)).indicator (hm j)
  · exact Eventually.of_forall fun s j ↦ by
      by_cases hs : (w, s) ∈ cavityCell retained row i j <;> simp [cavityAllocation, hs]
  · filter_upwards [ae_cavityAllocation_strictly_calibrated μ retained row i w hno] with s hs
    obtain ⟨k, _, hk⟩ := hs
    simp [hk]
  · intro j
    exact integral_indicator_one (hm j)

/-- The actual cavity allocation is optimal for its own masses, and equality of the
cost forces every feasible competitor to be that allocation almost everywhere. -/
theorem cavityAllocation_unique_optimal
    (μ : Measure S) [IsFiniteMeasure μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (m + 1)) (w : W)
    (hno : ∀ j l, j ≠ l →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) l} = 0)
    (hc : ∀ j, Integrable (fun s ↦ row (w, s) j) μ)
    (b : S → Fin (m + 1) → ℝ)
    (hb : IsSemidiscreteAllocation μ
      (fun j ↦ (cavityCellMass μ retained row i j w).toReal) b) :
    semidiscreteAllocationCost μ (fun s ↦ row (w, s)) (cavityAllocation retained row i w) ≤
      semidiscreteAllocationCost μ (fun s ↦ row (w, s)) b ∧
    (semidiscreteAllocationCost μ (fun s ↦ row (w, s)) (cavityAllocation retained row i w) =
      semidiscreteAllocationCost μ (fun s ↦ row (w, s)) b →
        cavityAllocation retained row i w =ᵐ[μ] b) := by
  have ha := isSemidiscreteAllocation_cavityAllocation μ retained row hret hrow i w hno
  have hcal := ae_cavityAllocation_strictly_calibrated μ retained row i w hno
  refine ⟨semidiscreteAllocationCost_le_of_calibrated μ _ _ _ b ha hb hc
    (assignmentCavityValue (retained w) i) ?_, ?_⟩
  · filter_upwards [hcal] with s hs
    obtain ⟨k, hk, ha⟩ := hs
    refine ⟨k, fun j ↦ ?_, ha⟩
    by_cases hj : j = k
    · simp [hj]
    · exact (hk j hj).le
  · exact semidiscreteAllocation_eq_of_cost_eq_of_strictly_calibrated μ _ _ _ b ha hb hc
      (assignmentCavityValue (retained w) i) hcal

/-- The earlier paired mean readout is exactly the cost of the actual cell allocation,
with the endpoint test in place of cost. -/
theorem cavityMeanReadout_eq_allocationCost
    (μ : Measure S) [IsFiniteMeasure μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (m + 1)) (w : W)
    (g : W × S → Fin (m + 1) → ℝ)
    (hg : ∀ j, Integrable (fun s ↦ g (w, s) j) μ) :
    cavityMeanReadout μ retained row i g w =
      semidiscreteAllocationCost μ (fun s ↦ g (w, s)) (cavityAllocation retained row i w) := by
  classical
  have hm j : MeasurableSet {s | (w, s) ∈ cavityCell retained row i j} :=
    (measurableSet_cavityCell retained row hret hrow i j).preimage measurable_prodMk_left
  have hind j : (fun s ↦ cavityAllocation retained row i w s j * g (w, s) j) =
      {s | (w, s) ∈ cavityCell retained row i j}.indicator (fun s ↦ g (w, s) j) := by
    funext s
    by_cases hs : (w, s) ∈ cavityCell retained row i j <;> simp [cavityAllocation, hs]
  have hi j : Integrable (fun s ↦ cavityAllocation retained row i w s j * g (w, s) j) μ := by
    rw [hind]
    exact (hg j).indicator (hm j)
  unfold cavityMeanReadout semidiscreteAllocationCost
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hind, integral_indicator (hm j)]

/-- For fixed source costs, two cavity environments with the same masses have the
same allocation almost everywhere. The conclusion follows from actual optimality. -/
theorem cavityAllocation_eq_of_same_masses
    (μ : Measure S) [IsFiniteMeasure μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Measurable (fun s ↦ c s j))
    (hci : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c s j - c s l)))
    (i : Fin (m + 1)) (w v : W)
    (hmass : ∀ j, cavityCellMass μ retained (fun z ↦ c z.2) i j w =
      cavityCellMass μ retained (fun z ↦ c z.2) i j v) :
    cavityAllocation retained (fun z ↦ c z.2) i w =ᵐ[μ]
      cavityAllocation retained (fun z ↦ c z.2) i v := by
  let row : W × S → Fin (m + 1) → ℝ := fun z ↦ c z.2
  have hrow j : Measurable (fun z ↦ row z j) := (hc j).comp measurable_snd
  have hno (u : W) (j l : Fin (m + 1)) (hjl : j ≠ l) :
      μ {s | cavityScore retained row i (u, s) j = cavityScore retained row i (u, s) l} = 0 := by
    have := hatom j l hjl
    exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow i j l u
  have hw := isSemidiscreteAllocation_cavityAllocation μ retained row hret hrow i w (hno w)
  have hv := isSemidiscreteAllocation_cavityAllocation μ retained row hret hrow i v (hno v)
  have hp : (fun j ↦ (cavityCellMass μ retained row i j w).toReal) =
      (fun j ↦ (cavityCellMass μ retained row i j v).toReal) :=
    funext fun j ↦ congrArg ENNReal.toReal (hmass j)
  have hoptw := cavityAllocation_unique_optimal μ retained row hret hrow i w (hno w) hci
    (cavityAllocation retained row i v) (hp.symm ▸ hv)
  have hoptv := cavityAllocation_unique_optimal μ retained row hret hrow i v (hno v) hci
    (cavityAllocation retained row i w) (hp ▸ hw)
  exact hoptw.2 (le_antisymm hoptw.1 hoptv.1)

/-- Every paired-test readout depends only on the actual cavity masses. -/
theorem cavityMeanReadout_eq_of_same_masses
    (μ : Measure S) [IsFiniteMeasure μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Measurable (fun s ↦ c s j))
    (hci : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c s j - c s l)))
    (i : Fin (m + 1)) (w v : W)
    (hmass : ∀ j, cavityCellMass μ retained (fun z ↦ c z.2) i j w =
      cavityCellMass μ retained (fun z ↦ c z.2) i j v)
    (g : S → Fin (m + 1) → ℝ) (hg : ∀ j, Integrable (fun s ↦ g s j) μ) :
    cavityMeanReadout μ retained (fun z ↦ c z.2) i (fun z ↦ g z.2) w =
      cavityMeanReadout μ retained (fun z ↦ c z.2) i (fun z ↦ g z.2) v := by
  have hrow j : Measurable (fun z : W × S ↦ c z.2 j) := (hc j).comp measurable_snd
  rw [cavityMeanReadout_eq_allocationCost μ retained _ hret hrow i w _ hg,
    cavityMeanReadout_eq_allocationCost μ retained _ hret hrow i v _ hg]
  apply integral_congr_ae
  filter_upwards [cavityAllocation_eq_of_same_masses μ retained hret c hc hci hatom i w v hmass]
    with s hs
  simp only [hs]

end OTSelector.Probability

end
end
