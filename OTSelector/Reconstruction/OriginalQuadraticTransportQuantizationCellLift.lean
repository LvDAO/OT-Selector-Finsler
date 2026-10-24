import OTSelector.Transport.EmpiricalSelector.CompactSupport
import Mathlib.Probability.ConditionalProbability

/-! Exact lifting of finite grid plans by products of conditional cell laws. -/
open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

variable {X Y I J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype I] [Fintype J] [MeasurableSpace I] [MeasurableSpace J]
  [DiscreteMeasurableSpace I] [DiscreteMeasurableSpace J]

/-- The genuine original-space plan obtained by distributing each grid mass
according to the two original conditional cell laws. -/
def finiteCellPlanLift (μ : Measure X) (ν : Measure Y) (T : X → I) (S : Y → J)
    (P : I → J → ℝ≥0∞) : Measure (X × Y) :=
  ∑ ij : I × J, P ij.1 ij.2 • (μ[|T ← ij.1]).prod (ν[|S ← ij.2])

private lemma finiteCell_cond_map (μ : Measure X) [IsFiniteMeasure μ]
    {T : X → I} (hT : Measurable T) (i : I) (hi : μ (T ⁻¹' {i}) ≠ 0) :
    (μ[|T ← i]).map T = Measure.dirac i := by
  let := cond_isProbabilityMeasure hi
  have heq : T =ᵐ[μ[|T ← i]] fun _ ↦ i := by
    exact ae_cond_of_forall_mem (hT (measurableSet_singleton i)) (by simp)
  rw [Measure.map_congr heq, Measure.map_const, measure_univ, one_smul]

set_option linter.unusedSectionVars false in
private lemma finiteCell_entry_zero_of_column {P : I → J → ℝ≥0∞}
    {ν : Measure Y} {S : Y → J}
    (hcol : ∀ j, ∑ i, P i j = ν (S ⁻¹' {j})) {j : J}
    (hj : ν (S ⁻¹' {j}) = 0) (i : I) : P i j = 0 := by
  have hle : P i j ≤ ∑ k, P k j := Finset.single_le_sum (f := fun k ↦ P k j) (fun k _ ↦ bot_le) (Finset.mem_univ i)
  rw [hcol j, hj] at hle
  exact le_antisymm hle bot_le

set_option linter.unusedSectionVars false in
private lemma finiteCell_entry_zero_of_row {P : I → J → ℝ≥0∞}
    {μ : Measure X} {T : X → I}
    (hrow : ∀ i, ∑ j, P i j = μ (T ⁻¹' {i})) {i : I}
    (hi : μ (T ⁻¹' {i}) = 0) (j : J) : P i j = 0 := by
  have hle : P i j ≤ ∑ k, P i k := Finset.single_le_sum (f := fun k ↦ P i k) (fun k _ ↦ bot_le) (Finset.mem_univ j)
  rw [hrow i, hi] at hle
  exact le_antisymm hle bot_le

/-- The lift restores both original marginals exactly, including zero-mass cells. -/
theorem finiteCellPlanLift_isCoupling (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {T : X → I} {S : Y → J}
    (hT : Measurable T) (hS : Measurable S) (P : I → J → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, P i j = μ (T ⁻¹' {i}))
    (hcol : ∀ j, ∑ i, P i j = ν (S ⁻¹' {j})) :
    Vlasov.IsCoupling (finiteCellPlanLift μ ν T S P) μ ν := by
  constructor
  · rw [finiteCellPlanLift, Measure.map_finset_sum' (f := Prod.fst) measurable_fst.aemeasurable]
    simp only [Measure.map_smul, Fintype.sum_prod_type]
    have hentry : ∀ i j, P i j • ((μ[|T ← i]).prod (ν[|S ← j])).map Prod.fst =
        P i j • μ[|T ← i] := by
      intro i j
      by_cases hj : ν (S ⁻¹' {j}) = 0
      · simp [finiteCell_entry_zero_of_column hcol hj i]
      · let := cond_isProbabilityMeasure hj
        simp
    simp_rw [hentry, ← Finset.sum_smul, hrow]
    exact sum_meas_smul_cond_fiber hT μ
  · rw [finiteCellPlanLift, Measure.map_finset_sum' (f := Prod.snd) measurable_snd.aemeasurable]
    simp only [Measure.map_smul, Fintype.sum_prod_type]
    have hentry : ∀ i j, P i j • ((μ[|T ← i]).prod (ν[|S ← j])).map Prod.snd =
        P i j • ν[|S ← j] := by
      intro i j
      by_cases hi : μ (T ⁻¹' {i}) = 0
      · simp [finiteCell_entry_zero_of_row hrow hi j]
      · let := cond_isProbabilityMeasure hi
        simp
    simp_rw [hentry]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcol]
    exact sum_meas_smul_cond_fiber hS ν

/-- Reading the lifted original plan through the same cells recovers every entry
of the prescribed finite grid plan. -/
theorem finiteCellPlanLift_map (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {T : X → I} {S : Y → J}
    (hT : Measurable T) (hS : Measurable S) (P : I → J → ℝ≥0∞)
    (hrow : ∀ i, ∑ j, P i j = μ (T ⁻¹' {i}))
    (hcol : ∀ j, ∑ i, P i j = ν (S ⁻¹' {j})) :
    (finiteCellPlanLift μ ν T S P).map (Prod.map T S) =
      ∑ ij : I × J, P ij.1 ij.2 • Measure.dirac ij := by
  rw [finiteCellPlanLift, Measure.map_finset_sum' (hT.prodMap hS).aemeasurable]
  simp only [Measure.map_smul]
  apply Finset.sum_congr rfl
  intro ij _
  by_cases hi : μ (T ⁻¹' {ij.1}) = 0
  · simp [finiteCell_entry_zero_of_row hrow hi ij.2]
  by_cases hj : ν (S ⁻¹' {ij.2}) = 0
  · simp [finiteCell_entry_zero_of_column hcol hj ij.1]
  rw [← Measure.map_prod_map _ _ hT hS, finiteCell_cond_map μ hT ij.1 hi,
    finiteCell_cond_map ν hS ij.2 hj]
  rw [Measure.dirac_prod_dirac]


/-- Every genuine coupling of the two finite cell laws has a genuine original
coupling that maps back to that very same finite coupling. -/
theorem exists_finiteCell_coupling_lift (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {T : X → I} {S : Y → J}
    (hT : Measurable T) (hS : Measurable S) (κ : Measure (I × J))
    (hκ : Vlasov.IsCoupling κ (μ.map T) (ν.map S)) :
    ∃ π : Measure (X × Y), Vlasov.IsCoupling π μ ν ∧ π.map (Prod.map T S) = κ := by
  let P : I → J → ℝ≥0∞ := fun i j ↦ κ {(i,j)}
  have hrow : ∀ i, ∑ j, P i j = μ (T ⁻¹' {i}) := by
    intro i
    calc
      _ = κ (Prod.fst ⁻¹' {i}) := by
        simpa only [P] using (measure_preimage_fst_singleton_eq_sum κ i).symm
      _ = (κ.map Prod.fst) {i} := (Measure.map_apply measurable_fst (measurableSet_singleton i)).symm
      _ = μ (T ⁻¹' {i}) := by rw [hκ.1, Measure.map_apply hT (measurableSet_singleton i)]
  have hcol : ∀ j, ∑ i, P i j = ν (S ⁻¹' {j}) := by
    intro j
    calc
      _ = κ (Prod.snd ⁻¹' {j}) := by
        simpa only [P] using (measure_preimage_snd_singleton_eq_sum κ j).symm
      _ = (κ.map Prod.snd) {j} := (Measure.map_apply measurable_snd (measurableSet_singleton j)).symm
      _ = ν (S ⁻¹' {j}) := by rw [hκ.2, Measure.map_apply hS (measurableSet_singleton j)]
  refine ⟨finiteCellPlanLift μ ν T S P, finiteCellPlanLift_isCoupling μ ν hT hS P hrow hcol, ?_⟩
  rw [finiteCellPlanLift_map μ ν hT hS P hrow hcol]
  simpa only [Measure.sum_fintype, P] using Measure.sum_smul_dirac κ


/-- Any genuine coupling of finite-range grid pushforwards lifts exactly to the
original finite measures. The quantizers may identify arbitrarily many points. -/
theorem exists_finiteRange_coupling_lift
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : X → A} {S : Y → B} (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite)
    (κ : Measure (A × B)) (hκ : Vlasov.IsCoupling κ (μ.map T) (ν.map S)) :
    ∃ π : Measure (X × Y), Vlasov.IsCoupling π μ ν ∧ π.map (Prod.map T S) = κ := by
  let T' : X → Set.range T := fun x ↦ ⟨T x, Set.mem_range_self x⟩
  let S' : Y → Set.range S := fun y ↦ ⟨S y, Set.mem_range_self y⟩
  let := hTfin.fintype
  let := hSfin.fintype
  have hT' : Measurable T' := hT.subtype_mk
  have hS' : Measurable S' := hS.subtype_mk
  have hμ : (μ.map T').map Subtype.val = μ.map T := by
    rw [Measure.map_map measurable_subtype_coe hT']
    rfl
  have hν : (ν.map S').map Subtype.val = ν.map S := by
    rw [Measure.map_map measurable_subtype_coe hS']
    rfl
  have hκ' : Vlasov.IsCoupling κ ((μ.map T').map Subtype.val)
      ((ν.map S').map Subtype.val) := by simpa only [hμ, hν] using hκ
  obtain ⟨κ', hκ', _⟩ := existsUnique_coupling_lift
    (MeasurableEmbedding.subtype_coe hTfin.measurableSet)
    (MeasurableEmbedding.subtype_coe hSfin.measurableSet) hκ'
  obtain ⟨π, hπ, hmap⟩ := exists_finiteCell_coupling_lift μ ν hT' hS' κ' hκ'.1
  refine ⟨π, hπ, ?_⟩
  calc
    π.map (Prod.map T S) =
        (π.map (Prod.map T' S')).map (Prod.map Subtype.val Subtype.val) := by
      rw [Measure.map_map (measurable_subtype_coe.prodMap measurable_subtype_coe)
        (hT'.prodMap hS')]
      rfl
    _ = κ := by rw [hmap]; exact hκ'.2

end OTSelector.Reconstruction
