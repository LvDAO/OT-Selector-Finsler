import OTSelector.Reconstruction.OriginalFiniteOrderedStrictBlocksMass

/-! The same continuous conditional coupling restricts to the actual zero-cut blocks. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 700000

/-- Surplus of the actual original source and target class masses. -/
def FiniteOrderedMonochromeClasses.surplus
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) : ℕ → ℝ :=
  finiteClassSurplus (fun i ↦ μ.real (C.cell i)) (fun i ↦ ν.real (C.cell i))

/-- Actual blocks use every tight prefix cut of the original class masses. -/
abbrev FiniteOrderedMonochromeClasses.StrictBlock
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) :=
  FiniteSurplusStrictBlock C.surplus C.count

/-- The actual scalar set of a block is the union of its unchanged raw classes. -/
def FiniteOrderedMonochromeClasses.blockCell
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (b : C.StrictBlock) : Set ℝ := ⋃ i ∈ b.classes, C.cell i

/-- Every actual block set is measurable. -/
theorem FiniteOrderedMonochromeClasses.measurable_blockCell
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (b : C.StrictBlock) : MeasurableSet (C.blockCell b) :=
  MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦ C.measurable_cell i

/-- Within a disjoint original class, block membership is exactly index
membership; no closure or reassignment of physical mass is performed. -/
theorem FiniteOrderedMonochromeClasses.mem_blockCell_iff_of_mem_cell
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (b : C.StrictBlock) {i : Fin C.count} {x : ℝ} (hx : x ∈ C.cell i) :
    x ∈ C.blockCell b ↔ b.Contains i := by
  classical
  constructor
  · intro hb
    obtain ⟨j, hj⟩ := mem_iUnion.mp hb
    obtain ⟨hj, hxj⟩ := mem_iUnion.mp hj
    have hij : i = j := by
      by_contra h
      exact disjoint_left.mp (C.disjoint h) hx hxj
    subst j
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hx⟩⟩

/-- The original genuine coupling supplies the weak surplus and both endpoint
zero cuts used by the canonical finite block construction. -/
theorem FiniteOrderedMonochromeClasses.surplus_facts_of_coupling
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 ≤ p.2) :
    C.surplus 0 = 0 ∧ C.surplus C.count = 0 ∧ ∀ k ≤ C.count, 0 ≤ C.surplus k := by
  obtain ⟨hrow, hcol⟩ := C.actualClassFlow_marginals γ hγ
  let P := actualClockClassFlow γ C.cell C.cell
  let a := fun i ↦ μ.real (C.cell i)
  let c := fun i ↦ ν.real (C.cell i)
  have hzero := C.actualClassFlow_zero hδ γ hγ hforward
  have hend := finiteClassFlow_surplus_endpoints P a c hrow hcol
  refine ⟨hend.1, hend.2, ?_⟩
  intro k hk
  exact finiteClassFlow_surplus_nonneg P a c (actualClockClassFlow_nonneg γ C.cell C.cell)
    hrow hcol hzero k hk

/-- The actual original coupling has equal source and target membership in
any constructed block, since all of its forbidden crossing rectangles are null. -/
theorem FiniteOrderedMonochromeClasses.ae_same_blockCell
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 ≤ p.2) (b : C.StrictBlock) :
    ∀ᵐ p ∂γ, p.1 ∈ C.blockCell b ↔ p.2 ∈ C.blockCell b := by
  classical
  obtain ⟨hrow, hcol⟩ := C.actualClassFlow_marginals γ hγ
  let P := actualClockClassFlow γ C.cell C.cell
  let a := fun i ↦ μ.real (C.cell i)
  let c := fun i ↦ ν.real (C.cell i)
  have hP := actualClockClassFlow_nonneg γ C.cell C.cell
  have hzero := C.actualClassFlow_zero hδ γ hγ hforward
  have hpairs : ∀ i j : Fin C.count, ∀ᵐ p ∂γ,
      p ∈ C.cell i ×ˢ C.cell j → (b.Contains i ↔ b.Contains j) := by
    intro i j
    by_cases hs : b.Contains i ↔ b.Contains j
    · exact ae_of_all _ fun _ _ ↦ hs
    have hzij : P i j = 0 := by
      by_cases hi : b.Contains i
      · have hj : ¬ b.Contains j := by tauto
        exact finiteClassFlow_zero_leaving_block P a c hP hrow hcol hzero b i j hi hj
      · have hj : b.Contains j := by tauto
        exact finiteClassFlow_zero_entering_block P a c hP hrow hcol hzero b i j hi hj
    have hnull : γ (C.cell i ×ˢ C.cell j) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top γ _)).mp hzij
    exact ae_iff.mpr (measure_mono_null (fun _ hp ↦ (not_imp.mp hp).1) hnull)
  have hall : ∀ᵐ p ∂γ, ∀ i j : Fin C.count,
      p ∈ C.cell i ×ˢ C.cell j → (b.Contains i ↔ b.Contains j) :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hpairs i)
  have hs : ∀ᵐ p ∂γ, p.1 ∈ ⋃ i, C.cell i :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hγ.1]; exact C.ae_source_cover)
  have ht : ∀ᵐ p ∂γ, p.2 ∈ ⋃ i, C.cell i :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hγ.2]; exact C.ae_target_cover)
  filter_upwards [hall, hs, ht] with p hp hs ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp hs
  obtain ⟨j, hj⟩ := mem_iUnion.mp ht
  rw [C.mem_blockCell_iff_of_mem_cell b hi, C.mem_blockCell_iff_of_mem_cell b hj]
  exact hp i j ⟨hi, hj⟩

/-- Restricting the same original coupling by an actual block retains both
original restricted laws exactly; no new coupling is selected. -/
theorem FiniteOrderedMonochromeClasses.block_restrict_coupling
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 ≤ p.2) (b : C.StrictBlock) :
    Vlasov.IsCoupling (γ.restrict (Prod.fst ⁻¹' C.blockCell b))
      (μ.restrict (C.blockCell b)) (ν.restrict (C.blockCell b)) := by
  have hm := C.measurable_blockCell b
  have heq : Prod.fst ⁻¹' C.blockCell b =ᵐ[γ] Prod.snd ⁻¹' C.blockCell b :=
    (C.ae_same_blockCell hδ γ hγ hforward b).mono fun _ hp ↦ propext hp
  constructor
  · exact (Measure.restrict_map measurable_fst hm).symm.trans
      (congrArg (fun θ : Measure ℝ ↦ θ.restrict (C.blockCell b)) hγ.1)
  · calc
      _ = (γ.restrict (Prod.snd ⁻¹' C.blockCell b)).map Prod.snd :=
        congrArg (fun θ : Measure (ℝ × ℝ) ↦ θ.map Prod.snd) (Measure.restrict_congr_set heq)
      _ = (γ.map Prod.snd).restrict (C.blockCell b) := (Measure.restrict_map measurable_snd hm).symm
      _ = _ := congrArg (fun θ : Measure ℝ ↦ θ.restrict (C.blockCell b)) hγ.2

/-- Each original class law is literally unchanged inside its own constructed block. -/
theorem FiniteOrderedMonochromeClasses.block_original_class_restrict
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (b : C.StrictBlock) (i : Fin C.count) (hi : b.Contains i) (θ : Measure ℝ) :
    (θ.restrict (C.blockCell b)).restrict (C.cell i) = θ.restrict (C.cell i) := by
  apply Measure.restrict_restrict_of_subset
  intro x hx
  exact (C.mem_blockCell_iff_of_mem_cell b hx).mpr hi

/-- Block mass is the sum of the actual unchanged original class masses. -/
theorem FiniteOrderedMonochromeClasses.block_mass_eq_class_sum
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (b : C.StrictBlock) (θ : Measure ℝ) [IsFiniteMeasure θ] :
    θ.real (C.blockCell b) = ∑ i ∈ b.classes, θ.real (C.cell i) := by
  apply measureReal_biUnion_finset
  · intro i _ j _ hij
    exact C.disjoint hij
  · intro i _
    exact C.measurable_cell i
  · intro i _
    exact measure_ne_top θ _

/-- Every actual block has equal positive original source and target masses. -/
theorem FiniteOrderedMonochromeClasses.block_mass_balanced_pos
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {δ : ℝ}
    (C : FiniteOrderedMonochromeClasses μ ν δ) (b : C.StrictBlock) :
    0 < μ.real (C.blockCell b) ∧ μ.real (C.blockCell b) = ν.real (C.blockCell b) := by
  rw [C.block_mass_eq_class_sum b μ, C.block_mass_eq_class_sum b ν]
  exact ⟨b.mass_pos (fun i ↦ μ.real (C.cell i)) (fun i ↦ ν.real (C.cell i))
    (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg) C.real_class_mass_pos,
    b.mass_balance (fun i ↦ μ.real (C.cell i)) (fun i ↦ ν.real (C.cell i))⟩

end OTSelector.Reconstruction
