import OTSelector.Reconstruction.OriginalFiniteOrderedStrictBlocksLaws

/-! Complete actual finite strict-block decomposition, including normalized margins. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 700000

/-- Distinct constructed blocks contain disjoint original scalar sets. -/
theorem FiniteOrderedMonochromeClasses.block_cells_disjoint
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (h₀ : C.surplus 0 = 0) (hN : C.surplus C.count = 0) :
    Pairwise (fun b c : C.StrictBlock ↦ Disjoint (C.blockCell b) (C.blockCell c)) := by
  classical
  intro b c hbc
  apply disjoint_left.mpr
  intro x hb hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hb
  obtain ⟨hi, hxi⟩ := mem_iUnion.mp hi
  obtain ⟨j, hj⟩ := mem_iUnion.mp hc
  obtain ⟨hj, hxj⟩ := mem_iUnion.mp hj
  have hij : i = j := by
    by_contra h
    exact disjoint_left.mp (C.disjoint h) hxi hxj
  subst j
  have hbi : b.Contains i := (Finset.mem_filter.mp hi).2
  have hci : c.Contains i := (Finset.mem_filter.mp hj).2
  exact hbc ((exists_unique_finiteSurplusStrictBlock C.surplus C.count h₀ hN i).unique hbi hci)

/-- Original raw class coverage passes to the canonical constructed blocks. -/
theorem FiniteOrderedMonochromeClasses.ae_block_cover
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (h₀ : C.surplus 0 = 0) (hN : C.surplus C.count = 0) (θ : Measure ℝ)
    (hθ : ∀ᵐ x ∂θ, x ∈ ⋃ i, C.cell i) : ∀ᵐ x ∂θ, x ∈ ⋃ b : C.StrictBlock, C.blockCell b := by
  classical
  filter_upwards [hθ] with x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨b, hb, _⟩ := exists_unique_finiteSurplusStrictBlock C.surplus C.count h₀ hN i
  exact mem_iUnion.mpr ⟨b, (C.mem_blockCell_iff_of_mem_cell b hi).mpr hb⟩

/-- The constructed block laws recover the original law exactly. -/
theorem FiniteOrderedMonochromeClasses.sum_block_restrict
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (h₀ : C.surplus 0 = 0) (hN : C.surplus C.count = 0) (θ : Measure ℝ)
    (hθ : ∀ᵐ x ∂θ, x ∈ ⋃ i, C.cell i) :
    (∑ b : C.StrictBlock, θ.restrict (C.blockCell b)) = θ := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion (C.block_cells_disjoint h₀ hN)
    C.measurable_blockCell]
  exact Measure.restrict_eq_self_of_ae_mem (C.ae_block_cover h₀ hN θ hθ)

/-- The actual original coupling, without replacement, is the exact finite sum
of its restrictions to the constructed source blocks. -/
theorem FiniteOrderedMonochromeClasses.sum_block_coupling
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (h₀ : C.surplus 0 = 0) (hN : C.surplus C.count = 0)
    (γ : Measure (ℝ × ℝ)) (hγ : Vlasov.IsCoupling γ μ ν) :
    (∑ b : C.StrictBlock, γ.restrict ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell b)) = γ := by
  have hd : Pairwise (fun b c : C.StrictBlock ↦
      Disjoint ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell b) ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell c)) := by
    intro b c hbc
    exact (C.block_cells_disjoint h₀ hN hbc).preimage Prod.fst
  have hm : ∀ b : C.StrictBlock, MeasurableSet ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell b) :=
    fun b ↦ measurable_fst (C.measurable_blockCell b)
  have hs : ∀ᵐ p ∂γ, p.1 ∈ ⋃ b : C.StrictBlock, C.blockCell b :=
    ae_of_ae_map measurable_fst.aemeasurable (by
      rw [hγ.1]
      exact C.ae_block_cover h₀ hN μ C.ae_source_cover)
  have hc : ∀ᵐ p ∂γ, p ∈ ⋃ b : C.StrictBlock, (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell b := by
    exact hs.mono fun p hp ↦ by
      obtain ⟨b, hb⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨b, hb⟩
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd hm]
  exact Measure.restrict_eq_self_of_ae_mem hc

/-- The same original continuous coupling has zero mass between any two
distinct actual blocks, without discarding or rebuilding any endpoints. -/
theorem FiniteOrderedMonochromeClasses.block_cross_mass_zero
    {μ ν : Measure ℝ} {δ : ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 ≤ p.2) (b c : C.StrictBlock) (hbc : b ≠ c) :
    γ (C.blockCell b ×ˢ C.blockCell c) = 0 := by
  obtain ⟨h₀, hN, _⟩ := C.surplus_facts_of_coupling hδ γ hγ hforward
  have hd := C.block_cells_disjoint h₀ hN hbc
  apply measure_mono_null (fun p hp ↦ ?_) (ae_iff.mp (C.ae_same_blockCell hδ γ hγ hforward b))
  intro heq
  exact disjoint_left.mp hd (heq.mp hp.1) hp.2

/-- Normalizing an actual positive block yields an internally constructed
positive margin at every proper original class-prefix cut. -/
theorem FiniteOrderedMonochromeClasses.exists_normalized_block_prefix_margin
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {δ : ℝ}
    (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 ≤ p.2) (b : C.StrictBlock) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : Fin (C.count + 1), b.lower < k → k < b.upper →
      η ≤ ((∑ i ∈ b.classes.filter (fun i ↦ i.val < k.val), μ.real (C.cell i)) -
        (∑ i ∈ b.classes.filter (fun i ↦ i.val < k.val), ν.real (C.cell i))) /
          μ.real (C.blockCell b) := by
  obtain ⟨_, _, hH⟩ := C.surplus_facts_of_coupling hδ γ hγ hforward
  obtain ⟨η, hη, hmargin⟩ := b.exists_uniform_proper_prefix_pos hH
  have hw := (C.block_mass_balanced_pos b).1
  refine ⟨η / μ.real (C.blockCell b), div_pos hη hw, ?_⟩
  intro k hlk hkr
  have heq := b.local_prefix_surplus (fun i ↦ μ.real (C.cell i))
    (fun i ↦ ν.real (C.cell i)) hlk.le hkr.le
  calc
    _ ≤ C.surplus k.val / μ.real (C.blockCell b) :=
      div_le_div_of_nonneg_right (hmargin k hlk hkr) hw.le
    _ = _ := congrArg (fun x : ℝ ↦ x / μ.real (C.blockCell b)) heq.symm

/-- A complete finite strict-block certificate keeps the actual original class
and plan laws together with the derived normalized proper-prefix margins. -/
structure OriginalFiniteOrderedStrictBlockCertificate
    {μ ν : Measure ℝ} (C : FiniteOrderedMonochromeClasses μ ν δ)
    (γ : Measure (ℝ × ℝ)) : Prop where
  surplus_nonneg : ∀ k ≤ C.count, 0 ≤ C.surplus k
  zero_endpoints : C.surplus 0 = 0 ∧ C.surplus C.count = 0
  class_partition : ∀ i : Fin C.count, ∃! b : C.StrictBlock, b.Contains i
  source_decomposition : (∑ b : C.StrictBlock, μ.restrict (C.blockCell b)) = μ
  target_decomposition : (∑ b : C.StrictBlock, ν.restrict (C.blockCell b)) = ν
  plan_decomposition : (∑ b : C.StrictBlock, γ.restrict ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell b)) = γ
  block_coupling : ∀ b : C.StrictBlock,
    Vlasov.IsCoupling (γ.restrict ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell b))
      (μ.restrict (C.blockCell b)) (ν.restrict (C.blockCell b))
  block_forward : ∀ b : C.StrictBlock, ∀ᵐ p ∂γ.restrict ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' C.blockCell b), p.1 < p.2
  block_mass : ∀ b : C.StrictBlock,
    0 < μ.real (C.blockCell b) ∧ μ.real (C.blockCell b) = ν.real (C.blockCell b)
  cross_mass_zero : ∀ b c : C.StrictBlock, b ≠ c → γ (C.blockCell b ×ˢ C.blockCell c) = 0
  normalized_margin : ∀ b : C.StrictBlock,
    ∃ η : ℝ, 0 < η ∧ ∀ k : Fin (C.count + 1), b.lower < k → k < b.upper →
      η ≤ ((∑ i ∈ b.classes.filter (fun i ↦ i.val < k.val), μ.real (C.cell i)) -
        (∑ i ∈ b.classes.filter (fun i ↦ i.val < k.val), ν.real (C.cell i))) /
          μ.real (C.blockCell b)

/-- An actual legal conditional coupling constructs the complete finite strict
block certificate. Every positive slack is an output, never a Hall assumption. -/
theorem FiniteOrderedMonochromeClasses.actual_strictBlockCertificate
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {δ : ℝ}
    (C : FiniteOrderedMonochromeClasses μ ν δ) (hδ : 0 < δ)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 < p.2) : OriginalFiniteOrderedStrictBlockCertificate C γ := by
  have hweak := hforward.mono fun _ h ↦ h.le
  obtain ⟨h₀, hN, hH⟩ := C.surplus_facts_of_coupling hδ γ hγ hweak
  exact
    { surplus_nonneg := hH
      zero_endpoints := ⟨h₀, hN⟩
      class_partition := exists_unique_finiteSurplusStrictBlock C.surplus C.count h₀ hN
      source_decomposition := C.sum_block_restrict h₀ hN μ C.ae_source_cover
      target_decomposition := C.sum_block_restrict h₀ hN ν C.ae_target_cover
      plan_decomposition := C.sum_block_coupling h₀ hN γ hγ
      block_coupling := C.block_restrict_coupling hδ γ hγ hweak
      block_forward := fun _ ↦ ae_restrict_of_ae hforward
      block_mass := C.block_mass_balanced_pos
      cross_mass_zero := C.block_cross_mass_zero hδ γ hγ hweak
      normalized_margin := C.exists_normalized_block_prefix_margin hδ γ hγ hweak }

/-- Genuine original support separation and the actual legal conditional plan
produce both the finite classes and all strict blocks without caller-supplied
classes, active components, tight cuts, Hall inequalities, or positive margins. -/
theorem exists_originalFiniteOrderedStrictBlockCertificate
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {δ D : ℝ}
    (hδ : 0 < δ) (hsep : ConditionalClockSupportBounds μ ν δ D)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hforward : ∀ᵐ p ∂γ, p.1 ≤ p.2) :
    ∃ C : FiniteOrderedMonochromeClasses μ ν δ, OriginalFiniteOrderedStrictBlockCertificate C γ := by
  obtain ⟨C⟩ := exists_finiteOrderedMonochromeClasses hδ hsep
  exact ⟨C, C.actual_strictBlockCertificate hδ γ hγ
    (hsep.ae_strict_order_of_coupling hδ hγ hforward)⟩

end OTSelector.Reconstruction
