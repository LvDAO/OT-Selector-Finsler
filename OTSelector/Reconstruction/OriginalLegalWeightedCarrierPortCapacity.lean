import OTSelector.Reconstruction.OriginalLegalWeightedClockGapExhaustion
import OTSelector.Reconstruction.MarkedStationaryValueLegalReserveRemovalHall

/-!
# Partial legal completion of actual original carrier ports

The retained core is kept in full. Only its free sources whose original clock
lies in the genuine positive-gap carrier are completed; remaining deficiency
is charged to actual outside-carrier free rows and original boundary escape.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace PartialMatching
variable {m n : ℕ}

/-- Prefix feasibility on an actual subset of the original free rows
completes that entire subset while retaining EVERY original core edge. -/
theorem exists_legal_clock_partial_completion_of_active_prefix_counts
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (active : Finset (Fin m)) (ha : active ⊆ σ.freeRows)
    (hprefix : ∀ i ∈ active,
      (active.filter (fun i' ↦ source i ≤ source i')).card ≤
        (σ.freeCols.filter (fun j ↦ source i < target j)).card) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ σ.edges ⊆ τ.edges ∧
      active ⊆ τ.rows ∧ τ.card = σ.card + active.card ∧
      τ.freeRows ⊆ σ.freeRows \ active ∧
      ∃ ρ : OTSelector.PartialMatching m n,
        IsLegal (residualAllowed (scalarClockLegalGraph source target) σ) ρ ∧
        ρ.card = active.card ∧ ρ.rows = active ∧ τ.edges = σ.edges ∪ ρ.edges := by
  have hp (i : active) :
      (Finset.univ.filter (fun i' : active ↦ source i.val ≤ source i'.val)).card ≤
        (Finset.univ.filter (fun j : σ.freeCols ↦ source i.val < target j.val)).card := by
    rw [card_univ_filter_finset_subtype active (fun i' : Fin m ↦ source i.val ≤ source i'),
      card_univ_filter_finset_subtype σ.freeCols (fun j : Fin n ↦ source i.val < target j)]
    exact hprefix i.val i.property
  obtain ⟨f, hf, hrel⟩ := exists_injective_forward_of_clock_prefix_counts
    (fun i : active ↦ source i.val) (fun j : σ.freeCols ↦ target j.val) hp
  let ρ : OTSelector.PartialMatching m n :=
    { edges := Finset.univ.image (fun i : active ↦ (i.val, (f i).val))
      row_inj := by
        intro e he e' he' h
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he'
        exact congrArg (fun i : active ↦ (i.val, (f i).val)) (Subtype.ext h)
      col_inj := by
        intro e he e' he' h
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he'
        exact congrArg (fun i : active ↦ (i.val, (f i).val)) (hf (Subtype.ext h)) }
  have hρ : IsLegal (residualAllowed (scalarClockLegalGraph source target) σ) ρ := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel i⟩,
      (Finset.mem_sdiff.mp (ha i.property)).2,
      (Finset.mem_sdiff.mp (f i).property).2⟩
  have hcard : ρ.card = active.card := by
    dsimp only [OTSelector.PartialMatching.card, ρ]
    rw [Finset.card_image_of_injective _ (fun i j h ↦ Subtype.ext (Prod.mk.inj h).1),
      Finset.card_univ, Fintype.card_coe]
  have hρrows : ρ.rows = active := by
    apply le_antisymm
    · intro i hi
      obtain ⟨e, he, hei⟩ := Finset.mem_image.mp hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
      exact hei ▸ j.property
    · intro i hi
      exact Finset.mem_image.mpr ⟨(i, (f ⟨i, hi⟩).val),
        Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩, rfl⟩
  obtain ⟨hr, hc⟩ := residualAllowed_disjoint σ ρ hρ
  let τ := σ.union ρ hr hc
  have hsub : σ.edges ⊆ τ.edges := Finset.subset_union_left
  have hactive : active ⊆ τ.rows := by
    intro i hi
    exact Finset.mem_image.mpr ⟨(i, (f ⟨i, hi⟩).val),
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩), rfl⟩
  have hrows : σ.rows ⊆ τ.rows := Finset.image_subset_image hsub
  refine ⟨τ, isLegal_union_residual σ ρ hσ hρ, hsub, hactive, ?_, ?_,
    ρ, hρ, hcard, hρrows, rfl⟩
  · exact (OTSelector.PartialMatching.card_union σ ρ hr hc).trans (by rw [hcard])
  · intro i hi
    have hnot := (Finset.mem_sdiff.mp hi).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun h ↦ hnot (hrows h)⟩, fun h ↦ hnot (hactive h)⟩

/-- The original adaptive-removal budget controls prefix counts on just the
actual free carrier rows. No premise places all free rows in the carrier. -/
theorem active_clock_prefix_counts_of_adaptive_reserve_slack
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n) (RS : Finset (Fin m)) (RT : Finset (Fin n))
    (K : Set ℝ) (H : ℝ)
    (hslack : ∀ a ∈ K, H ≤
      ((RT.filter (fun j ↦ a < target j)).card : ℝ) -
        ((RS.filter (fun i ↦ a ≤ source i)).card : ℝ))
    (hbudget : ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) ≤ H) :
    ∀ i ∈ σ.freeRows.filter (fun i ↦ source i ∈ K),
      ((σ.freeRows.filter (fun i ↦ source i ∈ K)).filter
        (fun i' ↦ source i ≤ source i')).card ≤
          (σ.freeCols.filter (fun j ↦ source i < target j)).card := by
  intro i hi
  let active := σ.freeRows.filter (fun i ↦ source i ∈ K)
  have hs := card_filter_le_filter_add_sdiff active RS (fun i' ↦ source i ≤ source i')
  have ht := card_filter_le_filter_add_sdiff RT σ.freeCols (fun j ↦ source i < target j)
  have hd : (active \ RS).card ≤ (σ.freeRows \ RS).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) (Subset.refl _))
  have hsR := Nat.cast_le (α := ℝ).mpr hs
  have htR := Nat.cast_le (α := ℝ).mpr ht
  have hdR := Nat.cast_le (α := ℝ).mpr hd
  simp only [Nat.cast_add] at hsR htR
  have hh := hslack (source i) (Finset.mem_filter.mp hi).2
  apply Nat.cast_le (α := ℝ).mp
  linarith

/-- All free carrier rows are legally completed while the original core
remains intact. The only possible source deficiency is the actual number
of free source rows outside the carrier. -/
theorem exists_legal_carrier_completion_of_adaptive_reserve_slack
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal (scalarClockLegalGraph source target) σ)
    (RS : Finset (Fin m)) (RT : Finset (Fin n)) (K : Set ℝ) (H : ℝ)
    (hslack : ∀ a ∈ K, H ≤
      ((RT.filter (fun j ↦ a < target j)).card : ℝ) -
        ((RS.filter (fun i ↦ a ≤ source i)).card : ℝ))
    (hbudget : ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) ≤ H) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ σ.edges ⊆ τ.edges ∧
      (σ.freeRows.filter (fun i ↦ source i ∈ K)) ⊆ τ.rows ∧
      τ.freeRows ⊆ σ.freeRows.filter (fun i ↦ source i ∉ K) ∧
      m - τ.card ≤ (σ.freeRows.filter (fun i ↦ source i ∉ K)).card := by
  obtain ⟨τ, hτ, hsub, ha, _, hf, _⟩ :=
    exists_legal_clock_partial_completion_of_active_prefix_counts source target σ hσ
      (σ.freeRows.filter (fun i ↦ source i ∈ K)) (Finset.filter_subset _ _)
      (active_clock_prefix_counts_of_adaptive_reserve_slack source target σ RS RT K H hslack hbudget)
  have heq : σ.freeRows \ (σ.freeRows.filter (fun i ↦ source i ∈ K)) =
      σ.freeRows.filter (fun i ↦ source i ∉ K) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [heq] at hf
  exact ⟨τ, hτ, hsub, ha, hf, by
    rw [← OTSelector.PartialMatching.card_freeRows τ]
    exact Finset.card_le_card hf⟩

end PartialMatching
/-- Original carrier-free-row deficiency is bounded by actual bad reserve
indices and the exact original adaptive-removal budget. -/
theorem PartialMatching.carrier_freeRows_count_le_bad_reserve_add_budget
    {m n : ℕ} (source : Fin m → ℝ) (σ : OTSelector.PartialMatching m n)
    (RS : Finset (Fin m)) (RT : Finset (Fin n)) (K : Set ℝ) (H : ℝ)
    (hbudget : ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) ≤ H) :
    ((σ.freeRows.filter (fun i ↦ source i ∉ K)).card : ℝ) ≤
      ((RS.filter (fun i ↦ source i ∉ K)).card : ℝ) + H := by
  have h := Nat.cast_le (α := ℝ).mpr
    (card_filter_le_filter_add_sdiff σ.freeRows RS (fun i ↦ source i ∉ K))
  simp only [Nat.cast_add] at h
  have hn : 0 ≤ ((RT \ σ.freeCols).card : ℝ) := Nat.cast_nonneg _
  linarith

/-- The original reserve embedding preserves literal finite-set counts,
including the original clocks and every multiplicity. -/
theorem card_filter_originalReserveAtomEmbedding_image
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {m : ℕ}
    (ν : Measure X) (source : Fin m → X) (B : Set X) :
    ((Finset.univ.image (originalReserveAtomEmbedding ν source)).filter
      (fun i ↦ source i ∈ B)).card = blockSetCount B (originalReserveAtomArray ν source) := by
  rw [Finset.filter_image, Finset.card_image_of_injective _
    (originalReserveAtomEmbedding ν source).injective]
  rfl

/-- The actual first-core escape plus actual original bad reserve mass is
a budget for source deficiency after partial carrier completion. -/
def legalOriginalCarrierPortBudget (q : ℕ) (U : Set (LegalMarkedPhysicalPoint q))
    (K : Set ℝ) (s r : LegalMarkedOptimalInputScene q) : ℝ≥0∞ :=
  legalInputColorMeasure q r.2 0 (U ∩ (univ ×ˢ Kᶜ)) +
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)

/-- The unchanged original color count is literal input measure evaluation. -/
theorem legalInputColorMeasure_apply_eq_input_product (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    legalInputColorMeasure q μ c B = (μ : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) := by
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hB,
    Measure.restrict_apply (hB.preimage measurable_fst)]
  rfl

/-- A finite real count bounded by extended masses is bounded by their sum,
including the possibility of an infinite actual escape mass. -/
theorem natCast_le_add_of_cast_le_toReal_add (k : ℕ) (x y : ℝ≥0∞)
    (h : (k : ℝ) ≤ x.toReal + y.toReal) : (k : ℝ≥0∞) ≤ x + y := by
  by_cases hx : x = ∞
  · simp only [hx, top_add, le_top]
  by_cases hy : y = ∞
  · simp only [hy, add_top, le_top]
  have hh := ENNReal.ofReal_le_ofReal h
  simpa only [ENNReal.ofReal_natCast,
    ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hx, ENNReal.ofReal_toReal hy] using hh

/-- The actual reserve arrays of an original core yield a partial legal
completion preserving that whole core. All free carrier rows are matched;
remaining source deficiency is bounded by bad original reserve mass plus
the literal first-plan window escape. -/
theorem IsOriginalReserveWindowCore.exists_carrier_completion
    {q : ℕ} {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    {K : Set ℝ} (hK : MeasurableSet K) {cost : LegalMarkedPhysicalEdge q → ℝ}
    {s r : LegalMarkedOptimalInputScene q}
    {b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)}
    (hcore : IsOriginalReserveWindowCore q U cost s r b) (H : ℝ)
    (hslack : ∀ a ∈ K, H ≤ legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi a)) 1 r -
      legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici a)) 0 r)
    (hescape : ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)).toReal ≤ H) :
    let source := legalOriginalBlockRestriction U b.1
    let target := legalOriginalBlockRestriction U b.2
    ∃ σ τ : OTSelector.PartialMatching source.1 target.1,
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (source.2 i).2)
        (fun j ↦ (target.2 j).2)) σ ∧
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U) =
        ∑ e ∈ σ.edges, Measure.dirac (source.2 e.1, target.2 e.2) ∧
      (∫ e in U ×ˢ U, cost e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
        σ.cost (fun i j ↦ cost (source.2 i, target.2 j)) ∧
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (source.2 i).2)
        (fun j ↦ (target.2 j).2)) τ ∧ σ.edges ⊆ τ.edges ∧
      (σ.freeRows.filter (fun i ↦ (source.2 i).2 ∈ K)) ⊆ τ.rows ∧
      τ.freeRows ⊆ σ.freeRows.filter (fun i ↦ (source.2 i).2 ∉ K) ∧
      ((source.1 - τ.card : ℕ) : ℝ) ≤
        (legalInputColorMeasure q r.2 0 (U ∩ (univ ×ˢ Kᶜ))).toReal +
          ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)).toReal ∧
      ((source.1 - τ.card : ℕ) : ℝ≥0∞) ≤ legalOriginalCarrierPortBudget q U K s r := by
  dsimp only [IsOriginalReserveWindowCore] at hcore
  dsimp only
  obtain ⟨σ, hσ, hplan, _, _, hcost, hs, ht, _, _, hbudget⟩ := hcore
  let source := legalOriginalBlockRestriction U b.1
  let target := legalOriginalBlockRestriction U b.2
  let νs := (legalInputColorMeasure q r.2 0).restrict U
  let νt := (legalInputColorMeasure q r.2 1).restrict U
  let RS := Finset.univ.image (originalReserveAtomEmbedding νs source.2)
  let RT := Finset.univ.image (originalReserveAtomEmbedding νt target.2)
  have hcounts (a : ℝ) :
      (((RS.filter (fun i ↦ a ≤ (source.2 i).2)).card : ℝ) =
        legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici a)) 0 r) ∧
      (((RT.filter (fun j ↦ a < (target.2 j).2)).card : ℝ) =
        legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi a)) 1 r) := by
    constructor
    · have hh := originalReserveArray_clockCount_eq_actual (B := univ ×ˢ Ici a) r 0 hU
        (MeasurableSet.univ.prod measurableSet_Ici) _ hs
      rw [← card_filter_originalReserveAtomEmbedding_image νs source.2 (univ ×ˢ Ici a)] at hh
      simpa only [Set.mem_prod, Set.mem_univ, Set.mem_Ici, true_and] using hh
    · have hh := originalReserveArray_clockCount_eq_actual (B := univ ×ˢ Ioi a) r 1 hU
        (MeasurableSet.univ.prod measurableSet_Ioi) _ ht
      rw [← card_filter_originalReserveAtomEmbedding_image νt target.2 (univ ×ˢ Ioi a)] at hh
      simpa only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] using hh
  have hb : ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) ≤ H :=
    hbudget.trans_le hescape
  obtain ⟨τ, hτ, hsub, ha, hf, hd⟩ :=
    PartialMatching.exists_legal_carrier_completion_of_adaptive_reserve_slack
      (fun i ↦ (source.2 i).2) (fun j ↦ (target.2 j).2) σ hσ RS RT K H
      (fun a ha ↦ by rw [(hcounts a).1, (hcounts a).2]; exact hslack a ha) hb
  refine ⟨σ, τ, hσ, hplan, hcost, hτ, hsub, ha, hf, ?_⟩
  have hbad := PartialMatching.carrier_freeRows_count_le_bad_reserve_add_budget
    (fun i ↦ (source.2 i).2) σ RS RT K
      (((s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)).toReal) hbudget.le
  have hread : ((RS.filter (fun i ↦ (source.2 i).2 ∉ K)).card : ℝ) =
      (legalInputColorMeasure q r.2 0 (U ∩ (univ ×ˢ Kᶜ))).toReal := by
    have hh := originalReserveArray_clockCount_eq_actual r 0 hU
      (MeasurableSet.univ.prod hK.compl) _ hs
    rw [← card_filter_originalReserveAtomEmbedding_image νs source.2 (univ ×ˢ Kᶜ)] at hh
    rw [legalInputColorMeasure_apply_eq_input_product q r.2 0
      (hU.inter (MeasurableSet.univ.prod hK.compl))]
    simpa only [Set.mem_prod, Set.mem_univ, Set.mem_compl_iff, true_and,
      legalOriginalWindowCount] using hh
  rw [hread] at hbad
  have hfinal := (Nat.cast_le (α := ℝ).mpr hd).trans hbad
  exact ⟨hfinal, natCast_le_add_of_cast_le_toReal_add _ _ _ hfinal⟩

local instance carrierPortCapacityInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance carrierPortCapacityPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Dilation preserves color and clock in the actual original color count. -/
theorem legalInputColorMeasure_dilation_apply (q : ℕ) (d : ℝ) (hd : d ≠ 0)
    (s : LegalMarkedOptimalInputScene q) (color : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    legalInputColorMeasure q (legalMarkedInputSceneDilation q d hd s).2 color B =
      legalInputColorMeasure q s.2 color ((legalMarkedPointDilation q d hd) ⁻¹' B) := by
  change legalInputColorMeasure q
    (localFiniteMapHomeomorph (legalColoredInputDilation q d hd) s.2) color B = _
  rw [legalInputColorMeasure_dilation, Measure.map_apply
    (legalMarkedPointDilation q d hd).continuous.measurable hB]

/-- The actual immutable input color window mass is measurable. -/
theorem measurable_legalInputColorMeasure_window (q : ℕ) (color : Fin 2)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    Measurable (fun s : LegalMarkedOptimalInputScene q ↦ legalInputColorMeasure q s.2 color B) := by
  simpa only [legalMarkedInputColorKernel_apply] using
    (Kernel.measurable_coe (legalMarkedInputColorKernel q color) hB)

/-- The original actual carrier-port budget is measurable before choosing
any legal extension or ordering any selected reserve array. -/
theorem measurable_legalOriginalCarrierPortBudget (q : ℕ)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    {K : Set ℝ} (hK : MeasurableSet K) :
    Measurable (fun p : LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q ↦
      legalOriginalCarrierPortBudget q U K p.1 p.2) := by
  apply Measurable.add
  · exact (measurable_legalInputColorMeasure_window q 0
      (hU.inter (MeasurableSet.univ.prod hK.compl))).comp measurable_snd
  · exact (((Measure.measurable_coe (hU.prod hU.compl)).comp
      measurable_localFiniteMeasure_coe).comp measurable_fst.fst).comp measurable_fst

/-- Genuine original reserve mass outside a carrier has exactly its original
physical mean, including the true inverse dilation Jacobian. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_dilated_original_input_color
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0) {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) :
    (∫⁻ s, legalInputColorMeasure q (legalMarkedInputSceneDilation q d hd s).2 0 B
      ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) =
      ENNReal.ofReal |(d ^ q)⁻¹| * ((volume : Measure (Fin q → ℝ)).prod α) B := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  simp_rw [legalInputColorMeasure_dilation_apply q d hd _ 0 hB]
  rw [lintegral_legalInputColorMeasure_eq_intensity q _ 0
    ((legalMarkedPointDilation q d hd).continuous.measurable hB),
    N.inputColorIntensities_eq_volume_prod.1,
    ← Measure.map_apply (legalMarkedPointDilation q d hd).continuous.measurable hB,
    map_physicalIntensity_legalMarkedPointDilation q d hd,
    Measure.smul_apply, smul_eq_mul]

/-- The SAME labelled joining gives the actual bad-reserve expected count.
No law is assigned to a selected free subcloud. -/
theorem lintegral_original_bad_reserve_le_clock_complement
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure (LegalOriginalReserveWindowExperiment q))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (d : ℝ) (hd : d ≠ 0) {V : Set (Fin q → ℝ)} (hV : MeasurableSet V)
    {A K : Set ℝ} (hA : MeasurableSet A) (hK : MeasurableSet K) :
    (∫⁻ p, legalInputColorMeasure q (legalMarkedInputSceneDilation q d hd p.1.2).2 0
      ((V ×ˢ A) ∩ (univ ×ˢ Kᶜ)) ∂P) ≤
      ENNReal.ofReal |(d ^ q)⁻¹| * volume V * α Kᶜ := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  have hB := (hV.prod hA).inter (MeasurableSet.univ.prod hK.compl)
  have hm := (measurable_legalInputColorMeasure_window q 0 hB).comp
    (continuous_legalMarkedInputSceneDilation q d hd).measurable
  have hproj : Measurable (fun p : LegalOriginalReserveWindowExperiment q ↦ p.1.2) :=
    measurable_snd.comp measurable_fst
  have heq : (V ×ˢ A) ∩ (univ ×ˢ Kᶜ) = V ×ˢ (A ∩ Kᶜ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    tauto
  calc
    _ = ∫⁻ s, legalInputColorMeasure q (legalMarkedInputSceneDilation q d hd s).2 0
        ((V ×ˢ A) ∩ (univ ×ˢ Kᶜ))
        ∂(P.map (fun p : LegalOriginalReserveWindowExperiment q ↦ p.1.2)) :=
      (lintegral_map hm hproj).symm
    _ = _ := by rw [original_labelled_reserve_coordinate_map_eq M N P hP]
    _ = ENNReal.ofReal |(d ^ q)⁻¹| *
        ((volume : Measure (Fin q → ℝ)).prod α) ((V ×ˢ A) ∩ (univ ×ˢ Kᶜ)) :=
      N.lintegral_dilated_original_input_color d hd hB
    _ ≤ _ := by
      rw [heq, Measure.prod_prod, ← mul_assoc]
      gcongr
      exact inter_subset_right

/-- The actual carrier-port budget has the expected original reserve loss
plus the literal expected first-plan escape. This is independent of any
choice or measurability of the later partial legal extension. -/
theorem lintegral_originalCarrierPortBudget_le
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure (LegalOriginalReserveWindowExperiment q))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V)
    {A K : Set ℝ} (hA : MeasurableSet A) (hK : MeasurableSet K) :
    (∫⁻ p, legalOriginalCarrierPortBudget q (V ×ˢ A) K
      (legalMarkedInputSceneDilation q c hc p.1.1)
      (legalMarkedInputSceneDilation q d hd p.1.2) ∂P) ≤
      ENNReal.ofReal |(d ^ q)⁻¹| * volume V * α Kᶜ +
      ∫⁻ p, ((legalMarkedInputSceneDilation q c hc p.1.1).1.1 :
        Measure (LegalMarkedPhysicalEdge q)) ((V ×ˢ A) ×ˢ (V ×ˢ A)ᶜ) ∂P := by
  have hm : Measurable (fun p : LegalOriginalReserveWindowExperiment q ↦
      legalInputColorMeasure q (legalMarkedInputSceneDilation q d hd p.1.2).2 0
        ((V ×ˢ A) ∩ (univ ×ˢ Kᶜ))) :=
    ((measurable_legalInputColorMeasure_window q 0
      ((hV.prod hA).inter (MeasurableSet.univ.prod hK.compl))).comp
        (continuous_legalMarkedInputSceneDilation q d hd).measurable).comp
          (measurable_snd.comp measurable_fst)
  unfold legalOriginalCarrierPortBudget
  rw [lintegral_add_left hm]
  exact add_le_add (lintegral_original_bad_reserve_le_clock_complement M N P hP d hd hV hA hK) le_rfl

/-- After the unchanged actual spatial-volume normalization, the port budget
is rho times the ORIGINAL source clock loss plus the ORIGINAL first escape. -/
theorem normalized_lintegral_originalCarrierPortBudget_le
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure (LegalOriginalReserveWindowExperiment q))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V) (hVzero : volume V ≠ 0)
    (hVtop : volume V ≠ ∞) {A K : Set ℝ} (hA : MeasurableSet A) (hK : MeasurableSet K) :
    (volume V)⁻¹ * (∫⁻ p, legalOriginalCarrierPortBudget q (V ×ˢ A) K
      (legalMarkedInputSceneDilation q c hc p.1.1)
      (legalMarkedInputSceneDilation q d hd p.1.2) ∂P) ≤
      ENNReal.ofReal |(d ^ q)⁻¹| * α Kᶜ + (volume V)⁻¹ *
      ∫⁻ p, ((legalMarkedInputSceneDilation q c hc p.1.1).1.1 :
        Measure (LegalMarkedPhysicalEdge q)) ((V ×ˢ A) ×ˢ (V ×ˢ A)ᶜ) ∂P := by
  have hh : (volume V)⁻¹ * (∫⁻ p, legalOriginalCarrierPortBudget q (V ×ˢ A) K
      (legalMarkedInputSceneDilation q c hc p.1.1)
      (legalMarkedInputSceneDilation q d hd p.1.2) ∂P) ≤
      (volume V)⁻¹ * (ENNReal.ofReal |(d ^ q)⁻¹| * volume V * α Kᶜ +
        ∫⁻ p, ((legalMarkedInputSceneDilation q c hc p.1.1).1.1 :
          Measure (LegalMarkedPhysicalEdge q)) ((V ×ˢ A) ×ˢ (V ×ˢ A)ᶜ) ∂P) := by
    gcongr
    exact lintegral_originalCarrierPortBudget_le M N P hP c d hc hd hV hA hK
  apply hh.trans_eq
  rw [mul_add]
  congr 1
  calc
    _ = ENNReal.ofReal |(d ^ q)⁻¹| * ((volume V)⁻¹ * volume V) * α Kᶜ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hVzero hVtop, mul_one]

/-- Actual first-plan escape is bounded by its own immutable original
source input. No transport or displacement moment is needed. -/
theorem IsFullOriginalInputMatching.window_escape_le_source_input
    {q : ℕ} {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ) ≤
      legalInputColorMeasure q s.2 0 U := by
  calc
    _ ≤ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.fst ⁻¹' U) :=
      measure_mono fun _ h ↦ h.1
    _ = ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map Prod.fst) U :=
      (Measure.map_apply measurable_fst hU).symm
    _ = _ := congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ U) hs.source_marginal

/-- The literal original first-plan escape in the SAME joining has finite
unit-density first moment. The sharper carrier budget retains its actual
escape expectation rather than replacing it by this coarse bound. -/
theorem lintegral_original_first_window_escape_le
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure (LegalOriginalReserveWindowExperiment q))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (c : ℝ) (hc : c ≠ 0) {V : Set (Fin q → ℝ)} (hV : MeasurableSet V)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ p, ((legalMarkedInputSceneDilation q c hc p.1.1).1.1 :
      Measure (LegalMarkedPhysicalEdge q)) ((V ×ˢ A) ×ˢ (V ×ˢ A)ᶜ) ∂P) ≤
      ENNReal.ofReal |(c ^ q)⁻¹| * volume V := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← M.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  have hU := hV.prod hA
  have hp : P.map (fun p ↦ p.1.1) = (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
    rw [show (fun p : LegalOriginalReserveWindowExperiment q ↦ p.1.1) =
      Prod.fst ∘ Prod.fst from rfl, ← Measure.map_map measurable_fst measurable_fst, hP]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hm := (((Measure.measurable_coe (hU.prod hU.compl)).comp
    measurable_localFiniteMeasure_coe).comp measurable_fst.fst).comp
      (continuous_legalMarkedInputSceneDilation q c hc).measurable
  calc
    _ = ∫⁻ s, ((legalMarkedInputSceneDilation q c hc s).1.1 :
        Measure (LegalMarkedPhysicalEdge q)) ((V ×ˢ A) ×ˢ (V ×ˢ A)ᶜ)
        ∂(P.map (fun p : LegalOriginalReserveWindowExperiment q ↦ p.1.1)) :=
      (lintegral_map hm (measurable_fst.comp measurable_fst)).symm
    _ = _ := by rw [hp]
    _ ≤ ∫⁻ s, legalInputColorMeasure q (legalMarkedInputSceneDilation q c hc s).2 0 (V ×ˢ A)
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
      apply lintegral_mono_ae
      filter_upwards [M.full_matching] with s hs
      exact (hs.dilation c hc).window_escape_le_source_input hU
    _ = ENNReal.ofReal |(c ^ q)⁻¹| * volume V * α A := by
      rw [M.lintegral_dilated_original_input_color c hc hU, Measure.prod_prod, ← mul_assoc]
    _ ≤ _ := by
      exact mul_le_of_le_one_right' (prob_le_one : α A ≤ 1)

/-- Finite original spatial windows have a finite genuine carrier-port
budget expectation, derived from original input intensities and matching
marginals rather than from a new integrability premise. -/
theorem lintegral_originalCarrierPortBudget_lt_top
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure (LegalOriginalReserveWindowExperiment q))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V) (hVtop : volume V ≠ ∞)
    {A K : Set ℝ} (hA : MeasurableSet A) (hK : MeasurableSet K) :
    (∫⁻ p, legalOriginalCarrierPortBudget q (V ×ˢ A) K
      (legalMarkedInputSceneDilation q c hc p.1.1)
      (legalMarkedInputSceneDilation q d hd p.1.2) ∂P) < ∞ := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  have hb := lintegral_originalCarrierPortBudget_le M N P hP c d hc hd hV hA hK
  have he := lintegral_original_first_window_escape_le M N P hP c hc hV hA
  have ht : ENNReal.ofReal |(d ^ q)⁻¹| * volume V * α Kᶜ +
      ENNReal.ofReal |(c ^ q)⁻¹| * volume V < ∞ := by finiteness
  exact (hb.trans (add_le_add le_rfl he)).trans_lt ht

end OTSelector.Reconstruction
