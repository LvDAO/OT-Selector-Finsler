import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocksSets

/-! The same actual coupling decomposes into positive original half-open clock blocks. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Actual original class restrictions are unchanged inside their own source or target block. -/
theorem block_original_class_restrict (b : G.ClockSlabBlock μ ν) (i : Fin G.count) (hi : b.Contains i) :
    (μ.restrict (G.sourceBlockCell μ ν b)).restrict (G.sourceCell i) = μ.restrict (G.sourceCell i) ∧
      (ν.restrict (G.targetBlockCell μ ν b)).restrict (G.targetCell i) = ν.restrict (G.targetCell i) :=
  ⟨Measure.restrict_restrict_of_subset (fun _ hx ↦ (G.mem_sourceBlockCell_iff b hx).mpr hi),
    Measure.restrict_restrict_of_subset (fun _ hx ↦ (G.mem_targetBlockCell_iff b hx).mpr hi)⟩

/-- A discarded zero block carries genuinely zero mass of the same original plan. -/
theorem zeroSlabBlock_plan [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (γ : Measure (ℝ × ℝ)) (hγ : Vlasov.IsCoupling γ μ ν)
    (b : G.ClockSlabBlock μ ν) (hb : b ∉ G.positiveSlabBlocks μ ν) :
    γ.restrict (Prod.fst ⁻¹' G.sourceBlockCell μ ν b) = 0 := by
  apply Measure.restrict_eq_zero.mpr
  rw [← Measure.map_apply measurable_fst (G.blockCells_measurable b).1, hγ.1]
  exact Measure.restrict_eq_zero.mp (G.zeroSlabBlock_restrict b hb).1

section ActualCoupling
variable {δ D : ℝ} (hδ : 0 < δ) (hsep : ConditionalClockSupportBounds μ ν δ D)
  (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
  (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
  (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
  (hweak : ∀ᵐ p ∂γ, p.1 ≤ p.2)
include hδ hsep hγ hs ht hmono hweak

/-- Every real plan point belongs to the same constructed block on both sides,
with each color retaining its own original half-open block set. -/
theorem ae_same_blockCells (b : G.ClockSlabBlock μ ν) :
    ∀ᵐ p ∂γ, p.1 ∈ G.sourceBlockCell μ ν b ↔ p.2 ∈ G.targetBlockCell μ ν b := by
  classical
  obtain ⟨hrow, hcol⟩ := G.actualSlabFlow_marginals γ hγ hs ht
  let P := actualClockClassFlow γ G.sourceCell G.targetCell
  let a := fun i ↦ μ.real (G.sourceCell i)
  let c := fun i ↦ ν.real (G.targetCell i)
  have hP := actualClockClassFlow_nonneg γ G.sourceCell G.targetCell
  have hz := G.actualSlabFlow_zero hδ hsep γ hγ hmono hweak
  have hpairs : ∀ i j : Fin G.count, ∀ᵐ p ∂γ,
      p ∈ G.sourceCell i ×ˢ G.targetCell j → (b.Contains i ↔ b.Contains j) := by
    intro i j
    by_cases hsame : b.Contains i ↔ b.Contains j
    · exact ae_of_all _ fun _ _ ↦ hsame
    have hzij : P i j = 0 := by
      by_cases hi : b.Contains i
      · exact finiteClassFlow_zero_leaving_block P a c hP hrow hcol hz b i j hi (by tauto)
      · exact finiteClassFlow_zero_entering_block P a c hP hrow hcol hz b i j hi (by tauto)
    have hnull : γ (G.sourceCell i ×ˢ G.targetCell j) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top γ _)).mp hzij
    exact ae_iff.mpr (measure_mono_null (fun _ hp ↦ (not_imp.mp hp).1) hnull)
  have hall : ∀ᵐ p ∂γ, ∀ i j : Fin G.count,
      p ∈ G.sourceCell i ×ˢ G.targetCell j → (b.Contains i ↔ b.Contains j) :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hpairs i)
  have hsc : ∀ᵐ p ∂γ, p.1 ∈ ⋃ i, G.sourceCell i :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hγ.1]; exact hs)
  have htc : ∀ᵐ p ∂γ, p.2 ∈ ⋃ j, G.targetCell j :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hγ.2]; exact ht)
  filter_upwards [hall, hsc, htc] with p hp hsc htc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hsc
  obtain ⟨j, hj⟩ := mem_iUnion.mp htc
  rw [G.mem_sourceBlockCell_iff b hi, G.mem_targetBlockCell_iff b hj]
  exact hp i j ⟨hi, hj⟩

/-- Restrict the unchanged plan to one source block; both original restricted
marginals are exact, despite their distinct endpoint conventions. -/
theorem block_restrict_coupling (b : G.ClockSlabBlock μ ν) :
    Vlasov.IsCoupling (γ.restrict (Prod.fst ⁻¹' G.sourceBlockCell μ ν b))
      (μ.restrict (G.sourceBlockCell μ ν b)) (ν.restrict (G.targetBlockCell μ ν b)) := by
  have hm := G.blockCells_measurable b
  have heq : Prod.fst ⁻¹' G.sourceBlockCell μ ν b =ᵐ[γ] Prod.snd ⁻¹' G.targetBlockCell μ ν b :=
    (G.ae_same_blockCells hδ hsep γ hγ hs ht hmono hweak b).mono fun _ hp ↦ propext hp
  constructor
  · exact (Measure.restrict_map measurable_fst hm.1).symm.trans
      (congrArg (fun θ : Measure ℝ ↦ θ.restrict (G.sourceBlockCell μ ν b)) hγ.1)
  · calc
      _ = (γ.restrict (Prod.snd ⁻¹' G.targetBlockCell μ ν b)).map Prod.snd :=
        congrArg (fun θ : Measure (ℝ × ℝ) ↦ θ.map Prod.snd) (Measure.restrict_congr_set heq)
      _ = (γ.map Prod.snd).restrict (G.targetBlockCell μ ν b) := (Measure.restrict_map measurable_snd hm.2).symm
      _ = _ := congrArg (fun θ : Measure ℝ ↦ θ.restrict (G.targetBlockCell μ ν b)) hγ.2

/-- The same original plan has no mass between distinct constructed blocks. -/
theorem block_cross_mass_zero (b c : G.ClockSlabBlock μ ν) (hbc : b ≠ c) :
    γ (G.sourceBlockCell μ ν b ×ˢ G.targetBlockCell μ ν c) = 0 := by
  obtain ⟨h₀, hN, _⟩ := G.clockSlabSurplus_facts hδ hsep γ hγ hs ht hmono hweak
  have hd := (G.blockCells_disjoint h₀ hN).2 hbc
  apply measure_mono_null (fun p hp ↦ ?_) (ae_iff.mp (G.ae_same_blockCells hδ hsep γ hγ hs ht hmono hweak b))
  intro heq
  exact disjoint_left.mp hd (heq.mp hp.1) hp.2

/-- Filtering only actual positive blocks loses no original source, target,
or plan measure; all zero blocks have been proved literally zero. -/
theorem sum_positiveBlock_measures [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∑ b ∈ G.positiveSlabBlocks μ ν, μ.restrict (G.sourceBlockCell μ ν b)) = μ ∧
      (∑ b ∈ G.positiveSlabBlocks μ ν, ν.restrict (G.targetBlockCell μ ν b)) = ν ∧
      (∑ b ∈ G.positiveSlabBlocks μ ν, γ.restrict (Prod.fst ⁻¹' G.sourceBlockCell μ ν b)) = γ := by
  classical
  obtain ⟨h₀, hN, _⟩ := G.clockSlabSurplus_facts hδ hsep γ hγ hs ht hmono hweak
  have hd := G.blockCells_disjoint h₀ hN
  have hc := G.blockCells_ae_cover h₀ hN hs ht
  have hsumS : (∑ b : G.ClockSlabBlock μ ν, μ.restrict (G.sourceBlockCell μ ν b)) = μ := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd.1 (fun b ↦ (G.blockCells_measurable b).1)]
    exact Measure.restrict_eq_self_of_ae_mem hc.1
  have hsumT : (∑ b : G.ClockSlabBlock μ ν, ν.restrict (G.targetBlockCell μ ν b)) = ν := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd.2 (fun b ↦ (G.blockCells_measurable b).2)]
    exact Measure.restrict_eq_self_of_ae_mem hc.2
  have hdp : Pairwise (fun b c : G.ClockSlabBlock μ ν ↦
      Disjoint (Prod.fst ⁻¹' G.sourceBlockCell μ ν b : Set (ℝ × ℝ)) (Prod.fst ⁻¹' G.sourceBlockCell μ ν c)) := by
    intro b c hbc
    exact (hd.1 hbc).preimage Prod.fst
  have hcp : ∀ᵐ p ∂γ, p ∈ ⋃ b : G.ClockSlabBlock μ ν, Prod.fst ⁻¹' G.sourceBlockCell μ ν b := by
    have hh : ∀ᵐ p ∂γ, p.1 ∈ ⋃ b : G.ClockSlabBlock μ ν, G.sourceBlockCell μ ν b :=
      ae_of_ae_map measurable_fst.aemeasurable (by rw [hγ.1]; exact hc.1)
    simpa only [mem_iUnion, mem_preimage] using hh
  have hsumP : (∑ b : G.ClockSlabBlock μ ν, γ.restrict (Prod.fst ⁻¹' G.sourceBlockCell μ ν b)) = γ := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdp
      (fun b ↦ measurable_fst (G.blockCells_measurable b).1)]
    exact Measure.restrict_eq_self_of_ae_mem hcp
  exact ⟨(Finset.sum_subset (Finset.subset_univ _) (fun b _ hb ↦ (G.zeroSlabBlock_restrict b hb).1)).trans hsumS,
    (Finset.sum_subset (Finset.subset_univ _) (fun b _ hb ↦ (G.zeroSlabBlock_restrict b hb).2)).trans hsumT,
    (Finset.sum_subset (Finset.subset_univ _) (fun b _ hb ↦ G.zeroSlabBlock_plan γ hγ b hb)).trans hsumP⟩

/-- Every retained positive block normalizes to a genuine probability coupling
of its two original restricted laws, using one shared actual mass. -/
theorem normalized_positiveBlock_coupling [IsFiniteMeasure μ] [IsFiniteMeasure ν] (b : G.ClockSlabBlock μ ν)
    (hb : b ∈ G.positiveSlabBlocks μ ν) :
    let w := μ (G.sourceBlockCell μ ν b)
    IsProbabilityMeasure (w⁻¹ • μ.restrict (G.sourceBlockCell μ ν b)) ∧
      IsProbabilityMeasure (w⁻¹ • ν.restrict (G.targetBlockCell μ ν b)) ∧
      Vlasov.IsCoupling (w⁻¹ • γ.restrict (Prod.fst ⁻¹' G.sourceBlockCell μ ν b))
        (w⁻¹ • μ.restrict (G.sourceBlockCell μ ν b)) (w⁻¹ • ν.restrict (G.targetBlockCell μ ν b)) := by
  let w := μ (G.sourceBlockCell μ ν b)
  have hm := G.positiveSlabBlock_mass b hb
  have hw : w ≠ 0 := by
    intro hz
    have hzreal : μ.real (G.sourceBlockCell μ ν b) = 0 := by
      change w.toReal = 0
      rw [hz, ENNReal.toReal_zero]
    exact hm.1.ne' hzreal
  have hwfin : w ≠ ∞ := measure_ne_top μ _
  have hbal : w = ν (G.targetBlockCell μ ν b) :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp hm.2
  have hcouple := G.block_restrict_coupling hδ hsep γ hγ hs ht hmono hweak b
  refine ⟨⟨?_⟩, ⟨?_⟩, ?_, ?_⟩
  · simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ] using ENNReal.inv_mul_cancel hw hwfin
  · simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, ← hbal] using ENNReal.inv_mul_cancel hw hwfin
  · rw [Measure.map_smul, hcouple.1]
  · rw [Measure.map_smul, hcouple.2]

/-- Each positive block has an internally generated positive normalized margin
at every proper original slab-prefix cut. No full-grid positivity is imposed. -/
theorem exists_normalized_positiveBlock_prefix_margin [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : G.ClockSlabBlock μ ν)
    (hb : b ∈ G.positiveSlabBlocks μ ν) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : Fin (G.count+1), b.lower < k → k < b.upper →
      η ≤ ((∑ i ∈ b.classes.filter (fun i ↦ i.val < k.val), μ.real (G.sourceCell i)) -
        (∑ i ∈ b.classes.filter (fun i ↦ i.val < k.val), ν.real (G.targetCell i))) /
          μ.real (G.sourceBlockCell μ ν b) := by
  obtain ⟨_, _, hH⟩ := G.clockSlabSurplus_facts hδ hsep γ hγ hs ht hmono hweak
  obtain ⟨η, hη, hmargin⟩ := b.exists_uniform_proper_prefix_pos hH
  have hw := (G.positiveSlabBlock_mass b hb).1
  refine ⟨η / μ.real (G.sourceBlockCell μ ν b), div_pos hη hw, ?_⟩
  intro k hlk hkr
  have heq := b.local_prefix_surplus (fun i ↦ μ.real (G.sourceCell i))
    (fun i ↦ ν.real (G.targetCell i)) hlk.le hkr.le
  exact (div_le_div_of_nonneg_right (hmargin k hlk hkr) hw.le).trans_eq
    (congrArg (fun x : ℝ ↦ x / μ.real (G.sourceBlockCell μ ν b)) heq.symm)

end ActualCoupling
end OTSelector.Reconstruction.OriginalStageClockGrid
