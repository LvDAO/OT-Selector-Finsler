import OTSelector.Reconstruction.OriginalStageClockSlabsWidth

/-! Original probability clock laws select their own positive extreme grid stages. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- An exact finite decomposition of a true probability law has an actual positive-mass
cell, including when the original grid contains empty stages. -/
theorem originalClockGrid_exists_positive_cell {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (cell : Fin n → Set ℝ) (hsum : (∑ i, μ.restrict (cell i)) = μ) :
    ∃ i, μ (cell i) ≠ 0 := by
  by_contra! hz
  have hzero : (∑ i, μ.restrict (cell i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact Measure.restrict_eq_zero.mpr (hz i)
  have hμzero : μ = 0 := hsum.symm.trans hzero
  have hmass := measure_univ (μ := μ)
  simp [hμzero] at hmass

/-- The unchanged original laws determine the first positive source stage and last
positive target stage before any scene, reserve positions or kept indices are observed.
These are the actual extreme deletion classes used by the finite count experiment. -/
theorem OriginalStageClockGrid.exists_positive_extreme_classes
    (G : OriginalStageClockGrid) (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hsource : (∑ i, μ.restrict (G.sourceCell i)) = μ)
    (htarget : (∑ i, ν.restrict (G.targetCell i)) = ν) :
    ∃ first last : Fin G.count,
      μ (G.sourceCell first) ≠ 0 ∧ ν (G.targetCell last) ≠ 0 ∧
      (∀ i, i < first → μ (G.sourceCell i) = 0) ∧
      (∀ i, last < i → ν (G.targetCell i) = 0) := by
  obtain ⟨is, hs⟩ := originalClockGrid_exists_positive_cell μ G.sourceCell hsource
  obtain ⟨it, ht⟩ := originalClockGrid_exists_positive_cell ν G.targetCell htarget
  let S := Finset.univ.filter (fun i ↦ μ (G.sourceCell i) ≠ 0)
  let T := Finset.univ.filter (fun i ↦ ν (G.targetCell i) ≠ 0)
  have hS : S.Nonempty := ⟨is, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
  have hT : T.Nonempty := ⟨it, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  refine ⟨S.min' hS, T.max' hT, (Finset.mem_filter.mp (S.min'_mem hS)).2,
    (Finset.mem_filter.mp (T.max'_mem hT)).2, ?_, ?_⟩
  · intro i hi
    by_contra hm
    have him : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    exact (not_le_of_gt hi) (S.min'_le _ him)
  · intro i hi
    by_contra hm
    have him : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    exact (not_le_of_gt hi) (T.le_max' _ him)

end OTSelector.Reconstruction
