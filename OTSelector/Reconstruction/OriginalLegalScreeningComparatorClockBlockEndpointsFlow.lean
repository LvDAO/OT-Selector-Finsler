import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocks

/-! Actual tight clock cuts have no crossing mass in the unchanged conditional coupling. -/
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid)

/-- A strict source prefix at an original threshold consists exactly of earlier source
Ico cells. In particular a source atom at the cut belongs to the right-hand cell. -/
theorem sourceCell_lt_cut_iff {i : Fin G.count} {x : ℝ} (hx : x ∈ G.sourceCell i) (k : ℕ) :
    x < G.cut k ↔ i.val < k := by
  constructor
  · intro h
    by_contra hn
    exact not_lt_of_ge ((G.strictMono.monotone (not_lt.mp hn)).trans hx.1) h
  · intro h
    exact hx.2.trans_le (G.strictMono.monotone (Nat.succ_le_of_lt h))

/-- A closed target prefix consists exactly of earlier target Ioc cells, retaining
all target atoms at the cut. No source endpoint convention is substituted. -/
theorem targetCell_le_cut_iff {j : Fin G.count} {y : ℝ} (hy : y ∈ G.targetCell j) (k : ℕ) :
    y ≤ G.cut k ↔ j.val < k := by
  constructor
  · intro h
    by_contra hn
    exact not_lt_of_ge ((G.strictMono.monotone (not_lt.mp hn)).trans' h) hy.1
  · intro h
    exact hy.2.trans (G.strictMono.monotone (Nat.succ_le_of_lt h))

/-- A genuine zero-surplus prefix kills all actual original coupling points that
strictly straddle its clock threshold. The actual flow and its tight crossing masses
are computed internally from the given coupling. -/
theorem ae_not_cross_tight_clockSlabCut
    {μ ν : Measure ℝ} {δ D : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ D)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hweak : ∀ᵐ p ∂π, p.1 ≤ p.2) (k : ℕ) (hk : k ≤ G.count)
    (hzero : G.clockSlabSurplus μ ν k = 0) :
    ∀ᵐ p ∂π, ¬ (p.1 < G.cut k ∧ G.cut k < p.2) := by
  classical
  obtain ⟨hrow,hcol⟩ := G.actualSlabFlow_marginals π hπ hs ht
  have hpairs (i j : Fin G.count) : ∀ᵐ p ∂π,
      p ∈ G.sourceCell i ×ˢ G.targetCell j → ¬ (p.1 < G.cut k ∧ G.cut k < p.2) := by
    by_cases hi : i.val < k
    · by_cases hj : k ≤ j.val
      · have hP := finiteClassFlow_zero_crossing_of_tight
          (actualClockClassFlow π G.sourceCell G.targetCell)
          (fun i ↦ μ.real (G.sourceCell i)) (fun j ↦ ν.real (G.targetCell j))
          (actualClockClassFlow_nonneg π G.sourceCell G.targetCell) hrow hcol
          (G.actualSlabFlow_zero hδ hsep π hπ hmono hweak) k hk hzero i j hi hj
        have hnull : π (G.sourceCell i ×ˢ G.targetCell j) = 0 :=
          (measureReal_eq_zero_iff (measure_ne_top π _)).mp hP
        exact (measure_eq_zero_iff_ae_notMem.mp hnull).mono (fun _ hn hp ↦ (hn hp).elim)
      · exact ae_of_all _ (fun p hp hcross ↦
          not_lt_of_ge ((G.targetCell_le_cut_iff hp.2 k).2 (by omega)) hcross.2)
    · exact ae_of_all _ (fun p hp hcross ↦ hi ((G.sourceCell_lt_cut_iff hp.1 k).1 hcross.1))
  have hall := ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (hpairs i))
  have hsc : ∀ᵐ p ∂π, p.1 ∈ ⋃ i, G.sourceCell i :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact hs)
  have htc : ∀ᵐ p ∂π, p.2 ∈ ⋃ j, G.targetCell j :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact ht)
  filter_upwards [hall,hsc,htc] with p hp hs' ht'
  obtain ⟨i,hi⟩ := mem_iUnion.mp hs'
  obtain ⟨j,hj⟩ := mem_iUnion.mp ht'
  exact hp i j ⟨hi,hj⟩

end OTSelector.Reconstruction.OriginalStageClockGrid
