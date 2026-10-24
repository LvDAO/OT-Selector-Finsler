import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockFloorsPrefixMasses
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlockExtremes

/-! Fixed positive error tolerances and scalar floors come from the actual finite block laws. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Actual strict-block prefix margins and positive first/last class masses admit one
fixed positive tolerance and floor over all positive blocks. Empty block families are allowed. -/
theorem exists_positiveBlock_error_and_floor [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus μ ν k)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ e : ℝ, 0 < e ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ block : G.ClockSlabBlock μ ν,
      block ∈ G.positiveSlabBlocks μ ν →
      ρ ≤ θ*μ.real (G.sourceCell (G.firstBlockClass block))-3*e ∧
      ρ ≤ θ*ν.real (G.targetCell (G.lastBlockClass block))-3*e ∧
      ∀ k : Fin (G.count+1), block.lower < k → k < block.upper →
        ρ ≤ θ*G.clockSlabSurplus μ ν k.val-4*e := by
  classical
  let I := {block : G.ClockSlabBlock μ ν // block ∈ G.positiveSlabBlocks μ ν}
  have hm (i : I) : ∃ d : ℝ, 0 < d ∧
      d ≤ μ.real (G.sourceCell (G.firstBlockClass i.val)) ∧
      d ≤ ν.real (G.targetCell (G.lastBlockClass i.val)) ∧
      ∀ k : Fin (G.count+1), i.val.lower < k → k < i.val.upper → d ≤ G.clockSlabSurplus μ ν k.val := by
    obtain ⟨a,ha,hak⟩ := i.val.exists_uniform_proper_prefix_pos hH
    obtain ⟨hs,ht⟩ := G.positiveSlabBlock_extreme_class_masses hmono hH i.val i.property
    refine ⟨min a (min (μ.real (G.sourceCell (G.firstBlockClass i.val)))
      (ν.real (G.targetCell (G.lastBlockClass i.val)))),lt_min ha (lt_min hs ht),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _),?_⟩
    intro k hl hu
    exact (min_le_left _ _).trans (hak k hl hu)
  choose d hdpos hdS hdT hdK using hm
  have hex : ∃ η : ℝ, 0 < η ∧ ∀ i : I,
      η ≤ μ.real (G.sourceCell (G.firstBlockClass i.val)) ∧
      η ≤ ν.real (G.targetCell (G.lastBlockClass i.val)) ∧
      ∀ k : Fin (G.count+1), i.val.lower < k → k < i.val.upper → η ≤ G.clockSlabSurplus μ ν k.val := by
    by_cases hI : (Finset.univ : Finset I).Nonempty
    · let η := Finset.univ.inf' hI d
      have hη : 0 < η := (Finset.lt_inf'_iff hI).mpr (fun i _ ↦ hdpos i)
      refine ⟨η,hη,?_⟩
      intro i
      have hi : η ≤ d i := Finset.inf'_le _ (Finset.mem_univ i)
      exact ⟨hi.trans (hdS i),hi.trans (hdT i),fun k hl hu ↦ hi.trans (hdK i k hl hu)⟩
    · refine ⟨1,zero_lt_one,?_⟩
      intro i
      exact (hI ⟨i,Finset.mem_univ _⟩).elim
  obtain ⟨η,hη,hηall⟩ := hex
  refine ⟨θ*η/16,div_pos (mul_pos hθ hη) (by norm_num),
    θ*η/2,div_pos (mul_pos hθ hη) (by norm_num),?_⟩
  intro block hb
  obtain ⟨hs,ht,hk⟩ := hηall ⟨block,hb⟩
  refine ⟨?_,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hs hθ.le,mul_pos hθ hη]
  · nlinarith [mul_le_mul_of_nonneg_left ht hθ.le,mul_pos hθ hη]
  · intro k hl hu
    nlinarith [mul_le_mul_of_nonneg_left (hk k hl hu) hθ.le,mul_pos hθ hη]

end OTSelector.Reconstruction.OriginalStageClockGrid
