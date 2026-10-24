import OTSelector.Reconstruction.FiniteScalarBins
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Actual measurable finite scalar labels retain zero-mass and out-of-range cases. -/
open Set Function MeasureTheory
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- The genuine membership word in the original finite scalar partition. -/
def originalShapeHoleScalarCode {I : Set ℝ} {gap : ℝ} (bins : FiniteScalarBins I gap) (a : ℝ) :
    Fin bins.count → Bool := fun i ↦ decide (a ∈ bins.cell i)

theorem measurable_originalShapeHoleScalarCode {I : Set ℝ} {gap : ℝ} (bins : FiniteScalarBins I gap) :
    Measurable (originalShapeHoleScalarCode bins) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_countable'
  intro b
  cases b
  · convert (bins.measurable_cell i).compl using 1
    ext a
    simp [originalShapeHoleScalarCode]
  · convert bins.measurable_cell i using 1
    ext a
    simp [originalShapeHoleScalarCode]

/-- A finite label reads the original cell and reserves its final value for
out-of-range clocks. It remains meaningful when the scalar partition is empty. -/
def originalShapeHoleScalarLabel {I : Set ℝ} {gap : ℝ} (bins : FiniteScalarBins I gap) (a : ℝ) :
    Fin (bins.count+1) :=
  let word := originalShapeHoleScalarCode bins a
  if h : ∃ i, word i = true then ⟨(Classical.choose h).val,Nat.lt_succ_of_lt (Classical.choose h).isLt⟩
  else ⟨bins.count,Nat.lt_succ_self _⟩

theorem measurable_originalShapeHoleScalarLabel {I : Set ℝ} {gap : ℝ} (bins : FiniteScalarBins I gap) :
    Measurable (originalShapeHoleScalarLabel bins) := by
  let pick : (Fin bins.count → Bool) → Fin (bins.count+1) := fun word ↦
    if h : ∃ i, word i = true then ⟨(Classical.choose h).val,Nat.lt_succ_of_lt (Classical.choose h).isLt⟩
    else ⟨bins.count,Nat.lt_succ_self _⟩
  exact (measurable_of_countable pick).comp (measurable_originalShapeHoleScalarCode bins)

/-- The observed finite scalar label is exactly genuine original cell membership. -/
theorem originalShapeHoleScalarLabel_eq_iff {I : Set ℝ} {gap : ℝ} (bins : FiniteScalarBins I gap)
    (a : ℝ) (i : Fin bins.count) :
    originalShapeHoleScalarLabel bins a = i.castSucc ↔ a ∈ bins.cell i := by
  unfold originalShapeHoleScalarLabel
  dsimp only
  split_ifs with h
  · have hc : a ∈ bins.cell (Classical.choose h) := by
      simpa only [originalShapeHoleScalarCode,decide_eq_true_eq] using Classical.choose_spec h
    constructor
    · intro he
      have he' : Classical.choose h = i := Fin.ext (congrArg (fun k : Fin (bins.count+1) ↦ k.val) he)
      simpa only [he'] using hc
    · intro ha
      have he : Classical.choose h = i := by
        by_contra hn
        exact Set.disjoint_left.mp (bins.disjoint hn) hc ha
      exact Fin.ext (congrArg (fun k : Fin bins.count ↦ k.val) he)
  · constructor
    · intro he
      have hh := congrArg Fin.val he
      have hi := i.isLt
      dsimp only [Fin.val_castSucc] at hh
      omega
    · intro ha
      exact False.elim (h ⟨i,by simpa only [originalShapeHoleScalarCode,decide_eq_true_eq] using ha⟩)

/-- One actual forward pair and equality of its target-bin labels make the
unchanged cross pair strictly legal. No realized type count is balanced. -/
theorem originalShapeHole_forward_of_same_target_label {I : Set ℝ} {gap : ℝ}
    (bins : FiniteScalarBins I gap) (hgap : 0 < gap) {a b d : ℝ}
    (hb : b ∈ I) (hforward : gap ≤ b-a)
    (heq : originalShapeHoleScalarLabel bins b = originalShapeHoleScalarLabel bins d) : a < d := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp (bins.union_eq.symm ▸ hb)
  have hbi := (originalShapeHoleScalarLabel_eq_iff bins b i).mpr hi
  have hdi := (originalShapeHoleScalarLabel_eq_iff bins d i).mp (heq.symm.trans hbi)
  have hclose := (abs_le.mp (bins.diameter i d hdi b hi)).1
  linarith

end OTSelector.Reconstruction
