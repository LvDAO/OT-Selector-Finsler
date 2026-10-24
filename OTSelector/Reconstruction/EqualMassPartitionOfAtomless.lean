import OTSelector.Reconstruction.FinslerOriginalEqualMassPartition
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue

/-!
# Equal-mass partitions from an atomless real clock

A measurable real clock with atomless pushforward constructs an equal-mass partition
of the original probability measure into any positive finite number of cells. The
cells are inverse images of consecutive intervals between CDF quantiles; no global
cube coordinate map or measure-space isomorphism is an input.

The final constructor supplies the mass fields of the physical block partition.
Per-block cube coordinates and the kinetic approximation remain separate data.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ENNReal BigOperators

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000

/-- An atomless real probability law has a continuous cumulative distribution function. -/
theorem continuous_cdf_of_nullSingletons (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hjump : ENNReal.ofReal (cdf μ x - leftLim (cdf μ) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf]
    exact measure_singleton x
  have hle : cdf μ x - leftLim (cdf μ) x ≤ 0 := ENNReal.ofReal_eq_zero.mp hjump
  have hleft : leftLim (cdf μ) x = cdf μ x :=
    le_antisymm ((cdf μ).mono.leftLim_le le_rfl) (by linarith)
  exact ((cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim).mpr
    (hleft.trans ((cdf μ).right_continuous x).rightLim_eq.symm)

/-- Every probability strictly between zero and one is attained by an atomless CDF. -/
theorem exists_cdf_eq_of_nullSingletons (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ x : ℝ, cdf μ x = p := by
  have hcont := continuous_cdf_of_nullSingletons μ
  have h := isPreconnected_univ.intermediate_value_Ioo
    (l₁ := (atBot : Filter ℝ)) (l₂ := (atTop : Filter ℝ))
    (by simp) (by simp) hcont.continuousOn (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ)
      ⟨hp0, hp1⟩
  obtain ⟨x, _, hx⟩ := h
  exact ⟨x, hx⟩

/-- Nested measurable cuts with equal successive mass increments give measurable cells. -/
def equalMassPartition_of_cuts {M : Type*} [MeasurableSpace M]
    (μ : Measure M) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0 < N)
    (cut : ℕ → Set M) (hcut : ∀ i, MeasurableSet (cut i))
    (hmono : Monotone cut) (hzero : cut 0 = ∅) (hfull : cut N = univ)
    (hmass : ∀ i, i ≤ N → μ (cut i) = ENNReal.ofReal ((i : ℝ) / N)) :
    EqualMassPartition μ (Fin N) (fun _ ↦ 1 / (N : ℝ)) := by
  classical
  have hex : ∀ x : M, ∃ i : Fin N, x ∈ cut (i.val + 1) := by
    intro x
    refine ⟨⟨N - 1, by omega⟩, ?_⟩
    simp [Nat.sub_add_cancel hN, hfull]
  let cell : M → Fin N := fun x ↦ Fin.find (fun i : Fin N ↦ x ∈ cut (i.val + 1)) (hex x)
  have hfiber : ∀ i : Fin N, cell ⁻¹' {i} = cut (i.val + 1) \ cut i.val := by
    intro i
    ext x
    change (cell x = i) ↔ x ∈ cut (i.val + 1) ∧ x ∉ cut i.val
    constructor
    · intro hx
      have hspec : x ∈ cut ((cell x).val + 1) := Fin.find_spec (hex x)
      refine ⟨hx ▸ hspec, ?_⟩
      intro hprev
      by_cases hi : i.val = 0
      · simp [hi, hzero] at hprev
      · have himin : cell x ≤ (⟨i.val - 1, by omega⟩ : Fin N) :=
          Fin.find_le_of_pos (hex x) (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
            using hprev)
        have hnat := Fin.le_iff_val_le_val.mp himin
        simp only [hx] at hnat
        omega
    · rintro ⟨hx, hprev⟩
      have hle : cell x ≤ i := Fin.find_le_of_pos (hex x) hx
      apply le_antisymm hle
      by_contra hnot
      have hlt : (cell x).val < i.val := by
        change ¬ i.val ≤ (cell x).val at hnot
        omega
      exact hprev ((hmono (by omega : (cell x).val + 1 ≤ i.val))
        (Fin.find_spec (hex x)))
  refine ⟨cell, ?_, ?_⟩
  · intro s _
    have hs : cell ⁻¹' s = ⋃ i ∈ s, cell ⁻¹' {i} := by ext x; simp
    rw [hs]
    exact MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦
      (hfiber i ▸ (hcut (i.val + 1)).diff (hcut i.val))
  · intro i
    rw [hfiber i, measure_sdiff (hmono (Nat.le_succ i.val))
      (hcut i.val).nullMeasurableSet (measure_ne_top _ _),
      hmass (i.val + 1) (by omega), hmass i.val (by omega),
      ← ENNReal.ofReal_sub _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    congr 1
    push_cast
    ring

/-- An atomless real clock constructs an equal-mass partition with `N` cells. -/
def equalMassPartitionFin_of_atomlessClock {M : Type*} [MeasurableSpace M]
    (μ : Measure M) [IsProbabilityMeasure μ] (u : M → ℝ) (hu : Measurable u)
    [NullSingletonClass (μ.map u)] (N : ℕ) (hN : 0 < N) :
    EqualMassPartition μ (Fin N) (fun _ ↦ 1 / (N : ℝ)) := by
  classical
  have : IsProbabilityMeasure (μ.map u) := Measure.isProbabilityMeasure_map hu.aemeasurable
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hquant : ∀ i : ℕ, 0 < i → i < N → ∃ x : ℝ, cdf (μ.map u) x = (i : ℝ) / N := by
    intro i hi hiN
    apply exists_cdf_eq_of_nullSingletons (μ.map u)
    · exact div_pos (by exact_mod_cast hi) hNR
    · exact (div_lt_one hNR).mpr (by exact_mod_cast hiN)
  let Q : ℕ → ℝ := fun i ↦ if hi : 0 < i ∧ i < N then (hquant i hi.1 hi.2).choose else 0
  have hQ : ∀ i : ℕ, 0 < i → i < N → cdf (μ.map u) (Q i) = (i : ℝ) / N := by
    intro i hi hiN
    simpa only [Q, dite_eq_left (show 0 < i ∧ i < N from ⟨hi, hiN⟩)] using
      (hquant i hi hiN).choose_spec
  have hQmono : ∀ i j : ℕ, 0 < i → j < N → i < j → Q i < Q j := by
    intro i j hi hj hij
    by_contra hnot
    have hle := (monotone_cdf (μ.map u)) (le_of_not_gt hnot)
    rw [hQ i hi (lt_trans hij hj), hQ j (lt_trans hi hij) hj] at hle
    have hratio : (i : ℝ) / N < (j : ℝ) / N :=
      div_lt_div_of_pos_right (by exact_mod_cast hij) hNR
    exact (not_le_of_gt hratio) hle
  let cut : ℕ → Set M := fun i ↦ if i = 0 then ∅ else if N ≤ i then univ
    else u ⁻¹' Iic (Q i)
  have hcut : ∀ i, MeasurableSet (cut i) := by
    intro i
    dsimp [cut]
    split_ifs
    · exact MeasurableSet.empty
    · exact MeasurableSet.univ
    · exact hu measurableSet_Iic
  have hmono : Monotone cut := by
    intro i j hij
    by_cases hi : i = 0
    · simp [cut, hi]
    by_cases hj : N ≤ j
    · simp [cut, hj, ne_of_gt (lt_of_lt_of_le hN hj)]
    have hni : ¬ N ≤ i := by omega
    have hj0 : j ≠ 0 := by omega
    simp only [cut, ite_eq_right hi, ite_eq_right hj0, ite_eq_right hj, ite_eq_right hni]
    apply preimage_mono
    apply Iic_subset_Iic.mpr
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact (hQmono i j (by omega) (by omega) hij).le
  refine equalMassPartition_of_cuts μ N hN cut hcut hmono (by simp [cut])
    (by simp [cut, Nat.ne_of_gt hN]) ?_
  intro i hiN
  by_cases hi0 : i = 0
  · simp [cut, hi0]
  by_cases hiN' : N ≤ i
  · have hi : i = N := by omega
    subst i
    simp [cut, ne_of_gt hN, ne_of_gt hNR]
  · rw [show cut i = u ⁻¹' Iic (Q i) from by simp [cut, hi0, hiN'],
      ← Measure.map_apply hu measurableSet_Iic, ← ofReal_cdf, hQ i (by omega) (by omega)]

/-- Any nonempty finite index set receives equal-mass cells from an atomless clock. -/
def equalMassPartition_of_atomlessClock {M ι : Type*} [MeasurableSpace M]
    [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    (μ : Measure M) [IsProbabilityMeasure μ] (u : M → ℝ) (hu : Measurable u)
    [NullSingletonClass (μ.map u)] :
    EqualMassPartition μ ι (fun _ ↦ 1 / (Fintype.card ι : ℝ)) := by
  classical
  let D := equalMassPartitionFin_of_atomlessClock μ u hu (Fintype.card ι)
    Fintype.card_pos
  let e := Fintype.equivFin ι
  refine ⟨e.symm ∘ D.cell, (measurable_of_finite e.symm).comp D.hcell, ?_⟩
  intro i
  have hfiber : (e.symm ∘ D.cell) ⁻¹' {i} = D.cell ⁻¹' {e i} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, comp_apply, Equiv.symm_apply_eq]
  rw [hfiber]
  exact D.hmass (e i)

/-- The physical source and target clocks construct the block partition's exact mass laws. -/
def cellMassPartition_of_atomlessClock {M : Type*} [MeasurableSpace M]
    (q k : ℕ) (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (u : M → ℝ) (hu : Measurable u)
    (hμatom : NullSingletonClass ((physicalSourceProbability ωM ρ₀ : Measure M).map u))
    (hνatom : NullSingletonClass ((physicalTargetProbability ωM ρ₁ : Measure M).map u)) :
    CellMassPartition (M := M) q k ωM ρ₀ ρ₁ := by
  let Dμ := equalMassPartition_of_atomlessClock
    (ι := Fin q → Fin (2 ^ k + 1)) (physicalSourceProbability ωM ρ₀ : Measure M) u hu
  let Dν := equalMassPartition_of_atomlessClock
    (ι := Fin q → Fin (2 ^ k + 1)) (physicalTargetProbability ωM ρ₁ : Measure M) u hu
  refine cellMassPartition_of_equalMass q k ωM ρ₀ ρ₁
    (fun _ ↦ 1 / (Fintype.card (Fin q → Fin (2 ^ k + 1)) : ℝ)) ?_ Dμ Dν
  intro c
  simp [blockW, unitBlock]

end OTSelector.Reconstruction
