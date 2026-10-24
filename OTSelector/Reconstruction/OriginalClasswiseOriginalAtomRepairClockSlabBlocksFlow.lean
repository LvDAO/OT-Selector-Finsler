import OTSelector.Reconstruction.OriginalStageClockSlabs
import OTSelector.Reconstruction.OriginalFiniteOrderedStrictBlocksMass

/-! The actual distinct half-open clock slabs produce their genuine finite forward flow. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction.OriginalStageClockGrid
variable (G : OriginalStageClockGrid) {μ ν : Measure ℝ}

/-- Surplus uses the actual source Ico and target Ioc masses on the same grid. -/
def clockSlabSurplus (μ ν : Measure ℝ) : ℕ → ℝ :=
  finiteClassSurplus (fun i ↦ μ.real (G.sourceCell i)) (fun i ↦ ν.real (G.targetCell i))

/-- Blocks retain every tight cut, including cuts adjacent to empty true slabs. -/
abbrev ClockSlabBlock (μ ν : Measure ℝ) := FiniteSurplusStrictBlock (G.clockSlabSurplus μ ν) G.count

/-- The true rectangular masses have exactly the two original half-open marginals. -/
theorem actualSlabFlow_marginals (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ]
    (hγ : Vlasov.IsCoupling γ μ ν)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j) :
    (∀ i, ∑ j, actualClockClassFlow γ G.sourceCell G.targetCell i j = μ.real (G.sourceCell i)) ∧
      (∀ j, ∑ i, actualClockClassFlow γ G.sourceCell G.targetCell i j = ν.real (G.targetCell j)) := by
  have hsc : ∀ᵐ p ∂γ, p.1 ∈ ⋃ i, G.sourceCell i :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hγ.1]; exact hs)
  have htc : ∀ᵐ p ∂γ, p.2 ∈ ⋃ j, G.targetCell j :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hγ.2]; exact ht)
  exact ⟨fun i ↦ by rw [actualClockClassFlow_row γ G.sourceCell G.targetCell
      (fun _ ↦ measurableSet_Ico) (fun _ ↦ measurableSet_Ioc) G.target_disjoint htc, hγ.1],
    fun j ↦ by rw [actualClockClassFlow_col γ G.sourceCell G.targetCell
      (fun _ ↦ measurableSet_Ico) (fun _ ↦ measurableSet_Ioc) G.source_disjoint hsc, hγ.2]⟩

/-- Real support separation rules out threshold equality before the weak-forward
coupling is reduced to a strict-forward slab matrix. Empty classes remain allowed. -/
theorem actualSlabFlow_zero {δ D : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ D)
    (γ : Measure (ℝ × ℝ)) (hγ : Vlasov.IsCoupling γ μ ν)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hweak : ∀ᵐ p ∂γ, p.1 ≤ p.2) (i j : Fin G.count) (hij : ¬ i < j) :
    actualClockClassFlow γ G.sourceCell G.targetCell i j = 0 := by
  have hnull : γ (G.sourceCell i ×ˢ G.targetCell j) = 0 := by
    by_cases heq : i = j
    · subst j
      rcases hmono i with hi | hi
      · have hs : γ (Prod.fst ⁻¹' G.sourceCell i) = 0 := by
          rw [← Measure.map_apply measurable_fst
            (show MeasurableSet (G.sourceCell i) from measurableSet_Ico), hγ.1, hi]
        exact measure_mono_null (fun _ hp ↦ hp.1) hs
      · have ht : γ (Prod.snd ⁻¹' G.targetCell i) = 0 := by
          rw [← Measure.map_apply measurable_snd
            (show MeasurableSet (G.targetCell i) from measurableSet_Ioc), hγ.2, hi]
        exact measure_mono_null (fun _ hp ↦ hp.2) ht
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq)
      have hstrict := hsep.ae_strict_order_of_coupling hδ hγ hweak
      apply measure_mono_null (fun p hp ↦ ?_) (ae_iff.mp hstrict)
      intro hlt
      have horder : p.2 ≤ p.1 := hp.2.2.trans
        ((G.strictMono.monotone (Nat.succ_le_of_lt hji)).trans hp.1.1)
      exact not_lt_of_ge horder hlt
  simp only [actualClockClassFlow, measureReal_def, hnull, ENNReal.toReal_zero]

/-- Genuine actual flow constructs nonnegative surplus and both zero endpoints. -/
theorem clockSlabSurplus_facts {δ D : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ D)
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ] (hγ : Vlasov.IsCoupling γ μ ν)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (hweak : ∀ᵐ p ∂γ, p.1 ≤ p.2) :
    G.clockSlabSurplus μ ν 0 = 0 ∧ G.clockSlabSurplus μ ν G.count = 0 ∧
      ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus μ ν k := by
  obtain ⟨hrow, hcol⟩ := G.actualSlabFlow_marginals γ hγ hs ht
  let P := actualClockClassFlow γ G.sourceCell G.targetCell
  let a := fun i ↦ μ.real (G.sourceCell i)
  let b := fun i ↦ ν.real (G.targetCell i)
  have hz := G.actualSlabFlow_zero hδ hsep γ hγ hmono hweak
  have hend := finiteClassFlow_surplus_endpoints P a b hrow hcol
  exact ⟨hend.1, hend.2, fun k hk ↦ finiteClassFlow_surplus_nonneg P a b
    (actualClockClassFlow_nonneg γ G.sourceCell G.targetCell) hrow hcol hz k hk⟩

end OTSelector.Reconstruction.OriginalStageClockGrid
