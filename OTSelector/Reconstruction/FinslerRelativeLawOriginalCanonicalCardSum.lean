import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellOptimizer
import OTSelector.Reconstruction.FinslerRelativeLawGlobalMatchingSplice
import OTSelector.Reconstruction.FinslerRelativeLawRetainedCellLabels

/-! The same original retained canonical cells spend at most the original number of rows. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Disjoint original physical cells bound the sum of their canonical matching
cardinalities on every sample, before taking expectations. -/
theorem sum_card_originalRetainedCellOptimizer_le
    {X Z C T : Type*} [Fintype C] [DecidableEq C] {N : ℕ}
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Finset (Fin N × Fin N))
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    (∑ c, (originalRetainedCellOptimizer a cell extra model c sample).card) ≤ N := by
  classical
  let source := fun j ↦ originalRetainedCellTag a cell (∅ : Finset (Option (Bool × T))) (sample.1 j)
  let target := fun k ↦ originalRetainedCellTag a cell (∅ : Finset (Option (Bool × T))) (sample.2 k)
  let pieces : Option C → OTSelector.PartialMatching N N
    | none => PartialMatching.empty
    | some c => originalRetainedCellOptimizer a cell extra model c sample
  have hpieces : ∀ c e, e ∈ (pieces c).edges → source e.1 = c ∧ target e.2 = c := by
    intro c e he
    cases c with
    | none => simp [pieces, PartialMatching.empty] at he
    | some c =>
      have hs := originalRetainedCellOptimizer_support a cell extra model c sample e he
      exact ⟨(originalRetainedCellTag_eq_some_iff a cell hdisj ∅ (sample.1 e.1) c).mpr
          ⟨(by simp), hs.2.2.2.1⟩,
        (originalRetainedCellTag_eq_some_iff a cell hdisj ∅ (sample.2 e.2) c).mpr
          ⟨(by simp), hs.2.2.2.2⟩⟩
  let union := populationCellMatchingUnion source target pieces hpieces
  have hcard : union.card = ∑ c, (originalRetainedCellOptimizer a cell extra model c sample).card := by
    rw [show union.card = ∑ c, (pieces c).card from card_populationCellMatchingUnion _ _ _ _]
    simp only [Fintype.sum_option, pieces, OTSelector.PartialMatching.card,
      PartialMatching.empty, Finset.card_empty, zero_add]
  rw [← hcard]
  simpa only [min_self] using union.card_le

/-- Expected matched-cardinality errors over disjoint original canonical
cells spend at most one original sample mass. -/
theorem integral_sum_card_originalRetainedCellOptimizer_le
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace (Option (Bool × T))]
    [Fintype C] [DecidableEq C] {N : ℕ}
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Finset (Fin N × Fin N))
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ)
    (law : Measure ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))))
    [IsProbabilityMeasure law]
    (hI : ∀ c, Integrable (fun sample ↦ ((originalRetainedCellOptimizer a cell extra model c sample).card : ℝ)) law) :
    (∑ c, ∫ sample, ((originalRetainedCellOptimizer a cell extra model c sample).card : ℝ) ∂law) ≤ N := by
  have hsum := integrable_finsetSum Finset.univ (fun c _ ↦ hI c)
  have hbound : ∀ᵐ sample ∂law,
      (∑ c, ((originalRetainedCellOptimizer a cell extra model c sample).card : ℝ)) ≤ (N : ℝ) := by
    apply Filter.Eventually.of_forall
    intro sample
    exact_mod_cast sum_card_originalRetainedCellOptimizer_le a cell hdisj extra model sample
  have h := integral_mono_ae hsum (integrable_const (N : ℝ)) hbound
  rw [integral_finsetSum Finset.univ (fun c _ ↦ hI c)] at h
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using h

/-- Different nonnegative cell probe errors bounded by one prescribed tolerance
still pay only that tolerance times the original number of samples. -/
theorem weighted_integral_card_originalRetainedCellOptimizer_le
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace (Option (Bool × T))]
    [Fintype C] [DecidableEq C] {N : ℕ}
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Finset (Fin N × Fin N))
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ)
    (law : Measure ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))))
    [IsProbabilityMeasure law]
    (hI : ∀ c, Integrable (fun sample ↦ ((originalRetainedCellOptimizer a cell extra model c sample).card : ℝ)) law)
    (error : C → ℝ) {bound : ℝ} (hbound : 0 ≤ bound) (herror : ∀ c, error c ≤ bound) :
    (∑ c, (∫ sample, ((originalRetainedCellOptimizer a cell extra model c sample).card : ℝ) ∂law) * error c) ≤
      (N : ℝ) * bound := by
  calc
    _ ≤ ∑ c, (∫ sample, ((originalRetainedCellOptimizer a cell extra model c sample).card : ℝ) ∂law) * bound := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (herror c) (integral_nonneg fun sample ↦ Nat.cast_nonneg _)
    _ = (∑ c, ∫ sample, ((originalRetainedCellOptimizer a cell extra model c sample).card : ℝ) ∂law) * bound :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (N : ℝ) * bound := mul_le_mul_of_nonneg_right
      (integral_sum_card_originalRetainedCellOptimizer_le a cell hdisj extra model law hI) hbound

end OTSelector.Reconstruction
