import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyOptimal

/-!
# Expected orphan cardinality of the actual optimal common core

The count term in the explicit hierarchy repair budget is charged to the
original legal cardinality deficit and original common-sampling mismatches.
These counts are integrated on the unchanged observation law.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Measurable edge events give an integrable actual matching cardinality under
every finite original observation law. -/
theorem integrable_retained_card_of_edge_events
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (σ : Ω → OTSelector.PartialMatching m n)
    (hσ : ∀ e, MeasurableSet {ω | e ∈ (σ ω).edges}) :
    Integrable (fun ω ↦ ((σ ω).card : ℝ)) P := by
  apply Integrable.of_bound (measurable_retained_card σ hσ).aestronglyMeasurable (min m n : ℝ)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (σ ω).card_le

/-- The number of changed original observations is integrable, without any
independence requirement for either observation array. -/
theorem integrable_observed_diffCount
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableEq X]
    {N : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (a b : Fin N → Ω → X)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) :
    Integrable (fun ω ↦ diffCount N (fun i ↦ (a i ω, b i ω))) P := by
  have hm : Measurable (fun ω ↦ diffCount N (fun i ↦ (a i ω, b i ω))) :=
    (measurable_diffCount N).comp (measurable_pi_lambda _ fun i ↦ (ha i).prodMk (hb i))
  apply Integrable.of_bound hm.aestronglyMeasurable N
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (diffCount_nonneg_le N _).1]
  exact (diffCount_nonneg_le N _).2

/-- The actual adaptive core's expected number of unused rows is controlled by
the original legal matching deficit and original endpoint mismatch counts.
No law for selected unmatched partners is used. -/
theorem integral_firstLegalOptimalCommonCore_missing_le
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableEq S] [MeasurableEq T] {N : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (allowed : Ω → Finset (Fin N × Fin N))
    (hallowed : ∀ E, MeasurableSet {ω | allowed ω = E})
    (score : Ω → Fin N → Fin N → ℝ) (hscore : ∀ i j, Measurable (fun ω ↦ score ω i j))
    (sa sb : Fin N → Ω → S) (ta tb : Fin N → Ω → T)
    (hsa : ∀ i, Measurable (sa i)) (hsb : ∀ i, Measurable (sb i))
    (hta : ∀ j, Measurable (ta j)) (htb : ∀ j, Measurable (tb j)) :
    (∫ ω, (N : ℝ) - (firstLegalOptimalCommonCore allowed score sa sb ta tb ω).card ∂P) ≤
      (∫ ω, (N : ℝ) - PartialMatching.legalMaximumCard (allowed ω) ∂P) +
        (∫ ω, diffCount N (fun i ↦ (sa i ω, sb i ω)) ∂P) +
        ∫ ω, diffCount N (fun j ↦ (ta j ω, tb j ω)) ∂P := by
  have hcore := integrable_retained_card_of_edge_events P
    (firstLegalOptimalCommonCore allowed score sa sb ta tb)
    (measurableSet_mem_firstLegalOptimalCommonCore allowed hallowed score hscore
      sa sb ta tb hsa hsb hta htb)
  have hopt := integrable_retained_card_of_edge_events P
    (fun ω ↦ PartialMatching.firstLegalOptimalMatching (allowed ω) (score ω))
    (PartialMatching.measurableSet_mem_firstLegalOptimalMatching allowed hallowed score hscore)
  have hmax : Integrable (fun ω ↦ (PartialMatching.legalMaximumCard (allowed ω) : ℝ)) P := by
    convert hopt using 1
    funext ω
    exact congrArg Nat.cast
      (PartialMatching.firstLegalOptimalMatching_isLegalOptimal (allowed ω) (score ω)).2.1.symm
  have hds := integrable_observed_diffCount P sa sb hsa hsb
  have hdt := integrable_observed_diffCount P ta tb hta htb
  have hm := (integrable_const (N : ℝ)).sub hmax
  have hmono := integral_mono ((integrable_const (N : ℝ)).sub hcore) ((hm.add hds).add hdt)
    (firstLegalOptimalCommonCore_missing_le allowed score sa sb ta tb)
  have heq := integral_add (hm.add hds) hdt
  have heq' := integral_add hm hds
  simp only [Pi.add_apply, Pi.sub_apply] at hmono heq heq'
  rw [heq, heq'] at hmono
  exact hmono

end OTSelector.Reconstruction
