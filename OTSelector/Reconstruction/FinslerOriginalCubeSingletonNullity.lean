import OTSelector.Reconstruction.FinslerOriginalProductDiagonalNullity

/-!
# Cube singleton nullity and unconditional a.e. distinctness of cloud marks

This module wires the last atomlessness input of
FinslerOriginalProductDiagonalNullity: singleton nullity of the cube Haar measure
cubeMeasure q 1 (for q >= 1) and of the single marked point law
(cubeMeasure q 1).prod alpha.

1. **uniformInterval_singleton_null**: the uniform interval law has null
   singletons (it is a scalar multiple of volume restricted to an interval, and
   volume singletons are null).
2. **cubeMeasure_singleton_null**: cubeMeasure (Fin q) 1 has null singletons for
   q >= 1, via the coordinate projection and Mathlib's pi_eval_preimage_null
   (a singleton is contained in the preimage of a null singleton under one
   coordinate evaluation).
3. **markedPointLaw_singleton_null**: the single marked point law
   (cubeMeasure (Fin q) 1).prod alpha has null singletons (product of a null
   singleton with any singleton, by Measure.prod_prod).
4. **markedSeqLaw_ae_marks_ne_unconditional**: consequently two distinct marked
   cloud points are a.e. different under markedSeqLaw q R alpha, with NO
   remaining atomlessness hypothesis.
5. **ae_prod_snd / ae_prod_fst**: a.e. properties transport from a factor to the
   product (needed to pass from the sequence law to the cloud law).
6. **twoMarkedCloudLaw_ae_source_marks_ne / twoMarkedCloudLaw_ae_target_marks_ne**:
   a.e. pairwise distinctness of source and target marked cloud points under
   twoMarkedCloudLaw, unconditionally.

## Exact remaining gap for CanonicalScenePlanSimplicity

The canonical scene configuration is indexed by the MATCHED INDEX PAIRS of
firstLegalMarkedOptimalMatching, not by all cloud indices.  The a.e. distinctness
proved here is at the level of cloud index pairs; to obtain
CanonicalScenePlanSimplicity one still needs the matching's source/target index
injectivity (distinct matched pairs have distinct source and target indices), and
the resulting index injection inserted into the a.e. distinctness statement for
the matched set.  That index-level injectivity is a field of the PartialMatching
lane and is not wired here; the marginal identity hm for canonicalInputMeasure is
separate (measure algebra).  No a.e. atomlessness hypothesis remains anywhere.
No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **The uniform interval law has null singletons.** -/
theorem uniformInterval_singleton_null (L x : ℝ) :
    uniformInterval L {x} = 0 := by
  unfold uniformInterval
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
  rw [measure_mono_null (Set.inter_subset_left) (by simp)]
  simp

/-- The uniform interval law is a finite measure. -/
instance uniformInterval_isFiniteMeasure (L : ℝ) : IsFiniteMeasure (uniformInterval L) where
  measure_univ_lt_top := by
    unfold uniformInterval
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    rw [smul_eq_mul]
    rcases eq_or_ne (volume (Set.Ioo (0 : ℝ) L)) 0 with h0 | h0
    · rw [h0, ENNReal.inv_zero]
      simp
    · rw [ENNReal.inv_mul_cancel h0]
      · exact ENNReal.one_lt_top
      · rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top

/-- The uniform interval law is sigma-finite. -/
instance uniformInterval_sigmaFinite (L : ℝ) : SigmaFinite (uniformInterval L) := by
  haveI := uniformInterval_isFiniteMeasure L
  infer_instance

/-- **The cube Haar measure has null singletons** for a nonempty index type, via
the coordinate projection and the nullity of a singleton in one factor. -/
theorem cubeMeasure_singleton_null {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ) (x : ι → ℝ) :
    cubeMeasure ι L {x} = 0 := by
  change Measure.pi (fun _ : ι => uniformInterval L) {x} = 0
  rw [Measure.pi_singleton]
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact Finset.prod_eq_zero (Finset.mem_univ i) (uniformInterval_singleton_null L (x i))

/-- **The single marked point law has null singletons.** -/
theorem markedPointLaw_singleton_null {q : ℕ} (hq : 0 < q)
    {A : Type*} [MeasurableSpace A] (α : Measure A) [IsProbabilityMeasure α]
    (p : (Fin q → ℝ) × A) :
    ((cubeMeasure (Fin q) 1).prod α) {p} = 0 := by
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  haveI : SFinite α := inferInstance
  have hset : ({p} : Set ((Fin q → ℝ) × A)) = {p.1} ×ˢ {p.2} := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_prod]
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1 h2
  rw [hset, Measure.prod_prod, cubeMeasure_singleton_null 1 p.1]
  simp

/-- **Two distinct marked cloud points are a.e. different**, unconditionally for
q >= 1 (the atomlessness input is closed here). -/
theorem markedSeqLaw_ae_marks_ne_unconditional {q : ℕ} (hq : 0 < q)
    (α : Measure ℝ) [IsProbabilityMeasure α] {i j : ℕ} (hij : i ≠ j) :
    ∀ᵐ seq ∂markedSeqLaw (q := q) ℝ α, seq i ≠ seq j :=
  markedSeqLaw_ae_marks_ne (q := q) α (fun p => markedPointLaw_singleton_null hq α p) hij

/-- **A.e. properties transport from the second factor of a product.** -/
theorem ae_prod_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {P : β → Prop}
    (h : ∀ᵐ y ∂ν, P y) :
    ∀ᵐ p ∂μ.prod ν, P p.2 := by
  rw [MeasureTheory.ae_iff] at h ⊢
  have hset : {p : α × β | ¬ P p.2} = Set.univ ×ˢ {y : β | ¬ P y} := by
    ext p
    simp
  rw [hset, Measure.prod_prod, h]
  simp

/-- **A.e. properties transport from the first factor of a product.** -/
theorem ae_prod_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {P : α → Prop}
    (h : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ p ∂μ.prod ν, P p.1 := by
  rw [MeasureTheory.ae_iff] at h ⊢
  have hset : {p : α × β | ¬ P p.1} = {x : α | ¬ P x} ×ˢ Set.univ := by
    ext p
    simp
  rw [hset, Measure.prod_prod, h]
  simp

/-- **A.e. distinctness of source marked cloud points** under the two-cloud law,
unconditionally for q >= 1. -/
theorem twoMarkedCloudLaw_ae_source_marks_ne {q : ℕ} (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    {i j : ℕ} (hij : i ≠ j) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ, ω.1.2 i ≠ ω.1.2 j := by
  have hseq : ∀ᵐ seq ∂markedSeqLaw (q := q) ℝ α, seq i ≠ seq j :=
    markedSeqLaw_ae_marks_ne_unconditional hq α hij
  haveI : IsProbabilityMeasure (markedPoissonLaw (q := q) ℝ α ρ) := inferInstance
  have hpois : ∀ᵐ cl ∂markedPoissonLaw (q := q) ℝ α ρ, cl.2 i ≠ cl.2 j :=
    ae_prod_snd hseq
  simpa [twoMarkedCloudLaw] using ae_prod_fst hpois

/-- **A.e. distinctness of target marked cloud points** under the two-cloud law,
unconditionally for q >= 1. -/
theorem twoMarkedCloudLaw_ae_target_marks_ne {q : ℕ} (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0)
    {i j : ℕ} (hij : i ≠ j) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ, ω.2.2 i ≠ ω.2.2 j := by
  have hseq : ∀ᵐ seq ∂markedSeqLaw (q := q) ℝ β, seq i ≠ seq j :=
    markedSeqLaw_ae_marks_ne_unconditional hq β hij
  haveI : IsProbabilityMeasure (markedPoissonLaw (q := q) ℝ β ρ) := inferInstance
  have hpois : ∀ᵐ cl ∂markedPoissonLaw (q := q) ℝ β ρ, cl.2 i ≠ cl.2 j :=
    ae_prod_snd hseq
  simpa [twoMarkedCloudLaw] using ae_prod_snd hpois

end OTSelector.Reconstruction
