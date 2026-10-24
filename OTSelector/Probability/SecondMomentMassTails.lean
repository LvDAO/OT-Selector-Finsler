import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
## Lemma skeleton

* **Conditions:** A common second-moment bound and a positive cutoff.
* **Objects:** Tail mass, tail expectation and a uniform cutoff across varying spaces.
* **Proof detail:** Use the pointwise cutoff inequality and Markov; choose one cutoff from the common bound.

## Mathematical sources

* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37

**Relationship to the sources:** The varying-space uniform cutoff is an elementary consequence, not an extra iid theorem.
-/

/-!
# Quantitative local mass tails from second moments

These estimates apply directly to the original probability spaces at different
sample sizes. A common second-moment bound gives uniform integrability through
a common cutoff and also gives a quantitative probability tail.
-/

open MeasureTheory Set

namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}

/-- The expected mass above R is at most its second moment divided by R. -/
theorem setIntegral_mass_tail_le_of_second_moment
    (hm : Measurable f) (hi : Integrable f P)
    (hsq : Integrable (fun sample ↦ (f sample) ^ 2) P)
    (hnonneg : ∀ᵐ sample ∂P, 0 ≤ f sample)
    {C : ℝ} (hsecond : (∫ sample, (f sample) ^ 2 ∂P) ≤ C)
    {R : ℝ} (hR : 0 < R) :
    (∫ sample in {sample | R ≤ f sample}, f sample ∂P) ≤ C / R := by
  have hset : MeasurableSet {sample | R ≤ f sample} := measurableSet_le measurable_const hm
  have hpoint : ∀ᵐ sample ∂P,
      R * ({sample | R ≤ f sample}.indicator f sample) ≤ (f sample) ^ 2 := by
    filter_upwards [hnonneg] with sample hs
    by_cases hmem : sample ∈ {sample | R ≤ f sample}
    · rw [Set.indicator_of_mem hmem]
      have hRf : R ≤ f sample := hmem
      nlinarith
    · rw [Set.indicator_of_notMem hmem, mul_zero]
      exact sq_nonneg _
  have h := integral_mono_ae ((hi.indicator hset).const_mul R) hsq hpoint
  rw [integral_const_mul, integral_indicator hset] at h
  apply (le_div_iff₀ hR).mpr
  simpa only [mul_comm] using h.trans hsecond

/-- The local mass exceeds R with probability at most C/R². -/
theorem probability_mass_tail_le_of_second_moment [IsFiniteMeasure P]
    (hsq : Integrable (fun sample ↦ (f sample) ^ 2) P)
    {C : ℝ} (hsecond : (∫ sample, (f sample) ^ 2 ∂P) ≤ C)
    {R : ℝ} (hR : 0 < R) : P.real {sample | R ≤ f sample} ≤ C / R ^ 2 := by
  have hsub : {sample | R ≤ f sample} ⊆ {sample | R ^ 2 ≤ (f sample) ^ 2} := by
    intro sample hs
    change R ≤ f sample at hs
    change R ^ 2 ≤ (f sample) ^ 2
    nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun sample ↦ sq_nonneg (f sample))) hsq (R ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := P) hsub) (sq_nonneg R)
  simpa only [mul_comm] using hmono.trans (hmark.trans hsecond)

/-- One cutoff works for an entire family, even when the underlying original
probability spaces depend on the index. -/
theorem exists_uniform_mass_tail_cutoff {I : Type*} {Ω : I → Type*}
    [∀ i, MeasurableSpace (Ω i)] (P : ∀ i, Measure (Ω i)) (f : ∀ i, Ω i → ℝ)
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) (P i))
    (hsq : ∀ i, Integrable (fun sample ↦ (f i sample) ^ 2) (P i))
    (hnonneg : ∀ i, ∀ᵐ sample ∂P i, 0 ≤ f i sample)
    {C : ℝ} (hC : 0 ≤ C) (hsecond : ∀ i, (∫ sample, (f i sample) ^ 2 ∂P i) ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∀ i, (∫ sample in {sample | R ≤ f i sample}, f i sample ∂P i) < ε := by
  refine ⟨C / ε + 1, by positivity, fun i ↦ ?_⟩
  apply (setIntegral_mass_tail_le_of_second_moment (hm i) (hi i) (hsq i)
    (hnonneg i) (hsecond i) (R := C / ε + 1) (by positivity)).trans_lt
  apply (div_lt_iff₀ (by positivity : 0 < C / ε + 1)).mpr
  have heq : ε * (C / ε + 1) = C + ε := by field_simp
  rw [heq]
  linarith

end OTSelector.Probability
