import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Selected Integer Bad Event Second Moment

Conditions: A fixed measurable random integer selector, fixed-scale measurable bad events and envelopes with summable squared bad integrals; the selected readout is dominated on its selected bad event and restricted to selector≥N.

Objects: Integrability and a deterministic series-tail upper bound for the selected bad square, followed by its vanishing L2 contribution.

Proof detail: Dominate the selected summand by the whole fixed-index nonnegative tail, use Tonelli and send the summable tail to zero.

Relation to primary sources: A local domination/Tonelli argument for a selector that may depend on every bad event and envelope. No independent-selection step is inserted.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.7, Theorem 1.7.2, p. 38. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=46
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 2.3, Theorem 2.3.1 and preceding union-tail estimate, pp. 67–68. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=75
-/
/-! # Current bad-event errors at a measurable random integer scale -/
open Set Function MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The current bad event at any measurable integer selector costs at most
the sum of the original fixed-scale mean-square errors above the cutoff.
Integrability is a consequence of the fixed-scale summable bounds. -/
theorem integrable_selected_bad_sq_and_integral_le_tsum
    {k : Ω → ℕ} (hk : Measurable k) {B : ℕ → Set Ω}
    (hB : ∀ m, MeasurableSet (B m)) {W : ℕ → Ω → ℝ}
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (_hC : 0 ≤ C)
    (hdom : ∀ᵐ ω ∂P, ω ∈ B (k ω) → |f ω| ≤ C * |W (k ω) ω|)
    {m₀ : ℕ} (hInt : ∀ m, m₀ ≤ m → Integrable (fun ω ↦ ((B m).indicator (W m) ω) ^ 2) P)
    (hsum : Summable (fun m ↦ ∫ ω, ((B m).indicator (W m) ω) ^ 2 ∂P))
    {N : ℕ} (hN : m₀ ≤ N) :
    let A := {ω | N ≤ k ω ∧ ω ∈ B (k ω)}
    Integrable (fun ω ↦ (A.indicator f ω) ^ 2) P ∧
      (∫ ω, (A.indicator f ω) ^ 2 ∂P) ≤
        C ^ 2 * ∑' n : ℕ, ∫ ω, ((B (n + N)).indicator (W (n + N)) ω) ^ 2 ∂P := by
  let A := {ω | N ≤ k ω ∧ ω ∈ B (k ω)}
  let S : ℕ → Set Ω := fun n ↦ {ω | k ω = n + N} ∩ B (n + N)
  have hS (n : ℕ) : MeasurableSet (S n) :=
    ((measurableSet_singleton (n + N)).preimage hk).inter (hB _)
  have hAeq : A = ⋃ n : ℕ, S n := by
    ext ω
    constructor
    · rintro ⟨hlarge, hbad⟩
      refine mem_iUnion.mpr ⟨k ω - N, ?_⟩
      exact ⟨(Nat.sub_add_cancel hlarge).symm, by simpa [Nat.sub_add_cancel hlarge] using hbad⟩
    · intro hω
      obtain ⟨n, hn, hb⟩ := mem_iUnion.mp hω
      change k ω = n + N at hn
      exact ⟨by omega, by simpa only [hn] using hb⟩
  have hA : MeasurableSet A := hAeq ▸ MeasurableSet.iUnion hS
  have hd : Pairwise (Disjoint on S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have hi' : k ω = i + N := hi.1
    have hj' : k ω = j + N := hj.1
    exact hij (by omega)
  let J : ℕ → ℝ := fun m ↦ ∫ ω, ((B m).indicator (W m) ω) ^ 2 ∂P
  have hshift : Summable (fun n : ℕ ↦ C ^ 2 * J (n + N)) :=
    ((summable_nat_add_iff N).2 hsum).mul_left _
  have hslice (n : ℕ) :
      Integrable ((S n).indicator (fun ω ↦ f ω ^ 2)) P ∧
        (∫ ω in S n, f ω ^ 2 ∂P) ≤ C ^ 2 * J (n + N) := by
    have hmajor := (hInt (n + N) (by omega)).const_mul (C ^ 2)
    have hle : ∀ᵐ ω ∂P, (S n).indicator (fun ω ↦ f ω ^ 2) ω ≤
        C ^ 2 * ((B (n + N)).indicator (W (n + N)) ω) ^ 2 := by
      filter_upwards [hdom] with ω hω
      by_cases hs : ω ∈ S n
      · have hkω : k ω = n + N := hs.1
        have hb := hs.2
        have h : |f ω| ≤ C * |W (n + N) ω| := by
          simpa only [hkω] using hω (by simpa only [hkω] using hb)
        rw [indicator_of_mem hs, indicator_of_mem hb]
        nlinarith [sq_nonneg (C * |W (n + N) ω| - |f ω|), sq_abs (f ω),
          sq_abs (W (n + N) ω), abs_nonneg (f ω), abs_nonneg (W (n + N) ω)]
      · rw [indicator_of_notMem hs]
        positivity
    have hi : Integrable ((S n).indicator (fun ω ↦ f ω ^ 2)) P :=
      hmajor.mono' ((hf.pow_const 2).indicator (hS n)).aestronglyMeasurable
        (hle.mono fun ω hω ↦ by
          rwa [Real.norm_of_nonneg (indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)] )
    refine ⟨hi, ?_⟩
    have h := integral_mono_ae hi hmajor hle
    rwa [integral_indicator (hS n), integral_const_mul] at h
  have hsliceOn (n : ℕ) : IntegrableOn (fun ω ↦ f ω ^ 2) (S n) P :=
    (integrable_indicator_iff (hS n)).mp (hslice n).1
  have hsliceSum : Summable (fun n ↦ ∫ ω in S n, ‖f ω ^ 2‖ ∂P) := by
    simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hshift.of_nonneg_of_le (fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _)
      (fun n ↦ (hslice n).2)
  have hUnion : IntegrableOn (fun ω ↦ f ω ^ 2) (⋃ n, S n) P :=
    integrableOn_iUnion_of_summable_integral_norm hsliceOn hsliceSum
  have hpow : (fun ω ↦ (A.indicator f ω) ^ 2) = A.indicator (fun ω ↦ f ω ^ 2) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  change Integrable (fun ω ↦ (A.indicator f ω) ^ 2) P ∧ _
  rw [hpow]
  refine ⟨(hAeq ▸ hUnion).integrable_indicator hA, ?_⟩
  rw [integral_indicator hA, hAeq, integral_iUnion hS hd hUnion]
  calc
    _ ≤ ∑' n : ℕ, C ^ 2 * J (n + N) :=
      Summable.tsum_le_tsum (fun n ↦ (hslice n).2)
        (by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsliceSum) hshift
    _ = C ^ 2 * ∑' n : ℕ, J (n + N) :=
      ((summable_nat_add_iff N).2 hsum).tsum_mul_left _

/-- The selected-current-bad error above a diverging cutoff vanishes in L2.
The selector, bad events, and envelope counts may depend on the same scene. -/
theorem tendsto_selected_bad_sq_integral_zero
    {k : Ω → ℕ} (hk : Measurable k) {B : ℕ → Set Ω}
    (hB : ∀ m, MeasurableSet (B m)) {W : ℕ → Ω → ℝ}
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ᵐ ω ∂P, ω ∈ B (k ω) → |f ω| ≤ C * |W (k ω) ω|)
    {m₀ : ℕ} (hInt : ∀ m, m₀ ≤ m → Integrable (fun ω ↦ ((B m).indicator (W m) ω) ^ 2) P)
    (hsum : Summable (fun m ↦ ∫ ω, ((B m).indicator (W m) ω) ^ 2 ∂P)) :
    Tendsto (fun N : ℕ ↦ ∫ ω,
      (({ω | N ≤ k ω ∧ ω ∈ B (k ω)}).indicator f ω) ^ 2 ∂P) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ integral_nonneg fun ω ↦ sq_nonneg _))
    ((eventually_ge_atTop m₀).mono (fun N hN ↦
      (integrable_selected_bad_sq_and_integral_le_tsum hk hB hf hC hdom hInt hsum hN).2))
  simpa only [mul_zero] using (tendsto_sum_nat_add
    (fun m ↦ ∫ ω, ((B m).indicator (W m) ω) ^ 2 ∂P)).const_mul (C ^ 2)

end OTSelector.Probability
