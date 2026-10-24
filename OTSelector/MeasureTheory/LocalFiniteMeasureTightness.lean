import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Semicontinuity.Basic
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCompactness

/-!
## Lemma skeleton

* **Conditions:** Uniform local mass tails or finite first moments on an open exhaustion.
* **Objects:** Tight families of laws of diffuse locally finite measures, on varying sample spaces.
* **Proof detail:** Choose summable window error budgets, union bound their complements and use Markov on each local mass.

## Mathematical sources

* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=68
* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37

**Relationship to the sources:** The quantitative exhaustion cutoffs and varying-space map formulation are local consequences of tightness and Markov; they are not independence assumptions.
-/

/-!
# Tightness of diffuse plan laws from local mass moments

Uniform first moments on an open exhaustion give genuine compact containment in
the compact-test topology. The probability spaces carrying the random measures
may vary with sample size.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace OTSelector.Probability.LocalFiniteMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X]

omit [T2Space X] in
theorem measurable_measure_open {U : Set X} (hU : IsOpen U) :
    Measurable (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X) U) :=
  (lowerSemicontinuous_measure_open hU).measurable

/-- One actual compact family controls the escaped law mass by local mass tails. -/
theorem exists_isCompact_measure_compl_le_localMassTail
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hcover : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ U n) (C : ℕ → ℝ≥0) :
    ∃ K : Set (LocalFiniteMeasure X), IsCompact K ∧
      ∀ P : Measure (LocalFiniteMeasure X),
        P Kᶜ ≤ ∑' n, P {μ | (C n : ℝ≥0∞) < (μ : Measure X) (U n)} := by
  let K : Set (LocalFiniteMeasure X) := {μ | ∀ n, (μ : Measure X) (U n) ≤ C n}
  refine ⟨K, isCompact_localMass_le U hU hcover C, fun P ↦ ?_⟩
  have hsub : Kᶜ ⊆ ⋃ n, {μ | (C n : ℝ≥0∞) < (μ : Measure X) (U n)} := by
    intro μ hμ
    simpa only [K, mem_compl_iff, mem_ofPred_eq, not_forall, not_le, mem_iUnion] using hμ
  exact (measure_mono hsub).trans (measure_iUnion_le _)

/-- Vanishing local mass tails imply tightness without an atomic scene carrier. -/
theorem isTightMeasureSet_of_localMass_tail
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hcover : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ U n)
    (S : Set (Measure (LocalFiniteMeasure X)))
    (htail : ∀ n, ∀ ε : ℝ≥0, 0 < ε → ∃ C : ℝ≥0,
      ∀ P ∈ S, P {μ | (C : ℝ≥0∞) < (μ : Measure X) (U n)} ≤ ε) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose C hC using fun n ↦ htail n (δ n) (hδpos n)
  obtain ⟨K, hK, hbound⟩ := exists_isCompact_measure_compl_le_localMassTail U hU hcover C
  exact ⟨K, hK, fun P hP ↦ (hbound P).trans
    ((ENNReal.tsum_le_tsum (fun n ↦ hC n P hP)).trans hδsum.le)⟩

omit [T2Space X] in
/-- Markov's inequality uses the actual open-window mass evaluation. -/
theorem measure_localMassTail_le_lintegral_div
    (P : Measure (LocalFiniteMeasure X)) {U : Set X} (hU : IsOpen U)
    {C : ℝ≥0} (hC : 0 < C) :
    P {μ | (C : ℝ≥0∞) < (μ : Measure X) U} ≤
      (∫⁻ μ, (μ : Measure X) U ∂P) / C := by
  apply (measure_mono (show {μ : LocalFiniteMeasure X | (C : ℝ≥0∞) < (μ : Measure X) U} ⊆
    {μ | (C : ℝ≥0∞) ≤ (μ : Measure X) U} from fun μ h ↦
      show (C : ℝ≥0∞) ≤ (μ : Measure X) U from le_of_lt h)).trans
  exact meas_ge_le_lintegral_div (measurable_measure_open hU).aemeasurable
    (ENNReal.coe_ne_zero.mpr hC.ne') ENNReal.coe_ne_top

/-- Uniform finite first moments on each open window produce tight plan laws. -/
theorem isTightMeasureSet_of_lintegral_localMass_le
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hcover : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ U n)
    (S : Set (Measure (LocalFiniteMeasure X))) (b : ℕ → ℝ≥0∞)
    (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ P ∈ S, ∀ n, ∫⁻ μ, (μ : Measure X) (U n) ∂P ≤ b n) :
    IsTightMeasureSet S := by
  apply isTightMeasureSet_of_localMass_tail U hU hcover S
  intro n ε hε
  have hεzero : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top (hb n) hεzero)
  have hratio : b n / ((M + 1 : ℕ) : ℝ≥0∞) ≤ ε := by
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    rw [mul_comm]
    apply (ENNReal.div_le_iff hεzero ENNReal.coe_ne_top).mp
    exact hM.le.trans (by exact_mod_cast Nat.le_succ M)
  refine ⟨(M + 1 : ℕ), fun P hP ↦ ?_⟩
  exact (measure_localMassTail_le_lintegral_div P (hU n) (C := (M + 1 : ℕ))
    (by positivity)).trans
    ((ENNReal.div_le_div_right (hbound P hP n) _).trans (by exact_mod_cast hratio))

/-- Random diffuse measures on sample-size-dependent spaces give tight laws. -/
theorem isTightMeasureSet_map_of_lintegral_localMass_le
    {I : Type*} {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) (measure : ∀ i, Ω i → LocalFiniteMeasure X)
    (hmeasure : ∀ i, Measurable (measure i))
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hcover : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ U n)
    (b : ℕ → ℝ≥0∞) (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ i n, ∫⁻ sample, (measure i sample : Measure X) (U n) ∂P i ≤ b n) :
    IsTightMeasureSet (range (fun i ↦ (P i).map (measure i))) := by
  apply isTightMeasureSet_of_lintegral_localMass_le U hU hcover _ b hb
  rintro _ ⟨i, rfl⟩ n
  rw [lintegral_map (measurable_measure_open (hU n)) (hmeasure i)]
  exact hbound i n

end OTSelector.Probability.LocalFiniteMeasure
