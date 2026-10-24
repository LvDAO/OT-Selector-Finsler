import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import OTSelector.MeasureTheory.LocalFiniteMeasure

/-!
## Lemma skeleton

* **Conditions:** Locally compact second-countable metrizable space with compact exhaustion.
* **Objects:** Countably many compact tests and an injective real-valued code.
* **Proof detail:** Multiply a dense continuous family by compact cutoffs; use test integral continuity and measure uniqueness.

## Mathematical sources

* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 281E, Stone–Weierstrass theorem for a point-separating unital algebra.
  https://www1.essex.ac.uk/maths/people/fremlin/chap28.pdf#page=4
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47

**Relationship to the sources:** The explicit sum-indexed test code and compact-family sequential compactness are constructive formal choices; no book claims this exact enumeration.
-/

/-!
# Countably many compact tests determine diffuse measures

A compact exhaustion and a dense sequence of continuous functions give a fixed
countable family of genuine compact tests. This family separates all locally
finite measures, including diffuse transport plans.
-/

open MeasureTheory Set Function Topology TopologicalSpace
open scoped CompactlySupported

noncomputable section
namespace OTSelector.Probability.LocalFiniteMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X]

omit [MeasurableSpace X] [T2Space X] [BorelSpace X] [SigmaCompactSpace X] in
theorem exists_compact_cutoff {K : Set X} (hK : IsCompact K) :
    ∃ φ : C_c(X, ℝ), EqOn φ 1 K ∧ ∀ x, φ x ∈ Icc 0 1 := by
  obtain ⟨f, hf, _, hcomp, hbound⟩ := exists_continuous_one_zero_of_isCompact
    hK (isClosed_empty : IsClosed (∅ : Set X)) (disjoint_empty K)
  exact ⟨⟨f, hcomp⟩, hf, hbound⟩

def exhaustionCutoff (K : CompactExhaustion X) (n : ℕ) : C_c(X, ℝ) :=
  (exists_compact_cutoff (K.isCompact n)).choose

omit [MeasurableSpace X] [T2Space X] [BorelSpace X] [SigmaCompactSpace X] in
theorem exhaustionCutoff_eq_one (K : CompactExhaustion X) (n : ℕ) :
    EqOn (exhaustionCutoff K n) 1 (K n) :=
  (exists_compact_cutoff (K.isCompact n)).choose_spec.1

omit [MeasurableSpace X] [T2Space X] [BorelSpace X] [SigmaCompactSpace X] in
theorem exhaustionCutoff_bounds (K : CompactExhaustion X) (n : ℕ) (x : X) :
    exhaustionCutoff K n x ∈ Icc 0 1 :=
  (exists_compact_cutoff (K.isCompact n)).choose_spec.2 x

/-- Multiplication by a fixed compact cutoff preserves actual compact support. -/
def weightedContinuousTest (φ : C_c(X, ℝ)) (g : C(X, ℝ)) : C_c(X, ℝ) where
  toFun x := φ x * g x
  continuous_toFun := φ.continuous.mul g.continuous
  hasCompactSupport' := φ.hasCompactSupport.mul_right

omit [T2Space X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] in
theorem continuous_weightedTestIntegral (μ : LocalFiniteMeasure X) (φ : C_c(X, ℝ)) :
    Continuous (fun g : C(X, ℝ) ↦ testIntegral μ (weightedContinuousTest φ g)) := by
  change Continuous (fun g : C(X, ℝ) ↦ ∫ x, φ x * g x ∂(μ : Measure X))
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support φ.hasCompactSupport
  · exact ((φ.continuous.comp continuous_snd).mul continuous_eval).continuousOn
  · intro g x _ hx
    simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

omit [MeasurableSpace X] [T2Space X] [BorelSpace X] [SigmaCompactSpace X] in
theorem weighted_exhaustionCutoff_eq (K : CompactExhaustion X) (f : C_c(X, ℝ))
    {n : ℕ} (hf : tsupport f ⊆ K n) :
    weightedContinuousTest (exhaustionCutoff K n) f.toContinuousMap = f := by
  ext x
  change exhaustionCutoff K n x * f x = f x
  by_cases hx : x ∈ K n
  · rw [exhaustionCutoff_eq_one K n hx]
    exact one_mul _
  · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hf h)), mul_zero]

variable [SecondCountableTopology X]

/-- The tests depend only on the original underlying space and its exhaustion. -/
def separatingTest (K : CompactExhaustion X) : ℕ ⊕ (ℕ × ℕ) → C_c(X, ℝ)
  | .inl n => exhaustionCutoff K n
  | .inr (n, m) => weightedContinuousTest (exhaustionCutoff K n)
      (denseSeq C(X, ℝ) m)

def separatingTestCode (K : CompactExhaustion X) (μ : LocalFiniteMeasure X)
    (i : ℕ ⊕ (ℕ × ℕ)) : ℝ := testIntegral μ (separatingTest K i)

omit [T2Space X] [BorelSpace X] [SigmaCompactSpace X] in
theorem continuous_separatingTestCode (K : CompactExhaustion X) :
    Continuous (separatingTestCode K : LocalFiniteMeasure X → (ℕ ⊕ (ℕ × ℕ) → ℝ)) :=
  continuous_pi (fun i ↦ continuous_testIntegral (separatingTest K i))

/-- Equality of the fixed countable compact tests determines the complete measure. -/
theorem separatingTestCode_injective (K : CompactExhaustion X) :
    Injective (separatingTestCode K : LocalFiniteMeasure X → (ℕ ⊕ (ℕ × ℕ) → ℝ)) := by
  intro μ ν heq
  apply testIntegral_injective
  funext f
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
  have hfull := (denseRange_denseSeq C(X, ℝ)).equalizer
    (continuous_weightedTestIntegral μ (exhaustionCutoff K n))
    (continuous_weightedTestIntegral ν (exhaustionCutoff K n))
    (funext (fun m ↦ congrFun heq (.inr (n, m))))
  have h := congrFun hfull f.toContinuousMap
  simpa only [weighted_exhaustionCutoff_eq K f hn] using h

/-- Every compact family of diffuse measures is metrizable by the fixed test code. -/
theorem metrizableSpace_of_isCompact {A : Set (LocalFiniteMeasure X)} (hA : IsCompact A) :
    MetrizableSpace A := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let K := CompactExhaustion.choice X
  have hcont := (continuous_separatingTestCode K).comp
    (continuous_subtype_val : Continuous (Subtype.val : A → LocalFiniteMeasure X))
  exact (hcont.isClosedEmbedding
    ((separatingTestCode_injective K).comp Subtype.val_injective)).isEmbedding.metrizableSpace

/-- Local mass compactness now gives actual convergent subsequences of measures. -/
theorem isSeqCompact_of_isCompact {A : Set (LocalFiniteMeasure X)} (hA : IsCompact A) :
    IsSeqCompact A := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let : MetrizableSpace A := metrizableSpace_of_isCompact hA
  intro μ hμ
  obtain ⟨ν, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (fun n ↦ (⟨μ n, hμ n⟩ : A))
  exact ⟨ν.val, ν.property, φ, hφ, (continuous_subtype_val.tendsto ν).comp hlim⟩

end OTSelector.Probability.LocalFiniteMeasure
