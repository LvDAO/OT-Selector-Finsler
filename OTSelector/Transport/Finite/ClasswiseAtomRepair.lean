import OTSelector.Probability.AtomicSmoothingClassLaws
import OTSelector.Transport.Coupling.FiniteStageLegality
import OTSelector.Transport.Coupling.OrderedStageChain
import OTSelector.Transport.Finite.TaggedAtomRepair
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepair.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepair`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepair

**Conditions:** Finite original source/target arrays have the stated equal cardinality, ordered class stage couplings and bounded endpoint smoothing radii.

**Objects:** A strict-class original-index bijection with explicit original squared transport cost.

**Proof detail:** Glue the actual stages into a chronological labelled coupling, recover the literal endpoint matrix from smoothing components, and round the legal finite fractional plan to a permutation without increasing cost.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Actual finite classwise stages repair the unchanged original atom arrays.
Class laws, tagged global coupling, RN matrix and legal rounding are constructed. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 500000
variable {E I J : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E] [Fintype I] [Fintype J]

/-- Genuine finite stages between the actual class-grouped smoothing laws yield
a strict-class legal repair on the original labels. Its literal square cost is
at most three times the number of stages times their actual total square cost,
plus the actual common-radius smoothing error. Empty arrays and N=0 are covered. -/
theorem exists_originalAtoms_strictClassRepair_of_actualStages
    (κ : I → Measure E) (τ : J → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (τ j)]
    (c : I → ℕ) (d : J → ℕ) (x : I → E) (y : J → E)
    (N : ℕ) (hc : ∀ i, c i < N) (hd : ∀ j, d j < N)
    (ν : ℕ → Measure E) (π : ℕ → Measure (E × E))
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hνN : ν N = 0)
    (hπ₁ : ∀ k < N, (π k).fst = ν k + originalAtomSmoothingClassLaw κ c k)
    (hπ₂ : ∀ k < N, (π k).snd = ν (k + 1) + originalAtomSmoothingClassLaw τ d k)
    (hstageCost : ∀ k < N, Integrable (fun p ↦ dist p.1 p.2 ^ 2) (π k))
    (hcolours : ∀ k < N, (∀ i, c i ≠ k) ∨ (∀ j, d j ≠ k))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ i, ∀ᵐ u ∂κ i, dist (x i) u ≤ a)
    (hy : ∀ j, ∀ᵐ v ∂τ j, dist v (y j) ≤ b) :
    ∃ σ : I ≃ J, (∀ i, c i < d (σ i)) ∧
      (∑ i, dist (x i) (y (σ i)) ^ 2) ≤
        3 * (N : ℝ) * (∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k) +
          3 * (a ^ 2 + b ^ 2) * (Fintype.card I : ℝ) := by
  classical
  have : ∀ k, IsFiniteMeasure (originalAtomSmoothingClassLaw κ c k) :=
    fun k ↦ originalAtomSmoothingClassLaw_isFiniteMeasure κ c k
  have : ∀ k, IsFiniteMeasure (originalAtomSmoothingClassLaw τ d k) :=
    fun k ↦ originalAtomSmoothingClassLaw_isFiniteMeasure τ d k
  have hzero : ∀ k < N, originalAtomSmoothingClassLaw κ c k = 0 ∨
      originalAtomSmoothingClassLaw τ d k = 0 := by
    intro k hk
    rcases hcolours k hk with hS | hT
    · exact Or.inl (originalAtomSmoothingClassLaw_eq_zero_of_no_label κ c k hS)
    · exact Or.inr (originalAtomSmoothingClassLaw_eq_zero_of_no_label τ d k hT)
  obtain ⟨Γ, hfinite, hΓ, hstrict, hΓI, hΓcost⟩ :=
    exists_finiteStrictOrderedQuadraticClasswiseCoupling ν
      (originalAtomSmoothingClassLaw κ c) (originalAtomSmoothingClassLaw τ d)
      π N hν₀ hνN hπ₁ hπ₂ hstageCost hzero
  have : IsFiniteMeasure Γ := hfinite
  rw [originalAtomSmoothingClassLaw_labelledPrefix κ c N hc,
    originalAtomSmoothingClassLaw_labelledPrefix τ d N hd] at hΓ
  obtain ⟨σ, hσ, hσcost⟩ := exists_originalAtoms_strictClassRepair_of_taggedCoupling
    κ τ c d x y ha hb hx hy Γ hΓ hstrict hΓI
  refine ⟨σ, hσ, ?_⟩
  calc
    _ ≤ 3 * (∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ) +
        3 * (a ^ 2 + b ^ 2) * (Fintype.card I : ℝ) := hσcost
    _ ≤ 3 * ((N : ℝ) * (∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k)) +
        3 * (a ^ 2 + b ^ 2) * (Fintype.card I : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hΓcost (by norm_num : (0 : ℝ) ≤ 3)) le_rfl
    _ = _ := by ring

end OTSelector.Reconstruction

end
end
