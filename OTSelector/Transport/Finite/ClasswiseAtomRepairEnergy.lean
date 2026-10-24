import OTSelector.Probability.AtomicSmoothingClassLaws
import OTSelector.Transport.Coupling.FiniteStageLegality
import OTSelector.Transport.Coupling.OrderedStageChain
import OTSelector.Transport.Finite.TaggedAtomRepairEnergy
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairActualStageEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairActualStageEnergy`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepairActualStageEnergy

**Conditions:** The actual ordered stage couplings and endpoint smoothing laws have integrable quadratic costs/deviations.

**Objects:** Strict original-label repair with the true stage and endpoint deviation energy budget.

**Proof detail:** Construct the same ordered global coupling and exact endpoint matrix, bound its energy by the finite chain and actual integrated deviations, then choose a legal permutation from its Birkhoff decomposition.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57), Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48; [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Real stage plans repair original labels with their actual endpoint energies,
so spreading reserve atoms to the population keeps the sharp transport budget. -/
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 500000
variable {E I J : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E] [Fintype I] [Fintype J]

/-- Actual ordered finite stages and the true endpoint transfer energies give
a strict-class legal bijection on the unchanged original atom labels. -/
theorem exists_originalAtoms_strictClassRepair_of_actualStages_deviationEnergy
    (κ : I → Measure E) (τ : J → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (τ j)]
    (c : I → ℕ) (d : J → ℕ) (x : I → E) (y : J → E)
    (hκI : ∀ i, Integrable (fun u ↦ dist (x i) u ^ 2) (κ i))
    (hτI : ∀ j, Integrable (fun v ↦ dist v (y j) ^ 2) (τ j))
    (N : ℕ) (hc : ∀ i, c i < N) (hd : ∀ j, d j < N)
    (ν : ℕ → Measure E) (π : ℕ → Measure (E × E))
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hνN : ν N = 0)
    (hπ₁ : ∀ k < N, (π k).fst = ν k + originalAtomSmoothingClassLaw κ c k)
    (hπ₂ : ∀ k < N, (π k).snd = ν (k + 1) + originalAtomSmoothingClassLaw τ d k)
    (hstageCost : ∀ k < N, Integrable (fun p ↦ dist p.1 p.2 ^ 2) (π k))
    (hcolours : ∀ k < N, (∀ i, c i ≠ k) ∨ (∀ j, d j ≠ k)) :
    ∃ σ : I ≃ J, (∀ i, c i < d (σ i)) ∧
      (∑ i, dist (x i) (y (σ i)) ^ 2) ≤
        3 * (N : ℝ) * (∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k) +
          3 * (∑ i, ∫ u, dist (x i) u ^ 2 ∂κ i) +
          3 * (∑ j, ∫ v, dist v (y j) ^ 2 ∂τ j) := by
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
  obtain ⟨σ, hσ, hσcost⟩ :=
    exists_originalAtoms_strictClassRepair_of_taggedCoupling_deviationEnergy
      κ τ c d x y hκI hτI Γ hΓ hstrict hΓI
  refine ⟨σ, hσ, hσcost.trans ?_⟩
  have hthree := mul_le_mul_of_nonneg_left hΓcost (by norm_num : (0 : ℝ) ≤ 3)
  calc
    _ ≤ 3 * ((N : ℝ) * (∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k)) +
        3 * (∑ i, ∫ u, dist (x i) u ^ 2 ∂κ i) +
        3 * (∑ j, ∫ v, dist v (y j) ^ 2 ∂τ j) :=
      add_le_add (add_le_add hthree le_rfl) le_rfl
    _ = _ := by ring

end OTSelector.Reconstruction

end
end
