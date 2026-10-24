import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.PointProcess.CompactLaplaceDetermination
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplacePairDetermination.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplacePairDetermination`; the selected original proof blocks follow. -/
section

/-!
# PointProcess.PairLaplaceDetermination

## Lemma skeleton

* **Conditions:** Finite laws of locally finite measure pairs, or measurable random measures under a probability law; all nonnegative compact Laplace test products agree or factor.
* **Objects:** Joint-law determination and actual independence from compact Laplace factorization.
* **Proof detail:** Compact Laplace tests contain constants, multiply by adding tests and separate locally finite measures. Use their multiplicative determining algebra on the product carrier, then compare with the product of the two marginals.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap28.pdf#page=4): Section 281E, Stone–Weierstrass theorem for a point-separating unital algebra.
- [Olav Kallenberg, Random Measures, Theory and Applications (Springer 2017)](https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4): Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
- [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254): Appendix A.1, Theorem A.5, p. 242.

Source relation (composition): Compact Laplace algebra determination on the existing carrier; independence is a proved law-factorization consequence.
-/

/-!
# Joint laws from pairs of original compact Laplace observations

A product of two actual compact Laplace observations determines joint laws on
locally finite measures. Factorization therefore gives actual independence,
without an auxiliary independence assumption on selected endpoints.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

@[simp] theorem legalInputMeasureLaplace_zero (μ : LocalFiniteMeasure X) :
    legalInputMeasureLaplace ⟨0, fun _ ↦ le_rfl⟩ μ = 1 := by
  simp [legalInputMeasureLaplace, LocalFiniteMeasure.testIntegral]

/-- Products of actual Laplace readouts add their original compact tests. -/
theorem legalInputMeasureLaplace_add (F G : LegalNonnegativeInputTest X)
    (μ : LocalFiniteMeasure X) :
    legalInputMeasureLaplace ⟨F.1 + G.1, fun x ↦ add_nonneg (F.2 x) (G.2 x)⟩ μ =
      legalInputMeasureLaplace F μ * legalInputMeasureLaplace G μ := by
  change Real.exp (-(∫ x, (F.1 + G.1) x ∂(μ : Measure X))) =
    Real.exp (-(∫ x, F.1 x ∂(μ : Measure X))) *
      Real.exp (-(∫ x, G.1 x ∂(μ : Measure X)))
  simp only [CompactlySupportedContinuousMap.add_apply]
  rw [integral_add F.1.integrable G.1.integrable, ← Real.exp_add]
  congr 1
  ring

/-- Nonnegative compact Laplace observations separate actual locally finite measures. -/
theorem exists_legalInputMeasureLaplace_ne {μ ν : LocalFiniteMeasure X} (hne : μ ≠ ν) :
    ∃ F : LegalNonnegativeInputTest X, legalInputMeasureLaplace F μ ≠
      legalInputMeasureLaplace F ν := by
  by_contra! h
  apply hne
  apply Subtype.ext
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro F
  have heq := h ⟨F.toReal, fun x ↦ by
    simpa only [CompactlySupportedContinuousMap.toReal_apply] using NNReal.coe_nonneg (F x)⟩
  change Real.exp (-LocalFiniteMeasure.testIntegral μ F.toReal) =
    Real.exp (-LocalFiniteMeasure.testIntegral ν F.toReal) at heq
  simpa only [LocalFiniteMeasure.testIntegral, CompactlySupportedContinuousMap.toReal_apply]
    using neg_injective (Real.exp_injective heq)

/-- A product readout retains both actual locally finite inputs. -/
def legalInputMeasureLaplacePair (F G : LegalNonnegativeInputTest X) :
    (LocalFiniteMeasure X × LocalFiniteMeasure X) →ᵇ ℝ :=
  (legalInputMeasureLaplace F).compContinuous ⟨Prod.fst, continuous_fst⟩ *
    (legalInputMeasureLaplace G).compContinuous ⟨Prod.snd, continuous_snd⟩

/-- Joint compact Laplace observations determine the full pair law. -/
theorem measure_eq_of_legalInput_compact_laplace_pair
    (P P' : Measure (LocalFiniteMeasure X × LocalFiniteMeasure X))
    [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ F G : LegalNonnegativeInputTest X,
      (∫ z, legalInputMeasureLaplacePair F G z ∂P) =
        ∫ z, legalInputMeasureLaplacePair F G z ∂P') : P = P' := by
  classical
  let M : Submonoid ((LocalFiniteMeasure X × LocalFiniteMeasure X) →ᵇ ℝ) :=
    { carrier := range (fun FG : LegalNonnegativeInputTest X × LegalNonnegativeInputTest X ↦
        legalInputMeasureLaplacePair FG.1 FG.2)
      one_mem' := by
        refine ⟨(⟨0, fun _ ↦ le_rfl⟩, ⟨0, fun _ ↦ le_rfl⟩), ?_⟩
        ext z
        simp [legalInputMeasureLaplacePair]
      mul_mem' := by
        rintro a b ⟨⟨F, G⟩, rfl⟩ ⟨⟨F', G'⟩, rfl⟩
        refine ⟨(⟨F.1 + F'.1, fun x ↦ add_nonneg (F.2 x) (F'.2 x)⟩,
          ⟨G.1 + G'.1, fun x ↦ add_nonneg (G.2 x) (G'.2 x)⟩), ?_⟩
        ext z
        simp only [legalInputMeasureLaplacePair, BoundedContinuousFunction.mul_apply,
          BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
          legalInputMeasureLaplace_add]
        ring }
  let A : StarSubalgebra ℝ ((LocalFiniteMeasure X × LocalFiniteMeasure X) →ᵇ ℝ) :=
    { Algebra.adjoin ℝ (M : Set ((LocalFiniteMeasure X × LocalFiniteMeasure X) →ᵇ ℝ)) with
      star_mem' := by
        intro a ha
        have heq : star a = a := by ext z; simp
        simpa only [heq] using ha }
  have hA : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro z w hne
    have hex : ∃ F G : LegalNonnegativeInputTest X,
        legalInputMeasureLaplacePair F G z ≠ legalInputMeasureLaplacePair F G w := by
      by_cases hfst : z.1 = w.1
      · have hsnd : z.2 ≠ w.2 := fun hs ↦ hne (Prod.ext hfst hs)
        obtain ⟨G, hG⟩ := exists_legalInputMeasureLaplace_ne hsnd
        refine ⟨⟨0, fun _ ↦ le_rfl⟩, G, ?_⟩
        simpa [legalInputMeasureLaplacePair] using hG
      · obtain ⟨F, hF⟩ := exists_legalInputMeasureLaplace_ne hfst
        refine ⟨F, ⟨0, fun _ ↦ le_rfl⟩, ?_⟩
        simpa [legalInputMeasureLaplacePair] using hF
    obtain ⟨F, G, hFG⟩ := hex
    refine ⟨(legalInputMeasureLaplacePair F G).toContinuousMap, ?_, hFG⟩
    refine ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℝ)
      (legalInputMeasureLaplacePair F G), ?_, rfl⟩
    refine ⟨legalInputMeasureLaplacePair F G, ?_, rfl⟩
    exact Algebra.subset_adjoin (mem_range_self (F, G))
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hA
  intro a ha
  have hspan : a ∈ Submodule.span ℝ
      (M : Set ((LocalFiniteMeasure X × LocalFiniteMeasure X) →ᵇ ℝ)) := by
    change a ∈ (Algebra.adjoin ℝ
      (M : Set ((LocalFiniteMeasure X × LocalFiniteMeasure X) →ᵇ ℝ))).toSubmodule at ha
    rwa [Algebra.adjoin_eq_span, M.closure_eq] at ha
  clear ha
  induction hspan using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨⟨F, G⟩, rfl⟩ := ha
      exact h F G
  | zero => simp
  | add a b ha hb hea heb =>
      simp only [BoundedContinuousFunction.add_apply]
      rw [integral_add (a.integrable P) (b.integrable P),
        integral_add (a.integrable P') (b.integrable P'), hea, heb]
  | smul c a ha hea =>
      simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hea]

/-- Factorization of compact Laplace observations proves actual independence. -/
theorem indepFun_of_legalInput_compact_laplace_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → LocalFiniteMeasure X) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ F G : LegalNonnegativeInputTest X,
      (∫ ω, legalInputMeasureLaplace F (f ω) * legalInputMeasureLaplace G (g ω) ∂P) =
        (∫ ω, legalInputMeasureLaplace F (f ω) ∂P) *
          ∫ ω, legalInputMeasureLaplace G (g ω) ∂P) : IndepFun f g P := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr
  apply measure_eq_of_legalInput_compact_laplace_pair
  intro F G
  rw [integral_map (hf.prodMk hg).aemeasurable
    (legalInputMeasureLaplacePair F G).continuous.aestronglyMeasurable]
  change (∫ ω, legalInputMeasureLaplace F (f ω) * legalInputMeasureLaplace G (g ω) ∂P) =
    ∫ z, legalInputMeasureLaplace F z.1 * legalInputMeasureLaplace G z.2
      ∂(P.map f).prod (P.map g)
  rw [integral_prod_mul,
    integral_map hf.aemeasurable (legalInputMeasureLaplace F).continuous.aestronglyMeasurable,
    integral_map hg.aemeasurable (legalInputMeasureLaplace G).continuous.aestronglyMeasurable]
  exact h F G

end OTSelector.Reconstruction

end
end
