import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish

/-!
Conditions: Finite laws on the specified locally finite measure carrier and equality of expectations of every actual nonnegative compact-test Laplace readout.

Objects: Equality of the whole original random-measure laws from the bounded compact Laplace observations.

Proof detail: Nonnegative compact tests separate locally finite measures; their exponentials form a multiplicative bounded continuous separating family. The proved finite-law extensionality theorem identifies the original laws.

References: Günter Last and Mathew Penrose: Section 2.3, Proposition 2.10, pp. 14–15; Section 3.1, Proposition 3.2, p. 20; D. H. Fremlin: Section 281E, Stone–Weierstrass theorem for a point-separating unital algebra.
Relation: A compact-Laplace law-determination argument for general locally finite input laws, not just Poisson laws. No first moment, uniform integrability or new coupling is required.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalInputLawDetermination.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalInputLawDetermination`; the selected original proof blocks follow. -/
section

/-!
# Compact Laplace observations determine the entire original input law

Nonnegative compact tests determine a locally finite measure. Their bounded
Laplace observations form a point-separating multiplicative family. Finite
measure extensionality therefore determines the whole random-measure law,
without first moments, uniform integrability, or a newly chosen input coupling.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]

/-- A nonnegative original compact observation of a locally finite input. -/
abbrev LegalNonnegativeInputTest (X : Type*) [TopologicalSpace X] :=
  {F : C_c(X, ℝ) // ∀ x, 0 ≤ F x}

/-- The bounded continuous Laplace observation of the actual input measure. -/
def legalInputMeasureLaplace (F : LegalNonnegativeInputTest X) : LocalFiniteMeasure X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun μ ↦ Real.exp (-LocalFiniteMeasure.testIntegral μ F.1),
      Real.continuous_exp.comp (LocalFiniteMeasure.continuous_testIntegral F.1).neg⟩ 2 (by
      intro μ ν
      have hb (ζ : LocalFiniteMeasure X) : |Real.exp (-LocalFiniteMeasure.testIntegral ζ F.1)| ≤ 1 := by
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        exact neg_nonpos.mpr (integral_nonneg F.2)
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans ((add_le_add (hb μ) (hb ν)).trans_eq (by norm_num)))

/-- Original compact Laplace identities identify the entire locally finite
random-measure law; no additional input moment assumption is needed. -/
theorem measure_eq_of_legalInput_compact_laplace
    (P P' : Measure (LocalFiniteMeasure X)) [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ F : LegalNonnegativeInputTest X,
      (∫ μ, legalInputMeasureLaplace F μ ∂P) = ∫ μ, legalInputMeasureLaplace F μ ∂P') : P = P' := by
  classical
  let M : Submonoid (LocalFiniteMeasure X →ᵇ ℝ) :=
    { carrier := range (legalInputMeasureLaplace (X := X))
      one_mem' := by
        refine ⟨⟨0, fun _ ↦ le_rfl⟩, ?_⟩
        ext μ
        simp [legalInputMeasureLaplace, LocalFiniteMeasure.testIntegral]
      mul_mem' := by
        rintro a b ⟨F, rfl⟩ ⟨G, rfl⟩
        refine ⟨⟨F.1 + G.1, fun x ↦ add_nonneg (F.2 x) (G.2 x)⟩, ?_⟩
        ext μ
        change Real.exp (-(∫ x, (F.1 + G.1) x ∂(μ : Measure X))) =
          Real.exp (-(∫ x, F.1 x ∂(μ : Measure X))) *
            Real.exp (-(∫ x, G.1 x ∂(μ : Measure X)))
        simp only [CompactlySupportedContinuousMap.add_apply]
        rw [integral_add F.1.integrable G.1.integrable, ← Real.exp_add]
        congr 1
        ring }
  let A : StarSubalgebra ℝ (LocalFiniteMeasure X →ᵇ ℝ) :=
    { Algebra.adjoin ℝ (M : Set (LocalFiniteMeasure X →ᵇ ℝ)) with
      star_mem' := by
        intro a ha
        have heq : star a = a := by ext μ; simp
        simpa only [heq] using ha }
  have hA : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro μ ν hne
    have hex : ∃ F : LegalNonnegativeInputTest X,
        LocalFiniteMeasure.testIntegral μ F.1 ≠ LocalFiniteMeasure.testIntegral ν F.1 := by
      by_contra! heq
      apply hne
      apply Subtype.ext
      apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
      intro F
      simpa only [LocalFiniteMeasure.testIntegral, CompactlySupportedContinuousMap.toReal_apply] using
        heq ⟨F.toReal, fun x ↦ by simpa only [CompactlySupportedContinuousMap.toReal_apply] using NNReal.coe_nonneg (F x)⟩
    obtain ⟨F, hF⟩ := hex
    refine ⟨(legalInputMeasureLaplace F).toContinuousMap, ?_, ?_⟩
    · refine ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℝ) (legalInputMeasureLaplace F), ?_, rfl⟩
      refine ⟨legalInputMeasureLaplace F, ?_, rfl⟩
      exact Algebra.subset_adjoin (mem_range_self F)
    · change Real.exp (-LocalFiniteMeasure.testIntegral μ F.1) ≠
        Real.exp (-LocalFiniteMeasure.testIntegral ν F.1)
      exact fun heq ↦ hF (neg_injective (Real.exp_injective heq))
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hA
  intro a ha
  have hspan : a ∈ Submodule.span ℝ (M : Set (LocalFiniteMeasure X →ᵇ ℝ)) := by
    change a ∈ (Algebra.adjoin ℝ (M : Set (LocalFiniteMeasure X →ᵇ ℝ))).toSubmodule at ha
    rwa [Algebra.adjoin_eq_span, M.closure_eq] at ha
  clear ha
  induction hspan using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨F, rfl⟩ := ha
      exact h F
  | zero => simp
  | add a b ha hb hea heb =>
      simp only [BoundedContinuousFunction.add_apply]
      rw [integral_add (a.integrable P) (b.integrable P),
        integral_add (a.integrable P') (b.integrable P'), hea, heb]
  | smul c a ha hea =>
      simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hea]

end OTSelector.Reconstruction

end
end
