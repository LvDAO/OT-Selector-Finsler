import OTSelector.MeasureTheory.CompactProductMarginalTests
import OTSelector.MeasureTheory.LocalFiniteMeasure
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CompactProductTestMarginalDomination.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CompactProductTestMarginalDomination`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.CompactProductMarginalDomination

## Lemma skeleton

* **Conditions:** A locally finite product plan, an outer-regular source reference and domination for all nonnegative compact source tests and [0,1] compact target tests.
* **Objects:** Whole first/second marginal domination, including possibly nonproper projections.
* **Proof detail:** Exhaust the target with compact cutoffs, obtain open-source-set bounds from nonnegative compact tests, then use outer regularity for arbitrary source sets.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47): Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Derived compact-test order criterion; it does not assume the projected plan is locally finite.
-/

/-!
# Whole marginal domination from compact product tests

Compact products exhaust all targets before outer regularity extends the bound
from open source windows to every source set. The endpoint projection need not
be proper and no local finiteness of the projected plan is assumed.
-/

open Set MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]

/-- Compact product-test domination controls the complete source marginal,
including all targets, without a properness or marginal finiteness hypothesis. -/
theorem fst_le_of_compact_product_tests
    (π : LocalFiniteMeasure (X × Y)) (ν : Measure X) [ν.OuterRegular]
    (h : ∀ (f : C_c(X, ℝ)), (∀ x, 0 ≤ f x) →
      ∀ (g : C_c(Y, ℝ)), (∀ y, g y ∈ Icc 0 1) →
        (∫ e, cavityProductTest f g e ∂(π : Measure (X × Y))) ≤ ∫ x, f x ∂ν) :
    (π : Measure (X × Y)).fst ≤ ν := by
  have hopen (O : Set X) (hO : IsOpen O) :
      (π : Measure (X × Y)) (O ×ˢ univ) ≤ ν O := by
    rw [(hO.prod isOpen_univ).measure_eq_iSup_isCompact]
    refine iSup_le fun K ↦ iSup_le fun hKO ↦ iSup_le fun hK ↦ ?_
    have hx : Prod.fst '' K ⊆ O := by
      rintro x ⟨e, he, rfl⟩
      exact (hKO he).1
    obtain ⟨f, hfK, hfcompact, hfO, hfb⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen (hK.image continuous_fst) hO hx
    obtain ⟨g, hgK, hgcompact, _hgU, hgb⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen (hK.image continuous_snd)
        isOpen_univ (subset_univ _)
    let f' : C_c(X, ℝ) := ⟨f, hasCompactSupport_def.mpr hfcompact⟩
    let g' : C_c(Y, ℝ) := ⟨g, hasCompactSupport_def.mpr hgcompact⟩
    calc
      (π : Measure (X × Y)) K ≤
          ENNReal.ofReal (∫ e, cavityProductTest f' g' e ∂(π : Measure (X × Y))) := by
        apply (cavityProductTest f' g').integrable.measure_le_integral
        · exact .of_forall fun e ↦ mul_nonneg (hfb e.1).1 (hgb e.2).1
        · intro e he
          change 1 ≤ f e.1 * g e.2
          rw [hfK (mem_image_of_mem _ he), hgK (mem_image_of_mem _ he)]
          norm_num
      _ ≤ ENNReal.ofReal (∫ x, f' x ∂ν) :=
        ENNReal.ofReal_le_ofReal (h f' (fun x ↦ (hfb x).1) g' hgb)
      _ ≤ ν O := by
        apply integral_le_measure (fun x _ ↦ (hfb x).2)
        intro x hx
        have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hm ↦ hx (hfO hm))
        exact hz.le
  intro B
  calc
    (π : Measure (X × Y)).fst B ≤
        ⨅ (O : Set X) (_ : B ⊆ O) (_ : IsOpen O), ν O := by
      refine le_iInf fun O ↦ le_iInf fun hBO ↦ le_iInf fun hO ↦ ?_
      calc
        (π : Measure (X × Y)).fst B ≤ (π : Measure (X × Y)).fst O := measure_mono hBO
        _ = (π : Measure (X × Y)) (O ×ˢ univ) := by
          rw [Measure.fst, Measure.map_apply measurable_fst hO.measurableSet]
          congr 1
          ext e
          simp
        _ ≤ ν O := hopen O hO
    _ = ν B := B.measure_eq_iInf_isOpen ν |>.symm

/-- The corresponding compact product tests control the complete target
marginal by interchanging the original endpoints. -/
theorem snd_le_of_compact_product_tests
    (π : LocalFiniteMeasure (X × Y)) (ν : Measure Y) [ν.OuterRegular]
    (h : ∀ (f : C_c(Y, ℝ)), (∀ y, 0 ≤ f y) →
      ∀ (g : C_c(X, ℝ)), (∀ x, g x ∈ Icc 0 1) →
        (∫ e, cavityProductTest g f e ∂(π : Measure (X × Y))) ≤ ∫ y, f y ∂ν) :
    (π : Measure (X × Y)).snd ≤ ν := by
  let σ : LocalFiniteMeasure (Y × X) :=
    ⟨(π : Measure (X × Y)).map Prod.swap,
      Measure.IsFiniteMeasureOnCompacts.map (π : Measure (X × Y)) (Homeomorph.prodComm X Y)⟩
  have hs : (σ : Measure (Y × X)).fst ≤ ν := by
    apply fst_le_of_compact_product_tests σ ν
    intro f hf g hg
    change (∫ e, cavityProductTest f g e
      ∂((π : Measure (X × Y)).map Prod.swap)) ≤ _
    rw [integral_map (f := fun e : Y × X ↦ cavityProductTest f g e)
      measurable_swap.aemeasurable
      (cavityProductTest f g).continuous.aestronglyMeasurable]
    have heq : (fun e : X × Y ↦ cavityProductTest f g (Prod.swap e)) =
        fun e ↦ cavityProductTest g f e := by
      funext e
      exact mul_comm _ _
    rw [heq]
    exact h f hf g hg
  simpa only [σ, Measure.fst_map_swap] using hs

end OTSelector.Probability

end
end
