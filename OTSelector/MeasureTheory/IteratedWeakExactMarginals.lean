import OTSelector.MeasureTheory.CompactProductMarginalTests
import OTSelector.MeasureTheory.IteratedWeakMarginalDefect
import OTSelector.MeasureTheory.LimitMarginalDefect
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedExactMarginals.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedExactMarginals`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakExactMarginals

## Lemma skeleton

* **Conditions:** Separate sample and outer weak limits, eventual compact cutoff discrepancy estimates with vanishing sample errors and vanishing cutoff tails, and locally finite limiting marginals.
* **Objects:** Exact equality of full source and target marginals almost surely in the final scene.
* **Proof detail:** Apply the iterated discrepancy bounds to the countable separating compact tests with zero core error, remove cutoffs and invoke compact-test uniqueness on one common conull event.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=101): Section 3A, Exercise 17(b), p. 86 (Fatou’s lemma).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47): Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.

Source relation (composition): Exact-marginal specialization of the iterated weak/cutoff assembly; a named Polish instance is a typeclass adapter.
-/

/-!
# Exact full marginals after separate sample and tilt limits
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Marginals
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
  [SecondCountableTopology Y]

local instance iteratedExactMarginalPlanPolish : PolishSpace (LocalFiniteMeasure (X × Y)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Separate sample and tilt weak limits retain exact full marginals once
actual compact cutoff errors vanish. The underlying scene is fixed throughout;
only auxiliary estimates are chosen when constructing the cutoff errors. -/
theorem ae_common_marginals_of_iterated_weak_eventual_cutoff_bounds
    (R : ProbabilityMeasure (CavityLocalScene X Y))
    (Q : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (P : ℕ → ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ k, Tendsto (fun n ↦ P k (φ k n)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun l ↦ Q (ψ l)) atTop (𝓝 R))
    (KX : CompactExhaustion X) (KY : CompactExhaustion Y)
    (targetCutoff : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion Y)
    (sourceCutoff : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion X)
    (hlocal : ∀ᵐ scene ∂(R : Measure (CavityLocalScene X Y)),
      (IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).fst ∧
        IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).fst) ∧
      (IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).snd ∧
        IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).snd))
    (sourceTail targetTail : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (hsourceTail : ∀ i, Tendsto (sourceTail i) atTop (𝓝 0))
    (htargetTail : ∀ i, Tendsto (targetTail i) atTop (𝓝 0))
    (sourceDefect targetDefect : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℕ → ℕ → ℝ≥0∞)
    (hsourceDefect : ∀ i j k, Tendsto (sourceDefect i j k) atTop (𝓝 0))
    (htargetDefect : ∀ i j k, Tendsto (targetDefect i j k) atTop (𝓝 0))
    (hsourceBound : ∀ i j k, ∀ᶠ N in atTop,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (targetCutoff i) j)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (targetCutoff i) j))|
        ∂(P k N : Measure (CavityLocalScene X Y))) ≤ sourceTail i j + sourceDefect i j k N)
    (htargetBound : ∀ i j k, ∀ᶠ N in atTop,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (sourceCutoff i) j)
            (LocalFiniteMeasure.separatingTest KY i)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (sourceCutoff i) j)
            (LocalFiniteMeasure.separatingTest KY i))|
        ∂(P k N : Measure (CavityLocalScene X Y))) ≤ targetTail i j + targetDefect i j k N) :
    ∀ᵐ scene ∂(R : Measure (CavityLocalScene X Y)),
      (scene.1 : Measure (X × Y)).fst = (scene.2 : Measure (X × Y)).fst ∧
      (scene.1 : Measure (X × Y)).snd = (scene.2 : Measure (X × Y)).snd := by
  have hs (i : ℕ ⊕ (ℕ × ℕ)) (j : ℕ) :
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (targetCutoff i) j)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (targetCutoff i) j))|
        ∂(R : Measure (CavityLocalScene X Y))) ≤ sourceTail i j := by
    simpa only [add_zero, Function.comp_apply, Pi.sub_apply] using
      lintegral_abs_le_of_iterated_weak_bound_vanishing_defect R Q P φ hφ ψ hinner houter
        _ (((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
          ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd))
        (sourceTail i j) 0 (sourceDefect i j) (hsourceDefect i j)
        (by simpa only [add_zero, Function.comp_apply, Pi.sub_apply] using hsourceBound i j)
  have ht (i : ℕ ⊕ (ℕ × ℕ)) (j : ℕ) :
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (sourceCutoff i) j)
            (LocalFiniteMeasure.separatingTest KY i)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (sourceCutoff i) j)
            (LocalFiniteMeasure.separatingTest KY i))|
        ∂(R : Measure (CavityLocalScene X Y))) ≤ targetTail i j := by
    simpa only [add_zero, Function.comp_apply, Pi.sub_apply] using
      lintegral_abs_le_of_iterated_weak_bound_vanishing_defect R Q P φ hφ ψ hinner houter
        _ (((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
          ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd))
        (targetTail i j) 0 (targetDefect i j) (htargetDefect i j)
        (by simpa only [add_zero, Function.comp_apply, Pi.sub_apply] using htargetBound i j)
  have hs' := ae_common_source_marginal_of_weak_tail_and_vanishing_discard
    R (fun _ ↦ R) tendsto_const_nhds KX targetCutoff (hlocal.mono fun _ h ↦ h.1)
    sourceTail hsourceTail (fun _ _ _ ↦ 0) (fun _ _ ↦ tendsto_const_nhds)
    (fun i j _ ↦ by simpa only [add_zero] using hs i j)
  have ht' := ae_common_target_marginal_of_weak_tail_and_vanishing_discard
    R (fun _ ↦ R) tendsto_const_nhds KY sourceCutoff (hlocal.mono fun _ h ↦ h.2)
    targetTail htargetTail (fun _ _ _ ↦ 0) (fun _ _ ↦ tendsto_const_nhds)
    (fun i j _ ↦ by simpa only [add_zero] using ht i j)
  exact hs'.and ht'

end Marginals
end OTSelector.Reconstruction

end
end
