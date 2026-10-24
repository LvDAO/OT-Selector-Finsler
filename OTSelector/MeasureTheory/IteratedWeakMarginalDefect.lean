import OTSelector.MeasureTheory.CompactProductMarginalTests
import OTSelector.MeasureTheory.LimitMarginalDefect
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedMarginalDefect.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedMarginalDefect`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakMarginalDefect

## Lemma skeleton

* **Conditions:** Separate inner sample and outer approximation weak limits, continuous compact discrepancy tests, vanishing finite-stage defects and cutoff tails, with a possibly nonzero fixed core-accuracy error.
* **Objects:** Expected full marginal-test defects after the first limits and exact common marginals only after the independent core-accuracy limit.
* **Proof detail:** Apply nonnegative Portmanteau at each weak limit, remove cutoffs by Fatou/DCT using limiting marginal local finiteness, preserve the fixed accuracy term, then let that accuracy vanish on the determining tests.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=101): Section 3A, Exercise 17(b), p. 86 (Fatou’s lemma).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=107): Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47): Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.

Source relation (composition): Iterated limiting assembly retaining the order of limits; core error is not discarded during the sample or atlas limit.
-/

/-!
# Separate transport, atlas, and core-accuracy limits

The first two weak limits retain a quantitative fixed-core error.  Compact
cutoffs then recover expected full marginal-test defects.  Only the independent
core-accuracy limit removes the original discarded physical source mass.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section IteratedWeak
variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [HasOuterApproxClosed Z]

/-- A finite initial segment does not affect the weak-limit defect bound. -/
theorem lintegral_abs_le_of_weak_eventual_bound_vanishing_defect
    (Q : ProbabilityMeasure Z) (P : ℕ → ProbabilityMeasure Z)
    (hweak : Tendsto P atTop (𝓝 Q)) (H : Z → ℝ) (hH : Continuous H)
    (tail : ℝ≥0∞) (defect : ℕ → ℝ≥0∞) (hdefect : Tendsto defect atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      (∫⁻ z, ENNReal.ofReal |H z| ∂(P n : Measure Z)) ≤ tail + defect n) :
    (∫⁻ z, ENNReal.ofReal |H z| ∂(Q : Measure Z)) ≤ tail := by
  have hlo : (∫⁻ z, ENNReal.ofReal |H z| ∂(Q : Measure Z)) ≤
      atTop.liminf (fun n ↦ ∫⁻ z, ENNReal.ofReal |H z| ∂(P n : Measure Z)) :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      hH.abs (fun _ ↦ abs_nonneg _) (fun U hU ↦
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU)
  have hlim : Tendsto (fun n ↦ tail + defect n) atTop (𝓝 tail) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hdefect)
  exact hlo.trans ((liminf_le_liminf hbound).trans_eq hlim.liminf_eq)

/-- The original transport subsequence is taken at each fixed atlas index;
the atlas subsequence is taken afterward.  Its fixed-core accuracy error remains. -/
theorem lintegral_abs_le_of_iterated_weak_bound_vanishing_defect
    (R : ProbabilityMeasure Z) (Q : ℕ → ProbabilityMeasure Z)
    (P : ℕ → ℕ → ProbabilityMeasure Z)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ k, Tendsto (fun n ↦ P k (φ k n)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun l ↦ Q (ψ l)) atTop (𝓝 R))
    (H : Z → ℝ) (hH : Continuous H) (tail accuracy : ℝ≥0∞)
    (defect : ℕ → ℕ → ℝ≥0∞)
    (hdefect : ∀ k, Tendsto (defect k) atTop (𝓝 0))
    (hbound : ∀ k, ∀ᶠ N in atTop,
      (∫⁻ z, ENNReal.ofReal |H z| ∂(P k N : Measure Z)) ≤
        tail + defect k N + accuracy) :
    (∫⁻ z, ENNReal.ofReal |H z| ∂(R : Measure Z)) ≤ tail + accuracy := by
  have hQ (k : ℕ) : (∫⁻ z, ENNReal.ofReal |H z| ∂(Q k : Measure Z)) ≤
      tail + accuracy := by
    apply lintegral_abs_le_of_weak_eventual_bound_vanishing_defect (Q k)
      (fun n ↦ P k (φ k n)) (hinner k) H hH (tail + accuracy)
      (fun n ↦ defect k (φ k n)) ((hdefect k).comp (hφ k))
    filter_upwards [(hφ k).eventually (hbound k)] with n hn
    simpa only [add_assoc, add_comm, add_left_comm] using hn
  exact lintegral_abs_le_of_weak_uniform_bound R (fun l ↦ Q (ψ l)) houter H hH
    (tail + accuracy) (fun l ↦ hQ (ψ l))

end IteratedWeak

section Cutoff
variable {Z : Type*} [MeasurableSpace Z]

/-- Fatou removes the compact cutoff while preserving the fixed-core error. -/
theorem lintegral_abs_le_of_cutoff_bounds
    (μ : Measure Z) (H : ℕ → Z → ℝ) (hH : ∀ j, Measurable (H j))
    (Hlim : Z → ℝ)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun j ↦ H j z) atTop (𝓝 (Hlim z)))
    (tail : ℕ → ℝ≥0∞) (htail : Tendsto tail atTop (𝓝 0)) (accuracy : ℝ≥0∞)
    (hbound : ∀ j, (∫⁻ z, ENNReal.ofReal |H j z| ∂μ) ≤ tail j + accuracy) :
    (∫⁻ z, ENNReal.ofReal |Hlim z| ∂μ) ≤ accuracy := by
  have hlim' : ∀ᵐ z ∂μ, Tendsto (fun j ↦ ENNReal.ofReal |H j z|)
      atTop (𝓝 (ENNReal.ofReal |Hlim z|)) :=
    hlim.mono fun z hz ↦ ENNReal.continuous_ofReal.continuousAt.tendsto.comp hz.abs
  have herr : Tendsto (fun j ↦ tail j + accuracy) atTop (𝓝 accuracy) := by
    simpa only [zero_add] using htail.add tendsto_const_nhds
  calc
    _ = ∫⁻ z, atTop.liminf (fun j ↦ ENNReal.ofReal |H j z|) ∂μ :=
      lintegral_congr_ae (hlim'.mono fun _ hz ↦ hz.liminf_eq.symm)
    _ ≤ atTop.liminf (fun j ↦ ∫⁻ z, ENNReal.ofReal |H j z| ∂μ) :=
      lintegral_liminf_le (fun j ↦
        ((continuous_abs : Continuous (fun x : ℝ ↦ |x|)).measurable.comp (hH j)).ennreal_ofReal)
    _ ≤ accuracy := (liminf_le_liminf (Eventually.of_forall hbound)).trans_eq herr.liminf_eq

end Cutoff

section Marginals
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
  [SecondCountableTopology Y]

local instance iteratedMarginalPlanPolish : PolishSpace (LocalFiniteMeasure (X × Y)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Original fixed-core errors survive the separate transport and atlas weak
limits as an expected full source-test defect, under actual outer local finiteness. -/
theorem lintegral_full_source_test_defect_le_of_iterated_weak_bounds
    (R : ProbabilityMeasure (CavityLocalScene X Y))
    (Q : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (P : ℕ → ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ k, Tendsto (fun n ↦ P k (φ k n)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun l ↦ Q (ψ l)) atTop (𝓝 R))
    (f : C_c(X, ℝ)) (K : CompactExhaustion Y)
    (hlocal : ∀ᵐ scene ∂(R : Measure (CavityLocalScene X Y)),
      IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).fst ∧
      IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).fst)
    (tail : ℕ → ℝ≥0∞) (htail : Tendsto tail atTop (𝓝 0))
    (accuracy : ℝ≥0∞) (defect : ℕ → ℕ → ℕ → ℝ≥0∞)
    (hdefect : ∀ j k, Tendsto (defect j k) atTop (𝓝 0))
    (hbound : ∀ j k, ∀ᶠ N in atTop,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K j)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K j))|
        ∂(P k N : Measure (CavityLocalScene X Y))) ≤ tail j + defect j k N + accuracy) :
    (∫⁻ scene : CavityLocalScene X Y, ENNReal.ofReal
      |(∫ e, f e.1 ∂(scene.1 : Measure (X × Y))) -
        ∫ e, f e.1 ∂(scene.2 : Measure (X × Y))|
      ∂(R : Measure (CavityLocalScene X Y))) ≤ accuracy := by
  let H := fun j (scene : CavityLocalScene X Y) ↦
    LocalFiniteMeasure.testIntegral scene.1
      (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K j)) -
    LocalFiniteMeasure.testIntegral scene.2
      (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K j))
  have hH (j : ℕ) : Continuous (H j) :=
    ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)
  refine lintegral_abs_le_of_cutoff_bounds (R : Measure (CavityLocalScene X Y)) H
    (fun j ↦ (hH j).measurable) _ ?_ tail htail accuracy ?_
  · filter_upwards [hlocal] with scene hs
    let : IsFiniteMeasureOnCompacts ((scene.1 : Measure (X × Y)).map Prod.fst) := hs.1
    let : IsFiniteMeasureOnCompacts ((scene.2 : Measure (X × Y)).map Prod.fst) := hs.2
    have hf₀ : Integrable (fun e : X × Y ↦ f e.1) (scene.1 : Measure (X × Y)) :=
      (integrable_map_measure (f := Prod.fst) (g := fun x ↦ f x)
        f.continuous.aestronglyMeasurable measurable_fst.aemeasurable).mp f.integrable
    have hf₁ : Integrable (fun e : X × Y ↦ f e.1) (scene.2 : Measure (X × Y)) :=
      (integrable_map_measure (f := Prod.fst) (g := fun x ↦ f x)
        f.continuous.aestronglyMeasurable measurable_fst.aemeasurable).mp f.integrable
    exact (tendsto_integral_cavityProductTest_cutoff _ f K hf₀).sub
      (tendsto_integral_cavityProductTest_cutoff _ f K hf₁)
  · intro j
    exact lintegral_abs_le_of_iterated_weak_bound_vanishing_defect R Q P φ hφ ψ
      hinner houter (H j) (hH j) (tail j) accuracy (defect j) (hdefect j) (hbound j)

/-- The same iterated closure for the actual full target tests.  No equality of
restricted finite-stage target columns is required. -/
theorem lintegral_full_target_test_defect_le_of_iterated_weak_bounds
    (R : ProbabilityMeasure (CavityLocalScene X Y))
    (Q : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (P : ℕ → ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop) (ψ : ℕ → ℕ)
    (hinner : ∀ k, Tendsto (fun n ↦ P k (φ k n)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun l ↦ Q (ψ l)) atTop (𝓝 R))
    (f : C_c(Y, ℝ)) (K : CompactExhaustion X)
    (hlocal : ∀ᵐ scene ∂(R : Measure (CavityLocalScene X Y)),
      IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).snd ∧
      IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).snd)
    (tail : ℕ → ℝ≥0∞) (htail : Tendsto tail atTop (𝓝 0))
    (accuracy : ℝ≥0∞) (defect : ℕ → ℕ → ℕ → ℝ≥0∞)
    (hdefect : ∀ j k, Tendsto (defect j k) atTop (𝓝 0))
    (hbound : ∀ j k, ∀ᶠ N in atTop,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff K j) f) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff K j) f)|
        ∂(P k N : Measure (CavityLocalScene X Y))) ≤ tail j + defect j k N + accuracy) :
    (∫⁻ scene : CavityLocalScene X Y, ENNReal.ofReal
      |(∫ e, f e.2 ∂(scene.1 : Measure (X × Y))) -
        ∫ e, f e.2 ∂(scene.2 : Measure (X × Y))|
      ∂(R : Measure (CavityLocalScene X Y))) ≤ accuracy := by
  let H := fun j (scene : CavityLocalScene X Y) ↦
    LocalFiniteMeasure.testIntegral scene.1
      (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff K j) f) -
    LocalFiniteMeasure.testIntegral scene.2
      (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff K j) f)
  have hH (j : ℕ) : Continuous (H j) :=
    ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)
  refine lintegral_abs_le_of_cutoff_bounds (R : Measure (CavityLocalScene X Y)) H
    (fun j ↦ (hH j).measurable) _ ?_ tail htail accuracy ?_
  · filter_upwards [hlocal] with scene hs
    let : IsFiniteMeasureOnCompacts ((scene.1 : Measure (X × Y)).map Prod.snd) := hs.1
    let : IsFiniteMeasureOnCompacts ((scene.2 : Measure (X × Y)).map Prod.snd) := hs.2
    have hf₀ : Integrable (fun e : X × Y ↦ f e.2) (scene.1 : Measure (X × Y)) :=
      (integrable_map_measure (f := Prod.snd) (g := fun y ↦ f y)
        f.continuous.aestronglyMeasurable measurable_snd.aemeasurable).mp f.integrable
    have hf₁ : Integrable (fun e : X × Y ↦ f e.2) (scene.2 : Measure (X × Y)) :=
      (integrable_map_measure (f := Prod.snd) (g := fun y ↦ f y)
        f.continuous.aestronglyMeasurable measurable_snd.aemeasurable).mp f.integrable
    exact (tendsto_integral_cavityProductTest_source_cutoff _ f K hf₀).sub
      (tendsto_integral_cavityProductTest_source_cutoff _ f K hf₁)
  · intro j
    exact lintegral_abs_le_of_iterated_weak_bound_vanishing_defect R Q P φ hφ ψ
      hinner houter (H j) (hH j) (tail j) accuracy (defect j) (hdefect j) (hbound j)


/-- The independent core-accuracy limit turns the surviving compact-test
estimates into exact full source and target marginals.  This limit does not
change the already completed transport or atlas subsequences. -/
theorem ae_common_marginals_of_weak_core_accuracy_cutoff_bounds
    (S : ProbabilityMeasure (CavityLocalScene X Y))
    (R : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (χ : ℕ → ℕ) (hχ : Tendsto χ atTop atTop)
    (hweak : Tendsto (fun l ↦ R (χ l)) atTop (𝓝 S))
    (KX : CompactExhaustion X) (KY : CompactExhaustion Y)
    (targetCutoff : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion Y)
    (sourceCutoff : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion X)
    (hlocal : ∀ᵐ scene ∂(S : Measure (CavityLocalScene X Y)),
      (IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).fst ∧
        IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).fst) ∧
      (IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).snd ∧
        IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).snd))
    (sourceTail targetTail : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (hsourceTail : ∀ i, Tendsto (sourceTail i) atTop (𝓝 0))
    (htargetTail : ∀ i, Tendsto (targetTail i) atTop (𝓝 0))
    (sourceAccuracy targetAccuracy : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (hsourceAccuracy : ∀ i, Tendsto (sourceAccuracy i) atTop (𝓝 0))
    (htargetAccuracy : ∀ i, Tendsto (targetAccuracy i) atTop (𝓝 0))
    (hsourceBound : ∀ i j c,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (targetCutoff i) j)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (targetCutoff i) j))|
        ∂(R c : Measure (CavityLocalScene X Y))) ≤ sourceTail i j + sourceAccuracy i c)
    (htargetBound : ∀ i j c,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (sourceCutoff i) j)
            (LocalFiniteMeasure.separatingTest KY i)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (sourceCutoff i) j)
            (LocalFiniteMeasure.separatingTest KY i))|
        ∂(R c : Measure (CavityLocalScene X Y))) ≤ targetTail i j + targetAccuracy i c) :
    ∀ᵐ scene ∂(S : Measure (CavityLocalScene X Y)),
      (scene.1 : Measure (X × Y)).fst = (scene.2 : Measure (X × Y)).fst ∧
      (scene.1 : Measure (X × Y)).snd = (scene.2 : Measure (X × Y)).snd := by
  have hs := ae_common_source_marginal_of_weak_tail_and_vanishing_discard
    S (fun l ↦ R (χ l)) hweak KX targetCutoff (hlocal.mono fun _ hs ↦ hs.1)
    sourceTail hsourceTail (fun i _j l ↦ sourceAccuracy i (χ l))
    (fun i _j ↦ (hsourceAccuracy i).comp hχ)
    (fun i j l ↦ hsourceBound i j (χ l))
  have ht := ae_common_target_marginal_of_weak_tail_and_vanishing_discard
    S (fun l ↦ R (χ l)) hweak KY sourceCutoff (hlocal.mono fun _ hs ↦ hs.2)
    targetTail htargetTail (fun i _j l ↦ targetAccuracy i (χ l))
    (fun i _j ↦ (htargetAccuracy i).comp hχ)
    (fun i j l ↦ htargetBound i j (χ l))
  exact hs.and ht

end Marginals
end OTSelector.Reconstruction

end
end
