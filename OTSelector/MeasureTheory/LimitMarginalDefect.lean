import OTSelector.MeasureTheory.CompactProductMarginalTests
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitMarginalDefect.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitMarginalDefect`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.LimitMarginalDefect

## Lemma skeleton

* **Conditions:** Weakly convergent plan-pair laws, finite-stage compact marginal-test defects tending to zero, cutoff tails tending to zero and local finiteness of limiting marginals.
* **Objects:** Exact almost-everywhere equality of whole limiting source/target marginals and deterministic restriction-discard identities.
* **Proof detail:** Bound product-test discrepancies by marginal defects plus the actual escape masses. Portmanteau transfers each continuous nonnegative discrepancy; remove the countable test exceptions, send cutoffs to infinity and use compact-test measure determination.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47): Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=107): Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).

Source relation (composition): Two-stage defect/cutoff assembly with explicit local finiteness; named Polish instance only registers the established carrier topology.
-/

/-!
# Exact limiting marginals from actual cutoff and discard errors

Actual finite marginal-test defects and escape masses control compact product
tests. Vanishing finite-stage defects and cutoff tails pass through weak laws
to exact full source or target marginal equality.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Deterministic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- An actual finite marginal-test discrepancy and the two escape tails bound
the compact product-test discrepancy.  Exact prelimit marginal equality is not
needed; the discrepancy is the original untruncated test difference itself. -/
theorem abs_product_tests_sub_le_source_defect_and_tails
    (π₀ π₁ : Measure (X × Y)) (f : C_c(X, ℝ)) (g : C_c(Y, ℝ))
    (hf₀ : Integrable (fun e : X × Y ↦ f e.1) π₀)
    (hf₁ : Integrable (fun e : X × Y ↦ f e.1) π₁)
    (hg : ∀ y, g y ∈ Icc 0 1) (K : Set Y) (hgK : EqOn g 1 K)
    (htail₀ : π₀ (tsupport f ×ˢ Kᶜ) < ⊤)
    (htail₁ : π₁ (tsupport f ×ˢ Kᶜ) < ⊤) :
    |(∫ e, cavityProductTest f g e ∂π₀) - ∫ e, cavityProductTest f g e ∂π₁| ≤
      |(∫ e, f e.1 ∂π₀) - ∫ e, f e.1 ∂π₁| +
        ‖f.toBoundedContinuousFunction‖ *
          (π₀.real (tsupport f ×ˢ Kᶜ) + π₁.real (tsupport f ×ˢ Kᶜ)) := by
  let S₀ := ∫ e : X × Y, f e.1 ∂π₀
  let S₁ := ∫ e : X × Y, f e.1 ∂π₁
  let T₀ := ∫ e, cavityProductTest f g e ∂π₀
  let T₁ := ∫ e, cavityProductTest f g e ∂π₁
  have h₀ := abs_integral_source_sub_product_le_tail π₀ f g hf₀ hg K hgK htail₀
  have h₁ := abs_integral_source_sub_product_le_tail π₁ f g hf₁ hg K hgK htail₁
  change |S₀ - T₀| ≤ _ at h₀
  change |S₁ - T₁| ≤ _ at h₁
  change |T₀ - T₁| ≤ |S₀ - S₁| + _
  have ht := (abs_sub_le T₀ S₀ T₁).trans
    (add_le_add le_rfl (abs_sub_le S₀ S₁ T₁))
  rw [abs_sub_comm T₀ S₀] at ht
  rw [mul_add]
  linarith

end Deterministic

section WeakBound

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [HasOuterApproxClosed Z]

/-- A vanishing original finite-stage defect disappears when a continuous
compact-test bound is passed through the actual weak convergence. -/
theorem lintegral_abs_le_of_weak_bound_vanishing_defect
    (Q : ProbabilityMeasure Z) (Pn : ℕ → ProbabilityMeasure Z)
    (hweak : Tendsto Pn atTop (𝓝 Q)) (H : Z → ℝ) (hH : Continuous H)
    (tail : ℝ≥0∞) (defect : ℕ → ℝ≥0∞) (hdefect : Tendsto defect atTop (𝓝 0))
    (hbound : ∀ n, (∫⁻ z, ENNReal.ofReal |H z| ∂(Pn n : Measure Z)) ≤ tail + defect n) :
    (∫⁻ z, ENNReal.ofReal |H z| ∂(Q : Measure Z)) ≤ tail := by
  have hlo : (∫⁻ z, ENNReal.ofReal |H z| ∂(Q : Measure Z)) ≤
      atTop.liminf (fun n ↦ ∫⁻ z, ENNReal.ofReal |H z| ∂(Pn n : Measure Z)) :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      hH.abs (fun _ ↦ abs_nonneg _) (fun U hU ↦
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU)
  have hlim : Tendsto (fun n ↦ tail + defect n) atTop (𝓝 tail) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hdefect)
  exact hlo.trans ((liminf_le_liminf (Eventually.of_forall hbound)).trans_eq hlim.liminf_eq)

end WeakBound

section Marginal

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
  [SecondCountableTopology Y]

local instance exactMarginalScratchLocalInst : PolishSpace (LocalFiniteMeasure (X × Y)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Actual cutoff tails vanishing with the cutoff and actual finite-stage
discard defects vanishing along the original sequence suffice for exact full
source marginal equality in the weak limit.  The prelimit marginal projections
need not be equal. -/
theorem ae_common_source_marginal_of_weak_tail_and_vanishing_discard
    (Q : ProbabilityMeasure (CavityLocalScene X Y))
    (Pn : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (hweak : Tendsto Pn atTop (𝓝 Q))
    (KX : CompactExhaustion X) (KY : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion Y)
    (hlocal : ∀ᵐ scene ∂(Q : Measure (CavityLocalScene X Y)),
      IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).fst ∧
      IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).fst)
    (tail : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (htail : ∀ i, Tendsto (tail i) atTop (𝓝 0))
    (discard : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℕ → ℝ≥0∞)
    (hdiscard : ∀ i R, Tendsto (discard i R) atTop (𝓝 0))
    (hbound : ∀ i R n,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (KY i) R)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (KY i) R))|
          ∂(Pn n : Measure (CavityLocalScene X Y))) ≤ tail i R + discard i R n) :
    ∀ᵐ scene ∂(Q : Measure (CavityLocalScene X Y)),
      (scene.1 : Measure (X × Y)).fst = (scene.2 : Measure (X × Y)).fst := by
  have hboundQ (i : ℕ ⊕ (ℕ × ℕ)) (R : ℕ) :
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (KY i) R)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (KY i) R))|
          ∂(Q : Measure (CavityLocalScene X Y))) ≤ tail i R := by
    apply lintegral_abs_le_of_weak_bound_vanishing_defect Q Pn hweak _ _
      (tail i R) (discard i R) (hdiscard i R) (hbound i R)
    exact ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)
  exact ae_common_source_marginal_of_weak_cutoff_errors Q (fun _ ↦ Q) tendsto_const_nhds
    KX KY hlocal tail htail (fun i R _ ↦ hboundQ i R)

/-- The source-cutoff approximation of a target test is the transpose of the
existing target-cutoff approximation of a source test. -/
theorem tendsto_integral_cavityProductTest_source_cutoff
    (π : Measure (X × Y)) (f : C_c(Y, ℝ)) (K : CompactExhaustion X)
    (hf : Integrable (fun e : X × Y ↦ f e.2) π) :
    Tendsto (fun R ↦ ∫ e, cavityProductTest (LocalFiniteMeasure.exhaustionCutoff K R) f e ∂π)
      atTop (𝓝 (∫ e, f e.2 ∂π)) := by
  have hfswap : Integrable (fun p : Y × X ↦ f p.1) (π.map Prod.swap) :=
    (integrable_map_measure (f := Prod.swap) (g := fun p : Y × X ↦ f p.1)
      (f.continuous.comp continuous_fst).aestronglyMeasurable
      measurable_swap.aemeasurable).mpr hf
  have hlim := tendsto_integral_cavityProductTest_cutoff (π.map Prod.swap) f K hfswap
  have heq (R : ℕ) :
      (∫ p, cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K R) p
        ∂π.map Prod.swap) =
      ∫ e, cavityProductTest (LocalFiniteMeasure.exhaustionCutoff K R) f e ∂π := by
    rw [integral_map (f := fun p : Y × X ↦
      cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K R) p)
      measurable_swap.aemeasurable
      (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K R)).continuous.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ ↦ mul_comm _ _
  have hread : (∫ p : Y × X, f p.1 ∂π.map Prod.swap) = ∫ e : X × Y, f e.2 ∂π :=
    integral_map measurable_swap.aemeasurable
      (f.continuous.comp continuous_fst).aestronglyMeasurable
  simpa only [heq, hread] using hlim

/-- The transposed cutoff closure preserves exact full target marginals from
the actual target-test defects and actual source escape tails.  Restricted
random target columns need not coincide at any finite stage. -/
theorem ae_common_target_marginal_of_weak_tail_and_vanishing_discard
    (Q : ProbabilityMeasure (CavityLocalScene X Y))
    (Pn : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (hweak : Tendsto Pn atTop (𝓝 Q))
    (KY : CompactExhaustion Y) (KX : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion X)
    (hlocal : ∀ᵐ scene ∂(Q : Measure (CavityLocalScene X Y)),
      IsFiniteMeasureOnCompacts (scene.1 : Measure (X × Y)).snd ∧
      IsFiniteMeasureOnCompacts (scene.2 : Measure (X × Y)).snd)
    (tail : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (htail : ∀ i, Tendsto (tail i) atTop (𝓝 0))
    (discard : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℕ → ℝ≥0∞)
    (hdiscard : ∀ i R, Tendsto (discard i R) atTop (𝓝 0))
    (hbound : ∀ i R n,
      (∫⁻ scene : CavityLocalScene X Y,
        ENNReal.ofReal |LocalFiniteMeasure.testIntegral scene.1
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (KX i) R)
            (LocalFiniteMeasure.separatingTest KY i)) -
          LocalFiniteMeasure.testIntegral scene.2
          (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (KX i) R)
            (LocalFiniteMeasure.separatingTest KY i))|
          ∂(Pn n : Measure (CavityLocalScene X Y))) ≤ tail i R + discard i R n) :
    ∀ᵐ scene ∂(Q : Measure (CavityLocalScene X Y)),
      (scene.1 : Measure (X × Y)).snd = (scene.2 : Measure (X × Y)).snd := by
  have hall : ∀ᵐ scene ∂(Q : Measure (CavityLocalScene X Y)), ∀ i : ℕ ⊕ (ℕ × ℕ),
      (∫ e, LocalFiniteMeasure.separatingTest KY i e.2 ∂(scene.1 : Measure (X × Y))) =
        ∫ e, LocalFiniteMeasure.separatingTest KY i e.2 ∂(scene.2 : Measure (X × Y)) := by
    apply ae_all_iff.mpr
    intro i
    let f := LocalFiniteMeasure.separatingTest KY i
    let H := fun R (scene : CavityLocalScene X Y) ↦
      LocalFiniteMeasure.testIntegral scene.1
        (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (KX i) R) f) -
      LocalFiniteMeasure.testIntegral scene.2
        (cavityProductTest (LocalFiniteMeasure.exhaustionCutoff (KX i) R) f)
    have hH : ∀ R, Continuous (H R) := fun _ ↦
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
        ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)
    have hb (R : ℕ) : (∫⁻ scene, ENNReal.ofReal |H R scene|
        ∂(Q : Measure (CavityLocalScene X Y))) ≤ tail i R :=
      lintegral_abs_le_of_weak_bound_vanishing_defect Q Pn hweak (H R) (hH R)
        (tail i R) (discard i R) (hdiscard i R) (hbound i R)
    have hz := ae_eq_zero_of_weak_cutoff_errors Q (fun _ ↦ Q) tendsto_const_nhds
      H hH (tail i) (htail i) (fun R _ ↦ hb R)
      (fun scene ↦ (∫ e, f e.2 ∂(scene.1 : Measure (X × Y))) -
        ∫ e, f e.2 ∂(scene.2 : Measure (X × Y))) (by
          filter_upwards [hlocal] with scene hs
          let : IsFiniteMeasureOnCompacts ((scene.1 : Measure (X × Y)).map Prod.snd) := hs.1
          let : IsFiniteMeasureOnCompacts ((scene.2 : Measure (X × Y)).map Prod.snd) := hs.2
          have hf₀ : Integrable (fun e : X × Y ↦ f e.2) (scene.1 : Measure (X × Y)) :=
            (integrable_map_measure (f := Prod.snd) (g := fun y ↦ f y)
              f.continuous.aestronglyMeasurable measurable_snd.aemeasurable).mp f.integrable
          have hf₁ : Integrable (fun e : X × Y ↦ f e.2) (scene.2 : Measure (X × Y)) :=
            (integrable_map_measure (f := Prod.snd) (g := fun y ↦ f y)
              f.continuous.aestronglyMeasurable measurable_snd.aemeasurable).mp f.integrable
          exact (tendsto_integral_cavityProductTest_source_cutoff _ f (KX i) hf₀).sub
            (tendsto_integral_cavityProductTest_source_cutoff _ f (KX i) hf₁))
    exact hz.mono fun _ h ↦ sub_eq_zero.mp h
  filter_upwards [hlocal, hall] with scene hs htests
  let μ₀ : LocalFiniteMeasure Y := ⟨(scene.1 : Measure (X × Y)).snd, hs.1⟩
  let μ₁ : LocalFiniteMeasure Y := ⟨(scene.2 : Measure (X × Y)).snd, hs.2⟩
  have heq : μ₀ = μ₁ := by
    apply LocalFiniteMeasure.separatingTestCode_injective KY
    funext i
    let f := LocalFiniteMeasure.separatingTest KY i
    change (∫ y, f y ∂(scene.1 : Measure (X × Y)).snd) =
      ∫ y, f y ∂(scene.2 : Measure (X × Y)).snd
    have h₀ := integral_map (μ := (scene.1 : Measure (X × Y))) (f := fun y ↦ f y)
      measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    have h₁ := integral_map (μ := (scene.2 : Measure (X × Y))) (f := fun y ↦ f y)
      measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    exact h₀.trans ((htests i).trans h₁.symm)
  exact congrArg (fun μ : LocalFiniteMeasure Y ↦ (μ : Measure Y)) heq

end Marginal

section SourceRestriction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- An actual source restriction has exactly the restricted original source
marginal, independently of its random target column masses. -/
theorem fst_actual_source_restriction (Γ : Measure (X × Y))
    (H : Set X) (hH : MeasurableSet H) :
    (Γ.restrict (H ×ˢ univ)).fst = Γ.fst.restrict H := by
  rw [show H ×ˢ (univ : Set Y) = Prod.fst ⁻¹' H by ext e; simp]
  change (Γ.restrict (Prod.fst ⁻¹' H)).map Prod.fst = (Γ.map Prod.fst).restrict H
  exact (Measure.restrict_map measurable_fst hH).symm

/-- The same original source marginal stays exactly equal under the same
actual source restriction. -/
theorem equal_fst_actual_source_restrictions (Γ₀ Γ₁ : Measure (X × Y))
    (hsource : Γ₀.fst = Γ₁.fst) (H : Set X) (hH : MeasurableSet H) :
    (Γ₀.restrict (H ×ˢ univ)).fst = (Γ₁.restrict (H ×ˢ univ)).fst := by
  rw [fst_actual_source_restriction Γ₀ H hH, fst_actual_source_restriction Γ₁ H hH, hsource]

variable [TopologicalSpace Y] [T2Space Y] [BorelSpace Y]

/-- A target test loses at most its supremum times the actual discarded source
mass when the original physical plan is restricted in its source. -/
theorem abs_target_integral_restrict_sub_global_le_discard
    (Γ : Measure (X × Y)) [IsFiniteMeasure Γ]
    (H : Set X) (hH : MeasurableSet H) (f : C_c(Y, ℝ)) :
    |(∫ e, f e.2 ∂Γ.restrict (H ×ˢ univ)) - ∫ e, f e.2 ∂Γ| ≤
      ‖f.toBoundedContinuousFunction‖ * Γ.real (Hᶜ ×ˢ univ) := by
  have hf : Integrable (fun e : X × Y ↦ f e.2) Γ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (Eventually.of_forall fun e ↦
        f.toBoundedContinuousFunction.norm_coe_le_norm e.2)
  have hcomp : (H ×ˢ (univ : Set Y))ᶜ = Hᶜ ×ˢ univ := by ext e; simp
  have hsplit := integral_add_compl (hH.prod (MeasurableSet.univ : MeasurableSet (univ : Set Y))) hf
  rw [hcomp] at hsplit
  have hb : |∫ e in Hᶜ ×ˢ univ, f e.2 ∂Γ| ≤
      ‖f.toBoundedContinuousFunction‖ * Γ.real (Hᶜ ×ˢ univ) := by
    simpa only [Real.norm_eq_abs] using
      (norm_setIntegral_le_of_norm_le_const_ae (μ := Γ) (s := Hᶜ ×ˢ univ)
        (f := fun e : X × Y ↦ f e.2) (measure_lt_top _ _)
        (Eventually.of_forall fun e ↦ f.toBoundedContinuousFunction.norm_coe_le_norm e.2))
  have heq : (∫ e, f e.2 ∂Γ.restrict (H ×ˢ univ)) - (∫ e, f e.2 ∂Γ) =
      -(∫ e in Hᶜ ×ˢ univ, f e.2 ∂Γ) := by linarith [hsplit]
  rw [heq, abs_neg]
  exact hb

/-- Common original global target marginals yield an explicit bound on the
actual restricted target-test discrepancy by the two discarded source masses.
The restricted random columns are used exactly as realized. -/
theorem abs_target_integrals_source_restrict_sub_le_common_global_target_discard
    (Γ₀ Γ₁ : Measure (X × Y)) [IsFiniteMeasure Γ₀] [IsFiniteMeasure Γ₁]
    (htarget : Γ₀.snd = Γ₁.snd) (H : Set X) (hH : MeasurableSet H) (f : C_c(Y, ℝ)) :
    |(∫ e, f e.2 ∂Γ₀.restrict (H ×ˢ univ)) -
      ∫ e, f e.2 ∂Γ₁.restrict (H ×ˢ univ)| ≤
      ‖f.toBoundedContinuousFunction‖ *
        (Γ₀.real (Hᶜ ×ˢ univ) + Γ₁.real (Hᶜ ×ˢ univ)) := by
  have hfull : (∫ e : X × Y, f e.2 ∂Γ₀) = ∫ e : X × Y, f e.2 ∂Γ₁ := by
    have h₀ := integral_map (μ := Γ₀) (f := fun y ↦ f y)
      measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    have h₁ := integral_map (μ := Γ₁) (f := fun y ↦ f y)
      measurable_snd.aemeasurable f.continuous.aestronglyMeasurable
    exact h₀.symm.trans ((congrArg (fun μ : Measure Y ↦ ∫ y, f y ∂μ) htarget).trans h₁)
  have h₀ := abs_target_integral_restrict_sub_global_le_discard Γ₀ H hH f
  have h₁ := abs_target_integral_restrict_sub_global_le_discard Γ₁ H hH f
  rw [← hfull] at h₁
  have htri := abs_sub_le (∫ e, f e.2 ∂Γ₀.restrict (H ×ˢ univ))
    (∫ e : X × Y, f e.2 ∂Γ₀) (∫ e, f e.2 ∂Γ₁.restrict (H ×ˢ univ))
  rw [abs_sub_comm (∫ e : X × Y, f e.2 ∂Γ₀)] at htri
  rw [mul_add]
  linarith

end SourceRestriction
end OTSelector.Reconstruction

end
end
