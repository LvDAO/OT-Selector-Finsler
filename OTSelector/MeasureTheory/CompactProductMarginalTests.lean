import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
import OTSelector.MeasureTheory.LocalFiniteMeasurePair
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish

/-!
## Lemma skeleton

* **Conditions:** Compact source tests, partner cutoffs, tail integrability and a weak law limit.
* **Objects:** Product tests and errors identifying a common limiting marginal.
* **Proof detail:** Bound cutoff error by omitted partner mass, pass continuous test bounds through weak convergence, then remove cutoffs.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47

**Relationship to the sources:** Historical cavity-named definitions are generic product-measure constructions. The exact marginal closure package is proved here from Portmanteau, Fatou/DCT and test extensionality.
-/

/-!
# Compact tests and the actual source-marginal cutoff error

The untruncated source test is compared with a genuine compact product test.
Only mass leaving the retained target set contributes to the error.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]

/-- An actual compact product test for vague convergence of transport plans. -/
def cavityProductTest (f : C_c(X, ℝ)) (g : C_c(Y, ℝ)) : C_c(X × Y, ℝ) where
  toFun e := f e.1 * g e.2
  continuous_toFun := (f.continuous.comp continuous_fst).mul
    (g.continuous.comp continuous_snd)
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact
    (f.hasCompactSupport.prod g.hasCompactSupport) (by
      intro e he
      have hh : f e.1 ≠ 0 ∧ g e.2 ≠ 0 := mul_ne_zero_iff.mp he
      exact ⟨subset_tsupport f hh.1, subset_tsupport g hh.2⟩)

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

omit [BorelSpace X] in
/-- Cutting off the target in a source test loses at most its supremum times the
actual mass outside the retained target set. No target compactness is presumed. -/
theorem abs_integral_source_sub_product_le_tail
    (π : Measure (X × Y)) (f : C_c(X, ℝ)) (g : C_c(Y, ℝ))
    (hf : Integrable (fun e : X × Y ↦ f e.1) π)
    (hg : ∀ y, g y ∈ Icc 0 1) (K : Set Y) (hgK : EqOn g 1 K)
    (htail : π (tsupport f ×ˢ Kᶜ) < ⊤) :
    |(∫ e, f e.1 ∂π) - ∫ e, cavityProductTest f g e ∂π| ≤
      ‖f.toBoundedContinuousFunction‖ * π.real (tsupport f ×ˢ Kᶜ) := by
  have hfg : Integrable (fun e : X × Y ↦ f e.1 * g e.2) π :=
    hf.mul_bdd (g.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun e ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hg e.2).1] using (hg e.2).2))
  change |(∫ e, f e.1 ∂π) - ∫ e, f e.1 * g e.2 ∂π| ≤ _
  rw [← integral_sub hf hfg]
  have hz : ∀ e : X × Y, e ∉ tsupport f ×ˢ Kᶜ →
      f e.1 - f e.1 * g e.2 = 0 := by
    intro e he
    by_cases hx : e.1 ∈ tsupport f
    · have hy : e.2 ∈ K := by
        by_contra hy
        exact he ⟨hx, hy⟩
      rw [hgK hy]
      simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply le_trans ?_ (le_refl _)
  simpa only [Real.norm_eq_abs] using
    norm_setIntegral_le_of_norm_le_const_ae htail
      (Filter.Eventually.of_forall (fun e : X × Y ↦ show
        ‖f e.1 - f e.1 * g e.2‖ ≤ ‖f.toBoundedContinuousFunction‖ from by
          rw [← mul_one_sub, norm_mul]
          have hfactor : ‖1 - g e.2‖ ≤ 1 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hg e.2).2)]
            linarith [(hg e.2).1]
          exact (mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)).trans
            (by simpa using f.toBoundedContinuousFunction.norm_coe_le_norm e.1)))

/-- The same actual source marginal makes two truncated plan readouts differ only
by their target escape masses. This applies to diffuse and infinite plans. -/
theorem abs_product_tests_sub_le_common_source_tails
    (π₀ π₁ : Measure (X × Y)) (f : C_c(X, ℝ)) (g : C_c(Y, ℝ))
    (hsource : π₀.map Prod.fst = π₁.map Prod.fst)
    (hf₀ : Integrable (fun e : X × Y ↦ f e.1) π₀)
    (hf₁ : Integrable (fun e : X × Y ↦ f e.1) π₁)
    (hg : ∀ y, g y ∈ Icc 0 1) (K : Set Y) (hgK : EqOn g 1 K)
    (htail₀ : π₀ (tsupport f ×ˢ Kᶜ) < ⊤)
    (htail₁ : π₁ (tsupport f ×ˢ Kᶜ) < ⊤) :
    |(∫ e, cavityProductTest f g e ∂π₀) - ∫ e, cavityProductTest f g e ∂π₁| ≤
      ‖f.toBoundedContinuousFunction‖ *
        (π₀.real (tsupport f ×ˢ Kᶜ) + π₁.real (tsupport f ×ˢ Kᶜ)) := by
  have heq : (∫ e, f e.1 ∂π₀) = ∫ e, f e.1 ∂π₁ := by
    have hm₀ := integral_map (μ := π₀) (f := fun x ↦ f x)
      measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
    have hm₁ := integral_map (μ := π₁) (f := fun x ↦ f x)
      measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
    exact hm₀.symm.trans ((congrArg (fun ν : Measure X ↦ ∫ x, f x ∂ν) hsource).trans hm₁)
  have h₀ := abs_integral_source_sub_product_le_tail π₀ f g hf₀ hg K hgK htail₀
  have h₁ := abs_integral_source_sub_product_le_tail π₁ f g hf₁ hg K hgK htail₁
  calc
    _ = |((∫ e, f e.1 ∂π₁) - ∫ e, cavityProductTest f g e ∂π₁) -
        ((∫ e, f e.1 ∂π₀) - ∫ e, cavityProductTest f g e ∂π₀)| := by rw [heq]; congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (by rw [mul_add]; linarith)

/-- Genuine compact target cutoffs recover an integrable original source test;
no properness of the source projection is required. -/
theorem tendsto_integral_cavityProductTest_cutoff
    [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
    (π : Measure (X × Y)) (f : C_c(X, ℝ)) (K : CompactExhaustion Y)
    (hf : Integrable (fun e : X × Y ↦ f e.1) π) :
    Tendsto (fun R ↦ ∫ e, cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff K R) e ∂π)
      atTop (𝓝 (∫ e, f e.1 ∂π)) := by
  apply tendsto_integral_of_dominated_convergence (fun e : X × Y ↦ ‖f e.1‖)
  · intro R
    exact ((f.continuous.measurable.comp measurable_fst).mul
      ((LocalFiniteMeasure.exhaustionCutoff K R).continuous.measurable.comp
        measurable_snd)).aestronglyMeasurable
  · exact hf.norm
  · intro R
    exact Filter.Eventually.of_forall fun e ↦ by
      change ‖f e.1 * LocalFiniteMeasure.exhaustionCutoff K R e.2‖ ≤ ‖f e.1‖
      rw [norm_mul, Real.norm_eq_abs (LocalFiniteMeasure.exhaustionCutoff K R e.2),
        abs_of_nonneg (LocalFiniteMeasure.exhaustionCutoff_bounds K R e.2).1]
      exact (mul_le_mul_of_nonneg_left
        (LocalFiniteMeasure.exhaustionCutoff_bounds K R e.2).2 (norm_nonneg _)).trans_eq
          (mul_one _)
  · exact Filter.Eventually.of_forall fun e ↦ by
      obtain ⟨R₀, hR₀⟩ := K.exists_mem e.2
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop R₀] with R hR
      change f e.1 = f e.1 * LocalFiniteMeasure.exhaustionCutoff K R e.2
      rw [LocalFiniteMeasure.exhaustionCutoff_eq_one K R (K.subset hR hR₀)]
      simp

section WeakClosure
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- A uniform original expectation bound for a continuous readout survives weak
convergence, even when that readout is unbounded. -/
theorem lintegral_abs_le_of_weak_uniform_bound
    (Q : ProbabilityMeasure Ω) (P : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto P atTop (𝓝 Q)) (H : Ω → ℝ) (hH : Continuous H)
    (C : ℝ≥0∞) (hbound : ∀ n, (∫⁻ ω, ENNReal.ofReal |H ω| ∂(P n : Measure Ω)) ≤ C) :
    (∫⁻ ω, ENNReal.ofReal |H ω| ∂(Q : Measure Ω)) ≤ C := by
  apply (lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hH.abs (fun _ ↦ abs_nonneg _) (fun U hU ↦
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU)).trans
  exact liminf_le_of_frequently_le (Filter.Eventually.frequently
    (Filter.Eventually.of_forall hbound))

/-- Removing compact cutoffs after weak convergence preserves an exact zero
identity whenever its original cutoff errors tend to zero. -/
theorem ae_eq_zero_of_weak_cutoff_errors
    (Q : ProbabilityMeasure Ω) (P : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto P atTop (𝓝 Q)) (H : ℕ → Ω → ℝ) (hH : ∀ R, Continuous (H R))
    (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ R n, (∫⁻ ω, ENNReal.ofReal |H R ω| ∂(P n : Measure Ω)) ≤ error R)
    (Hlim : Ω → ℝ) (hlim : ∀ᵐ ω ∂(Q : Measure Ω),
      Tendsto (fun R ↦ H R ω) atTop (𝓝 (Hlim ω))) :
    ∀ᵐ ω ∂(Q : Measure Ω), Hlim ω = 0 := by
  have hb (R : ℕ) : (∫⁻ ω, ENNReal.ofReal |H R ω| ∂(Q : Measure Ω)) ≤ error R :=
    lintegral_abs_le_of_weak_uniform_bound Q P hweak (H R) (hH R) (error R) (hbound R)
  have hz : Tendsto (fun R ↦ ∫⁻ ω, ENNReal.ofReal |H R ω| ∂(Q : Measure Ω))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herror
      (fun _ ↦ zero_le) hb
  have hlim' : ∀ᵐ ω ∂(Q : Measure Ω),
      Tendsto (fun R ↦ ENNReal.ofReal |H R ω|) atTop (𝓝 (ENNReal.ofReal |Hlim ω|)) :=
    hlim.mono fun ω h ↦ ENNReal.continuous_ofReal.continuousAt.tendsto.comp h.abs
  have hzero : (∫⁻ ω, ENNReal.ofReal |Hlim ω| ∂(Q : Measure Ω)) = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ = ∫⁻ ω, atTop.liminf (fun R ↦ ENNReal.ofReal |H R ω|) ∂(Q : Measure Ω) :=
        lintegral_congr_ae (hlim'.mono fun _ h ↦ h.liminf_eq.symm)
      _ ≤ atTop.liminf (fun R ↦ ∫⁻ ω, ENNReal.ofReal |H R ω| ∂(Q : Measure Ω)) :=
        lintegral_liminf_le (fun R ↦ (hH R).abs.measurable.ennreal_ofReal)
      _ = 0 := hz.liminf_eq
  have hmeas := ENNReal.aemeasurable_of_tendsto
    (fun R ↦ (hH R).abs.measurable.ennreal_ofReal.aemeasurable) hlim'
  exact ((lintegral_eq_zero_iff' hmeas).mp hzero).mono fun ω h ↦
    abs_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp h) (abs_nonneg _))
end WeakClosure

section MarginalClosure
variable [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
  [SecondCountableTopology Y]

local instance cavitySemidiscreteMarginalTestsLocalInst1 : PolishSpace (LocalFiniteMeasure (X × Y)) := LocalFiniteMeasure.instPolishSpace

/-- Countable source tests and actual vanishing target-cutoff errors preserve the
full common source marginal through weak convergence of the correlated scene. -/
theorem ae_common_source_marginal_of_weak_cutoff_errors
    (Q : ProbabilityMeasure (CavityLocalScene X Y))
    (P : ℕ → ProbabilityMeasure (CavityLocalScene X Y))
    (hweak : Tendsto P atTop (𝓝 Q))
    (KX : CompactExhaustion X) (KY : (ℕ ⊕ (ℕ × ℕ)) → CompactExhaustion Y)
    (hlocal : ∀ᵐ π ∂(Q : Measure (CavityLocalScene X Y)),
      IsFiniteMeasureOnCompacts (π.1 : Measure (X × Y)).fst ∧
      IsFiniteMeasureOnCompacts (π.2 : Measure (X × Y)).fst)
    (error : (ℕ ⊕ (ℕ × ℕ)) → ℕ → ℝ≥0∞)
    (herror : ∀ i, Tendsto (error i) atTop (𝓝 0))
    (hbound : ∀ i R n,
      (∫⁻ π : CavityLocalScene X Y, ENNReal.ofReal |LocalFiniteMeasure.testIntegral π.1
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (KY i) R)) -
        LocalFiniteMeasure.testIntegral π.2
          (cavityProductTest (LocalFiniteMeasure.separatingTest KX i)
            (LocalFiniteMeasure.exhaustionCutoff (KY i) R))| ∂(P n : Measure (CavityLocalScene X Y))) ≤ error i R) :
    ∀ᵐ π ∂(Q : Measure (CavityLocalScene X Y)),
      (π.1 : Measure (X × Y)).fst = (π.2 : Measure (X × Y)).fst := by
  have hall : ∀ᵐ π ∂(Q : Measure (CavityLocalScene X Y)), ∀ i : ℕ ⊕ (ℕ × ℕ),
      (∫ e, LocalFiniteMeasure.separatingTest KX i e.1 ∂(π.1 : Measure (X × Y))) =
        ∫ e, LocalFiniteMeasure.separatingTest KX i e.1 ∂(π.2 : Measure (X × Y)) := by
    apply ae_all_iff.mpr
    intro i
    let f := LocalFiniteMeasure.separatingTest KX i
    let H := fun R (π : CavityLocalScene X Y) ↦
      LocalFiniteMeasure.testIntegral π.1 (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff (KY i) R)) -
      LocalFiniteMeasure.testIntegral π.2 (cavityProductTest f (LocalFiniteMeasure.exhaustionCutoff (KY i) R))
    have hH : ∀ R, Continuous (H R) := fun R ↦
      ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).sub
        ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)
    have hz := ae_eq_zero_of_weak_cutoff_errors Q P hweak H hH (error i) (herror i) (hbound i)
      (fun π ↦ (∫ e, f e.1 ∂(π.1 : Measure (X × Y))) -
        ∫ e, f e.1 ∂(π.2 : Measure (X × Y))) (by
          filter_upwards [hlocal] with π hπ
          let : IsFiniteMeasureOnCompacts ((π.1 : Measure (X × Y)).map Prod.fst) := hπ.1
          let : IsFiniteMeasureOnCompacts ((π.2 : Measure (X × Y)).map Prod.fst) := hπ.2
          have hf₀ : Integrable (fun e : X × Y ↦ f e.1) (π.1 : Measure (X × Y)) :=
            (integrable_map_measure (f := Prod.fst) (g := fun x ↦ f x)
              f.continuous.aestronglyMeasurable measurable_fst.aemeasurable).mp f.integrable
          have hf₁ : Integrable (fun e : X × Y ↦ f e.1) (π.2 : Measure (X × Y)) :=
            (integrable_map_measure (f := Prod.fst) (g := fun x ↦ f x)
              f.continuous.aestronglyMeasurable measurable_fst.aemeasurable).mp f.integrable
          exact (tendsto_integral_cavityProductTest_cutoff _ f (KY i) hf₀).sub
            (tendsto_integral_cavityProductTest_cutoff _ f (KY i) hf₁))
    exact hz.mono fun _ h ↦ sub_eq_zero.mp h
  filter_upwards [hlocal, hall] with π hπ htests
  let := hπ.1
  let := hπ.2
  let μ₀ : LocalFiniteMeasure X := ⟨(π.1 : Measure (X × Y)).fst, hπ.1⟩
  let μ₁ : LocalFiniteMeasure X := ⟨(π.2 : Measure (X × Y)).fst, hπ.2⟩
  have heq : μ₀ = μ₁ := by
    apply LocalFiniteMeasure.separatingTestCode_injective KX
    funext i
    let f := LocalFiniteMeasure.separatingTest KX i
    change (∫ x, f x ∂(π.1 : Measure (X × Y)).fst) =
      ∫ x, f x ∂(π.2 : Measure (X × Y)).fst
    have hm₀ := integral_map (μ := (π.1 : Measure (X × Y))) (f := fun x ↦ f x)
      measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
    have hm₁ := integral_map (μ := (π.2 : Measure (X × Y))) (f := fun x ↦ f x)
      measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
    exact hm₀.trans ((htests i).trans hm₁.symm)
  exact congrArg (fun μ : LocalFiniteMeasure X ↦ (μ : Measure X)) heq
end MarginalClosure

end OTSelector.Probability
