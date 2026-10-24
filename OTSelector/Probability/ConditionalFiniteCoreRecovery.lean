import OTSelector.Probability.ConditionalLabelCoreRecovery
import OTSelector.Probability.LabelDependentKernel
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConditionalFiniteCoreRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConditionalFiniteCoreRecovery`; the selected original proof blocks follow. -/
section

/-!
# Probability.ConditionalFiniteCoreRecovery

## Lemma skeleton

* **Conditions:** A finite disjoint measurable label-core family and the exact original conditional recovery law on every label set.
* **Objects:** Finite core/complement reconstruction of original populations and their nonnegative or integrable vector observables, with a complement-mass error bound.
* **Proof detail:** Partition the common label measure into the finite cores plus untouched complement, transport the given conditional recovery identities and apply finite integral additivity and the bounded complement estimate.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46): Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Finite label partition assembly preserving original masses; integrable signed/vector readouts state their own integrability premises.
-/

/-!
# Exact finite reconstruction on original label cores

Finite disjoint label pieces retain their original masses and conditional kernels.
Their physical restrictions and the untouched complement recover both original
populations exactly, as do the original conditional mixtures on those pieces.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {M Z I : Type*} [MeasurableSpace M] [MeasurableSpace Z] [Fintype I]

/-- A finite measurable partition and its complement recover the original measure. -/
theorem sum_restrict_add_restrict_complement (μ : Measure Z) (K : I → Set Z)
    (hK : ∀ i, MeasurableSet (K i)) (hd : Pairwise (Function.onFun Disjoint K)) :
    (∑ i, μ.restrict (K i)) + μ.restrict (⋃ i, K i)ᶜ = μ := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd hK]
  exact Measure.restrict_add_restrict_compl (MeasurableSet.iUnion hK)

/-- Finite original label cores preserve the two physical laws, their masses,
their label-clock disintegrations and their original conditional distributions. -/
structure FiniteLabelCoreRecovery (u : M → ℝ) (a : M → Z) (b : Z × ℝ → M)
    (lambda : Measure Z) (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (K : I → Set Z) : Prop where
  measurable : ∀ i, MeasurableSet (K i)
  disjoint : Pairwise (Function.onFun Disjoint K)
  label_decomposition : (∑ i, lambda.restrict (K i)) + lambda.restrict (⋃ i, K i)ᶜ = lambda
  source_decomposition : (∑ i, η₀.restrict (a ⁻¹' K i)) +
    η₀.restrict (a ⁻¹' (⋃ i, K i)ᶜ) = η₀
  target_decomposition : (∑ i, η₁.restrict (a ⁻¹' K i)) +
    η₁.restrict (a ⁻¹' (⋃ i, K i)ᶜ) = η₁
  source_joint : ∀ i, (η₀.restrict (a ⁻¹' K i)).map (fun x ↦ (a x, u x)) =
    lambda.restrict (K i) ⊗ₘ condDistrib u a η₀
  target_joint : ∀ i, (η₁.restrict (a ⁻¹' K i)).map (fun x ↦ (a x, u x)) =
    lambda.restrict (K i) ⊗ₘ condDistrib u a η₁
  source_mixture : (∑ i, mapWithLabel (condDistrib u a η₀) b ∘ₘ lambda.restrict (K i)) +
    mapWithLabel (condDistrib u a η₀) b ∘ₘ lambda.restrict (⋃ i, K i)ᶜ = η₀
  target_mixture : (∑ i, mapWithLabel (condDistrib u a η₁) b ∘ₘ lambda.restrict (K i)) +
    mapWithLabel (condDistrib u a η₁) b ∘ₘ lambda.restrict (⋃ i, K i)ᶜ = η₁
  source_mass : ∀ i, η₀ (a ⁻¹' K i) = lambda (K i)
  target_mass : ∀ i, η₁ (a ⁻¹' K i) = lambda (K i)
  source_remainder_mass : η₀ (a ⁻¹' (⋃ i, K i)ᶜ) = lambda (⋃ i, K i)ᶜ
  target_remainder_mass : η₁ (a ⁻¹' (⋃ i, K i)ᶜ) = lambda (⋃ i, K i)ᶜ
  source_conditional : ∀ i, condDistrib u a (η₀.restrict (a ⁻¹' K i))
    =ᵐ[lambda.restrict (K i)] condDistrib u a η₀
  target_conditional : ∀ i, condDistrib u a (η₁.restrict (a ⁻¹' K i))
    =ᵐ[lambda.restrict (K i)] condDistrib u a η₁

/-- The original recovery law supplies finite disjoint core reconstruction with
the exact original label weights and conditional kernels. -/
theorem PopulationLabelCoreRecoveryLaw.finite_recovery
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (hlaw : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (ha : Measurable a) (hu : Measurable u) (K : I → Set Z)
    (hK : ∀ i, MeasurableSet (K i)) (hd : Pairwise (Function.onFun Disjoint K)) :
    FiniteLabelCoreRecovery u a b lambda η₀ η₁ K := by
  have hU : MeasurableSet (⋃ i, K i) := MeasurableSet.iUnion hK
  have hdata i := hlaw (K i) (hK i)
  have hrest := hlaw (⋃ i, K i)ᶜ hU.compl
  have hlabel₀ : η₀.map a = lambda := by
    simpa using (hlaw univ MeasurableSet.univ).1
  have hlabel₁ : η₁.map a = lambda := by
    simpa using (hlaw univ MeasurableSet.univ).2.1
  have hphys (η : Measure M) : (∑ i, η.restrict (a ⁻¹' K i)) +
      η.restrict (a ⁻¹' (⋃ i, K i)ᶜ) = η := by
    simpa only [preimage_compl, preimage_iUnion] using
      sum_restrict_add_restrict_complement η (fun i ↦ a ⁻¹' K i)
        (fun i ↦ ha (hK i)) (fun i j hij ↦ (hd hij).preimage a)
  refine ⟨hK, hd, sum_restrict_add_restrict_complement lambda K hK hd,
    hphys η₀, hphys η₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← hlabel₀]
    exact original_label_clock_restrict_eq_compProd η₀ ha hu (hK i)
  · intro i
    rw [← hlabel₁]
    exact original_label_clock_restrict_eq_compProd η₁ ha hu (hK i)
  · simp_rw [(hdata _).2.2.1, hrest.2.2.1]
    exact hphys η₀
  · simp_rw [(hdata _).2.2.2.1, hrest.2.2.2.1]
    exact hphys η₁
  · exact fun i ↦ (hdata i).2.2.2.2.1
  · exact fun i ↦ (hdata i).2.2.2.2.2.1
  · exact hrest.2.2.2.2.1
  · exact hrest.2.2.2.2.2.1
  · exact fun i ↦ (hdata i).2.2.2.2.2.2.2.2.1
  · exact fun i ↦ (hdata i).2.2.2.2.2.2.2.2.2

/-- Integrating a nonnegative local pressure against the original label law is
exactly the finite core sum plus its original complementary contribution. -/
theorem FiniteLabelCoreRecovery.lintegral_labels
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {K : I → Set Z}
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K) (f : Z → ℝ≥0∞) :
    ∫⁻ z, f z ∂lambda = (∑ i, ∫⁻ z in K i, f z ∂lambda) +
      ∫⁻ z in (⋃ i, K i)ᶜ, f z ∂lambda := by
  conv_lhs => rw [← D.label_decomposition]
  rw [lintegral_add_measure, lintegral_finsetSum_measure]

/-- Signed or vector-valued local pressures also split with the exact original
label masses whenever the original observable is integrable. -/
theorem FiniteLabelCoreRecovery.integral_labels
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {K : I → Set Z}
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K)
    {f : Z → G} (hf : Integrable f lambda) :
    ∫ z, f z ∂lambda = (∑ i, ∫ z in K i, f z ∂lambda) +
      ∫ z in (⋃ i, K i)ᶜ, f z ∂lambda := by
  have hpieces : ∀ i ∈ (Finset.univ : Finset I), Integrable f (lambda.restrict (K i)) :=
    fun _ _ ↦ hf.mono_measure Measure.restrict_le_self
  have hrest : Integrable f (lambda.restrict (⋃ i, K i)ᶜ) :=
    hf.mono_measure Measure.restrict_le_self
  conv_lhs => rw [← D.label_decomposition]
  rw [integral_add_measure (integrable_finsetSum_measure.mpr hpieces) hrest,
    integral_finsetSum_measure hpieces]

/-- A bound on the discarded original label contribution gives the pressure
truncation error with its actual lost mass. -/
theorem FiniteLabelCoreRecovery.norm_integral_labels_sub_sum_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    [IsFiniteMeasure lambda] {η₀ η₁ : Measure M}
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {K : I → Set Z}
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K)
    {f : Z → G} (hf : Integrable f lambda) {C : ℝ}
    (hC : ∀ᵐ z ∂lambda.restrict (⋃ i, K i)ᶜ, ‖f z‖ ≤ C) :
    ‖(∫ z, f z ∂lambda) - ∑ i, ∫ z in K i, f z ∂lambda‖ ≤
      C * lambda.real (⋃ i, K i)ᶜ := by
  rw [D.integral_labels hf, add_sub_cancel_left]
  exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top _ _) hC

/-- The source physical integral splits into the original conditional integrals
with their original label masses on each finite core and on the complement. -/
theorem FiniteLabelCoreRecovery.lintegral_source
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    [SFinite lambda] {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {K : I → Set Z} (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K)
    (hb : Measurable b) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂η₀ =
      (∑ i, ∫⁻ z in K i, ∫⁻ t, f (b (z, t)) ∂condDistrib u a η₀ z ∂lambda) +
      ∫⁻ z in (⋃ i, K i)ᶜ, ∫⁻ t, f (b (z, t)) ∂condDistrib u a η₀ z ∂lambda := by
  conv_lhs => rw [← D.source_mixture]
  rw [lintegral_add_measure, lintegral_finsetSum_measure]
  simp_rw [lintegral_mapWithLabel_comp _ _ hb hf]

/-- The target physical integral uses the same finite original label weights. -/
theorem FiniteLabelCoreRecovery.lintegral_target
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    [SFinite lambda] {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {K : I → Set Z} (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K)
    (hb : Measurable b) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂η₁ =
      (∑ i, ∫⁻ z in K i, ∫⁻ t, f (b (z, t)) ∂condDistrib u a η₁ z ∂lambda) +
      ∫⁻ z in (⋃ i, K i)ᶜ, ∫⁻ t, f (b (z, t)) ∂condDistrib u a η₁ z ∂lambda := by
  conv_lhs => rw [← D.target_mixture]
  rw [lintegral_add_measure, lintegral_finsetSum_measure]
  simp_rw [lintegral_mapWithLabel_comp _ _ hb hf]

end OTSelector.Reconstruction

end
end
