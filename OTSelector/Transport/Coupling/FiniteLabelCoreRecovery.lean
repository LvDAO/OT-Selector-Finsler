import LeanPool.Vlasov.OT.Coupling
import OTSelector.Probability.ConditionalFiniteCoreRecovery
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConditionalFiniteCouplingRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConditionalFiniteCouplingRecovery`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.ConditionalFiniteCouplingRecovery

**Conditions:** An original coupling is concentrated on equal measurable labels, and finite label cores partition the prescribed retained region.

**Objects:** Exact coupling restrictions to physical cores and converse finite gluing with the original complement.

**Proof detail:** Equal-label concentration identifies both restricted marginals, disjoint restrictions sum to the original plan, and finite additivity preserves the common legality condition and exact cost lower integrals.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Section 235G, integration along an inverse-measure-preserving map; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144), Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Restricting and gluing original couplings on finite label cores

Every original coupling concentrated on equal labels restricts to couplings of
the exact physical core marginals. Conversely, arbitrary local couplings with
these original marginals and an original complementary coupling glue exactly.
Any shared almost-everywhere legality condition is preserved by this finite sum.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {M Z I : Type*} [MeasurableSpace M] [MeasurableSpace Z] [Fintype I]

/-- Restriction by a common original label retains both exact restricted marginals. -/
theorem isCoupling_restrict_common_label {η₀ η₁ : Measure M}
    {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π η₀ η₁)
    {a : M → Z} (ha : Measurable a) (hsame : ∀ᵐ p ∂π, a p.1 = a p.2)
    {K : Set Z} (hK : MeasurableSet K) :
    Vlasov.IsCoupling (π.restrict ((fun p : M × M ↦ a p.1) ⁻¹' K))
      (η₀.restrict (a ⁻¹' K)) (η₁.restrict (a ⁻¹' K)) := by
  constructor
  · change (π.restrict (Prod.fst ⁻¹' (a ⁻¹' K))).map Prod.fst = _
    rw [← Measure.restrict_map measurable_fst (ha hK), hπ.1]
  · have heq : ((fun p : M × M ↦ a p.1) ⁻¹' K) =ᵐ[π]
        ((fun p : M × M ↦ a p.2) ⁻¹' K) := by
      filter_upwards [hsame] with p hp
      change (a p.1 ∈ K) = (a p.2 ∈ K)
      rw [hp]
    rw [Measure.restrict_congr_set heq]
    change (π.restrict (Prod.snd ⁻¹' (a ⁻¹' K))).map Prod.snd = _
    rw [← Measure.restrict_map measurable_snd (ha hK), hπ.2]

/-- Every equal-label original coupling decomposes exactly over a finite original
core, and each term retains the original physical marginals of that piece. -/
theorem FiniteLabelCoreRecovery.restrict_coupling
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {K : I → Set Z}
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K)
    (ha : Measurable a) {π : Measure (M × M)} (hπ : Vlasov.IsCoupling π η₀ η₁)
    (hsame : ∀ᵐ p ∂π, a p.1 = a p.2) :
    (∀ i, Vlasov.IsCoupling (π.restrict ((fun p : M × M ↦ a p.1) ⁻¹' K i))
      (η₀.restrict (a ⁻¹' K i)) (η₁.restrict (a ⁻¹' K i))) ∧
    Vlasov.IsCoupling (π.restrict ((fun p : M × M ↦ a p.1) ⁻¹' (⋃ i, K i)ᶜ))
      (η₀.restrict (a ⁻¹' (⋃ i, K i)ᶜ)) (η₁.restrict (a ⁻¹' (⋃ i, K i)ᶜ)) ∧
    (∑ i, π.restrict ((fun p : M × M ↦ a p.1) ⁻¹' K i)) +
      π.restrict ((fun p : M × M ↦ a p.1) ⁻¹' (⋃ i, K i)ᶜ) = π := by
  refine ⟨fun i ↦ isCoupling_restrict_common_label hπ ha hsame (D.measurable i),
    isCoupling_restrict_common_label hπ ha hsame (MeasurableSet.iUnion D.measurable).compl, ?_⟩
  simpa only [preimage_compl, preimage_iUnion] using
    sum_restrict_add_restrict_complement π (fun i ↦ (fun p : M × M ↦ a p.1) ⁻¹' K i)
      (fun i ↦ (ha.comp measurable_fst) (D.measurable i))
      (fun i j hij ↦ (D.disjoint hij).preimage _)

/-- Local couplings with the original finite-core marginals and a complementary
coupling glue to a coupling of the complete original physical populations. -/
theorem FiniteLabelCoreRecovery.glue_couplings
    {u : M → ℝ} {a : M → Z} {b : Z × ℝ → M} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {K : I → Set Z}
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K)
    {π : I → Measure (M × M)} {πrest : Measure (M × M)}
    (hπ : ∀ i, Vlasov.IsCoupling (π i) (η₀.restrict (a ⁻¹' K i))
      (η₁.restrict (a ⁻¹' K i)))
    (hrest : Vlasov.IsCoupling πrest (η₀.restrict (a ⁻¹' (⋃ i, K i)ᶜ))
      (η₁.restrict (a ⁻¹' (⋃ i, K i)ᶜ))) :
    Vlasov.IsCoupling ((∑ i, π i) + πrest) η₀ η₁ := by
  constructor
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_finset_sum' measurable_fst.aemeasurable]
    simp_rw [(hπ _).1, hrest.1]
    exact D.source_decomposition
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_finset_sum' measurable_snd.aemeasurable]
    simp_rw [(hπ _).2, hrest.2]
    exact D.target_decomposition

/-- Finite core gluing preserves every original almost-everywhere legality property. -/
theorem ae_glue_finite_couplings {π : I → Measure (M × M)} {πrest : Measure (M × M)}
    {Legal : M × M → Prop} (hπ : ∀ i, ∀ᵐ p ∂π i, Legal p)
    (hrest : ∀ᵐ p ∂πrest, Legal p) :
    ∀ᵐ p ∂(∑ i, π i) + πrest, Legal p := by
  rw [ae_add_measure_iff]
  refine ⟨?_, hrest⟩
  rw [← Measure.sum_fintype, Measure.ae_sum_iff]
  exact hπ

/-- The cost of the glued original coupling is the exact sum of the local costs
and the complementary cost, before any local-pressure estimates are applied. -/
theorem lintegral_glue_finite_couplings (π : I → Measure (M × M))
    (πrest : Measure (M × M)) (c : M × M → ℝ≥0∞) :
    ∫⁻ p, c p ∂((∑ i, π i) + πrest) =
      (∑ i, ∫⁻ p, c p ∂π i) + ∫⁻ p, c p ∂πrest := by
  rw [lintegral_add_measure, lintegral_finsetSum_measure]

end OTSelector.Reconstruction

end
end
