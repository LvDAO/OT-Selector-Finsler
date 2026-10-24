import LeanPool.Vlasov.OT.Coupling
import Mathlib.Probability.Kernel.CondDistrib
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CouplingDisintegration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CouplingDisintegration`; the selected original proof blocks follow. -/
section

/-!
# Transport.Coupling.LabelDisintegration

## Lemma skeleton

* **Conditions:** Finite or probability couplings on the inherited standard Borel spaces, measurable common labels and a measurable carrying relation for the equivalence.
* **Objects:** Equal label marginals and actual labelwise conditional couplings; reconstruction preserves marginals and carrying.
* **Proof detail:** Disintegrate the actual paired law over its common label, identify conditional coordinate marginals almost everywhere by uniqueness and integrate a supplied conditional coupling kernel for the converse.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (composition): Disintegration/gluing over a supplied measurable label. Geometric quotient and calibration are separate inputs.
-/

/-!
# Conditional couplings over an actual common measurable label

The common label law is derived from a coupling supported on equal labels. Actual
regular conditional distributions then disintegrate the joint law into couplings of
the two original conditional marginals. Conversely, any measurable family of such
couplings reconstructs the original marginals. Measurable support restrictions pass
in both directions. The geometric quotient and calibration relation remain separate.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]

/-- A coupling concentrated on equal measurable labels forces equality of the original
quotient marginals. This does not assume any prior balance of the two populations. -/
theorem map_label_eq_of_coupling {π : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    (hπ : Vlasov.IsCoupling π μ ν) {a : A → Z} {b : B → Z}
    (ha : Measurable a) (hb : Measurable b)
    (heq : ∀ᵐ z ∂π, a z.1 = b z.2) : μ.map a = ν.map b := by
  rw [← hπ.1, ← hπ.2, Measure.map_map ha measurable_fst,
    Measure.map_map hb measurable_snd]
  exact Measure.map_congr heq

variable [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]

/-- Conditioning the actual pair on its common label has the two original conditional
marginals. All three kernels are constructed regular conditional distributions. -/
theorem condDistrib_marginals_of_common_label
    {π : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    [IsFiniteMeasure π] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) {a : A → Z} {b : B → Z}
    (ha : Measurable a) (hb : Measurable b)
    (heq : ∀ᵐ z ∂π, a z.1 = b z.2) :
    ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling
      (condDistrib id (a ∘ Prod.fst) π z) (condDistrib id a μ z) (condDistrib id b ν z) := by
  have hmapA : π.map (a ∘ Prod.fst) = μ.map a := by
    rw [← Measure.map_map ha measurable_fst, hπ.1]
  have hmapB : π.map (b ∘ Prod.snd) = μ.map a := by
    exact (Measure.map_congr heq).symm.trans hmapA
  have hA := condDistrib_map (ν := π) (f := Prod.fst)
    (X := a) (Y := id) ha.aemeasurable measurable_id.aemeasurable
    measurable_fst.aemeasurable
  simp only [hπ.1, hmapA] at hA
  have hB := condDistrib_map (ν := π) (f := Prod.snd)
    (X := b) (Y := id) hb.aemeasurable measurable_id.aemeasurable
    measurable_snd.aemeasurable
  simp only [hπ.2, hmapB] at hB
  have hfst := condDistrib_comp (mβ := inferInstance) (a ∘ Prod.fst) (μ := π) (Y := id)
    measurable_id.aemeasurable measurable_fst
  have hsnd := condDistrib_comp (mβ := inferInstance) (a ∘ Prod.fst) (μ := π) (Y := id)
    measurable_id.aemeasurable measurable_snd
  rw [hmapA] at hfst hsnd
  have hlabel : condDistrib (id ∘ Prod.snd) (b ∘ Prod.snd) π =
      condDistrib (id ∘ Prod.snd) (a ∘ Prod.fst) π :=
    condDistrib_congr_right
      (show (a ∘ Prod.fst) =ᵐ[π] (b ∘ Prod.snd) from heq).symm
  rw [hlabel] at hB
  filter_upwards [hA, hB, hfst, hsnd] with z hzA hzB hzfst hzsnd
  constructor
  · exact (Kernel.map_apply _ measurable_fst _).symm.trans (hzfst.symm.trans hzA.symm)
  · exact (Kernel.map_apply _ measurable_snd _).symm.trans (hzsnd.symm.trans hzB.symm)

/-- The joint conditional law is constructed and retains both original conditional
marginals and every measurable almost-sure support restriction of the original plan. -/
theorem exists_coupling_disintegration_of_common_label
    {π : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure π] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) {a : A → Z} {b : B → Z}
    (ha : Measurable a) (hb : Measurable b)
    (heq : ∀ᵐ z ∂π, a z.1 = b z.2)
    {R : Set (A × B)} (hπR : ∀ᵐ z ∂π, z ∈ R) :
    μ.map a = ν.map b ∧ ∃ κ : Kernel Z (A × B), IsMarkovKernel κ ∧
      (μ.map a) ⊗ₘ κ = π.map (fun z ↦ (a z.1, z)) ∧ κ ∘ₘ μ.map a = π ∧
      ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
        (condDistrib id a μ z) (condDistrib id b ν z) ∧ ∀ᵐ p ∂κ z, p ∈ R := by
  have hmap : π.map (a ∘ Prod.fst) = μ.map a := by
    rw [← Measure.map_map ha measurable_fst, hπ.1]
  let κ := condDistrib id (a ∘ Prod.fst) π
  have hrec : κ ∘ₘ μ.map a = π := by
    rw [← hmap]
    simpa only [Measure.map_id] using
      condDistrib_comp_map (ha.comp measurable_fst).aemeasurable
        (measurable_id.aemeasurable : AEMeasurable (id : A × B → A × B) π)
  refine ⟨map_label_eq_of_coupling hπ ha hb heq, κ, inferInstance, ?_, hrec, ?_⟩
  · rw [← hmap]
    exact compProd_map_condDistrib measurable_id.aemeasurable
  · have hcond := condDistrib_marginals_of_common_label hπ ha hb heq
    have hsupp : ∀ᵐ z ∂μ.map a, ∀ᵐ p ∂κ z, p ∈ R :=
      Measure.ae_ae_of_ae_comp (by rwa [hrec])
    filter_upwards [hcond, hsupp] with z hz hzR using ⟨hz, hzR⟩

/-- Every measurable family of couplings of the actual original conditional marginals
reconstructs a coupling of the original populations. Support restrictions are preserved. -/
theorem isCoupling_comp_of_conditional_couplings
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : A → Z} {b : B → Z} (ha : Measurable a) (hb : Measurable b)
    (hbalance : μ.map a = ν.map b) (κ : Kernel Z (A × B)) [IsMarkovKernel κ]
    (hκ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
      (condDistrib id a μ z) (condDistrib id b ν z))
    {R : Set (A × B)} (hR : MeasurableSet R)
    (hsupp : ∀ᵐ z ∂μ.map a, ∀ᵐ p ∂κ z, p ∈ R) :
    Vlasov.IsCoupling (κ ∘ₘ μ.map a) μ ν ∧ ∀ᵐ p ∂κ ∘ₘ μ.map a, p ∈ R := by
  refine ⟨⟨?_, ?_⟩, Measure.ae_comp_of_ae_ae hR hsupp⟩
  · rw [Measure.map_comp _ _ measurable_fst]
    have hm : (κ.map Prod.fst) ∘ₘ μ.map a = (condDistrib id a μ) ∘ₘ μ.map a := by
      apply Measure.comp_congr
      filter_upwards [hκ] with z hz
      rw [Kernel.map_apply _ measurable_fst]
      exact hz.1
    rw [hm]
    simpa only [Measure.map_id] using condDistrib_comp_map ha.aemeasurable
      (measurable_id.aemeasurable : AEMeasurable (id : A → A) μ)
  · rw [Measure.map_comp _ _ measurable_snd]
    have hm : (κ.map Prod.snd) ∘ₘ μ.map a = (condDistrib id b ν) ∘ₘ μ.map a := by
      apply Measure.comp_congr
      filter_upwards [hκ] with z hz
      rw [Kernel.map_apply _ measurable_snd]
      exact hz.2
    rw [hm, hbalance]
    simpa only [Measure.map_id] using condDistrib_comp_map hb.aemeasurable
      (measurable_id.aemeasurable : AEMeasurable (id : B → B) ν)

/-- Every coupling supported on a measurable common-label relation is exactly a mixture
of couplings of the original conditional marginals with the same support restriction.
The shared label law is a conclusion of the forward direction. -/
theorem isCoupling_supported_iff_conditional_couplings
    {π : Measure (A × B)} {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : A → Z} {b : B → Z} (ha : Measurable a) (hb : Measurable b)
    {R : Set (A × B)} (hR : MeasurableSet R)
    (hlabel : ∀ p ∈ R, a p.1 = b p.2) :
    (Vlasov.IsCoupling π μ ν ∧ ∀ᵐ p ∂π, p ∈ R) ↔
      μ.map a = ν.map b ∧ ∃ κ : Kernel Z (A × B), IsMarkovKernel κ ∧
        κ ∘ₘ μ.map a = π ∧ ∀ᵐ z ∂μ.map a,
          Vlasov.IsCoupling (κ z) (condDistrib id a μ z) (condDistrib id b ν z) ∧
            ∀ᵐ p ∂κ z, p ∈ R := by
  constructor
  · rintro ⟨hπ, hsupp⟩
    have : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ inferInstance
    have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
    have heq : ∀ᵐ p ∂π, a p.1 = b p.2 := hsupp.mono fun p hp ↦ hlabel p hp
    obtain ⟨hbalance, κ, hκ, _, hrec, hc⟩ :=
      exists_coupling_disintegration_of_common_label hπ ha hb heq hsupp
    exact ⟨hbalance, κ, hκ, hrec, hc⟩
  · rintro ⟨hbalance, κ, hκ, hrec, hc⟩
    have : IsMarkovKernel κ := hκ
    rw [← hrec]
    exact isCoupling_comp_of_conditional_couplings ha hb hbalance κ
      (hc.mono fun _ h ↦ h.1) hR (hc.mono fun _ h ↦ h.2)

end OTSelector.Reconstruction

end
end
