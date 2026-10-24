import Mathlib.MeasureTheory.Integral.IntegrableOn
import OTSelector.Transport.CyclicMonotonicity.AmbientCountableTargetRigidity
import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteLegalTargetRigidity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteLegalTargetRigidity`; the selected original proof blocks follow. -/
section

/-!
# Probability.CavitySemidiscreteLegalTargetRigidity

**Conditions:** Original plans share their source marginal and a measurably embedded countable target cloud; two-cycle and atomless difference conditions hold only on the actual common legal source sets.

**Objects:** Ambient-plan equality from the common legal averaged support.

**Proof detail:** Pull back the target embedding, restrict cost differences to common legal sources, apply legal countable-target rigidity, and recover both original plans by the inverse pushforward; continuity on an open legal set supplies measurability.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30), Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31; [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254), Appendix A.1, Theorem A.5, p. 242; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (generalization): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Ambient plan rigidity using only legal exchanges

The original plans are carried by the legal part of their averaged support.
Only cost differences on common legal source domains enter the proof. The
common countable target embedding is reused without an ordered-separation
assumption or a global extension of the continuous cost.
-/

open MeasureTheory Set OTSelector.Reconstruction
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S Y J : Type*} [MeasurableSpace S] [MeasurableSpace Y]
  [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]

/-- Continuity only on the actual legal domain supplies the restricted
cost-difference measurability needed by the rigidity argument. -/
theorem aemeasurable_costDifference_on_commonLegalSource
    [TopologicalSpace S] [OpensMeasurableSpace S] [TopologicalSpace Y]
    (μ : Measure S) {c : S → Y → ℝ} {D : Set (S × Y)} (hD : MeasurableSet D)
    (hc : ContinuousOn (Function.uncurry c) D) (y z : Y) :
    AEMeasurable (fun s ↦ c s y - c s z) (μ.restrict (commonLegalSource D y z)) := by
  have hy : ContinuousOn (fun s ↦ c s y) (commonLegalSource D y z) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ h ↦ h.1)
  have hz : ContinuousOn (fun s ↦ c s z) (commonLegalSource D y z) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ h ↦ h.2)
  exact (hy.sub hz).aemeasurable (measurableSet_commonLegalSource hD y z)

/-- A common legal two-cycle monotone relation determines the original ambient
plans from their source marginal and common countable target cloud. -/
theorem ambient_plan_eq_of_countable_target_legal_twoCycle
    (μ : Measure S) (π₀ π₁ : Measure (S × Y))
    (y : J → Y) (hy : MeasurableEmbedding y)
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : ∀ᵐ z ∂π₀, z.2 ∈ range y) (htarget₁ : ∀ᵐ z ∂π₁, z.2 ∈ range y)
    (c : S → Y → ℝ) (D Γ : Set (S × Y)) (hD : MeasurableSet D)
    (hΓ : MeasurableSet Γ) (hsub : Γ ⊆ D)
    (hcycle : IsTwoCycleMonotoneOn c D Γ)
    (hcarried₀ : ∀ᵐ z ∂π₀, z ∈ Γ) (hcarried₁ : ∀ᵐ z ∂π₁, z ∈ Γ)
    (hc : ∀ i j, AEMeasurable (fun s ↦ c s (y i) - c s (y j))
      (μ.restrict (commonLegalSource D (y i) (y j))))
    (hatom : ∀ i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource D (y i) (y j))).map
        (fun s ↦ c s (y i) - c s (y j)))) : π₀ = π₁ := by
  apply ambient_plan_eq_of_countable_target_ae_single_valued μ π₀ π₁ y hy
    hsource₀ hsource₁ htarget₀ htarget₁ Γ hΓ hcarried₀ hcarried₁
  apply IsTwoCycleMonotoneOn.ae_single_valued (c := fun s j ↦ c s (y j))
    (D := (Prod.map id y) ⁻¹' D) (Γ := (Prod.map id y) ⁻¹' Γ)
    (fun x i x' j hi hj hcross hcross' ↦
      hcycle x (y i) x' (y j) hi hj hcross hcross')
    (hD.preimage (measurable_id.prodMap hy.measurable)) (preimage_mono hsub) hc hatom

/-- Legality and legal two-cycle monotonicity of the actual averaged support
force equality, including infinite source and plan mass. -/
theorem ambient_plan_eq_of_countable_target_legal_average_support
    [TopologicalSpace S] [TopologicalSpace Y]
    [OpensMeasurableSpace S] [OpensMeasurableSpace Y]
    [SecondCountableTopology S] [SecondCountableTopology Y]
    (μ : Measure S) (ν : Measure Y) (π₀ π₁ : Measure (S × Y))
    (y : J → Y) (hy : MeasurableEmbedding y) (hν : ∀ᵐ z ∂ν, z ∈ range y)
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : π₀.map Prod.snd = ν) (htarget₁ : π₁.map Prod.snd = ν)
    (c : S → Y → ℝ) (D : Set (S × Y)) (hD : MeasurableSet D)
    (hlegal₀ : ∀ᵐ z ∂π₀, z ∈ D) (hlegal₁ : ∀ᵐ z ∂π₁, z ∈ D)
    (hcycle : IsTwoCycleMonotoneOn c D
      ((((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) ∩ D))
    (hc : ∀ i j, AEMeasurable (fun s ↦ c s (y i) - c s (y j))
      (μ.restrict (commonLegalSource D (y i) (y j))))
    (hatom : ∀ i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource D (y i) (y j))).map
        (fun s ↦ c s (y i) - c s (y j)))) : π₀ = π₁ := by
  have hsupp : ∀ᵐ z ∂(2 : ℝ≥0∞)⁻¹ • (π₀ + π₁),
      z ∈ (((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) := Measure.support_mem_ae
  rw [Measure.ae_ennreal_smul_measure_iff (by simp), ae_add_measure_iff] at hsupp
  exact ambient_plan_eq_of_countable_target_legal_twoCycle μ π₀ π₁ y hy hsource₀ hsource₁
    (ae_of_ae_map measurable_snd.aemeasurable (htarget₀.symm ▸ hν))
    (ae_of_ae_map measurable_snd.aemeasurable (htarget₁.symm ▸ hν))
    c D _ hD (Measure.isClosed_support.measurableSet.inter hD) inter_subset_right hcycle
    (hsupp.1.and hlegal₀) (hsupp.2.and hlegal₁) hc hatom

/-- For an open legal cost domain, local continuity and restricted atomless
cost differences suffice for ambient uniqueness. -/
theorem ambient_plan_eq_of_countable_target_open_legal_average_support
    [TopologicalSpace S] [TopologicalSpace Y]
    [OpensMeasurableSpace S] [OpensMeasurableSpace Y]
    [SecondCountableTopology S] [SecondCountableTopology Y]
    (μ : Measure S) (ν : Measure Y) (π₀ π₁ : Measure (S × Y))
    (y : J → Y) (hy : MeasurableEmbedding y) (hν : ∀ᵐ z ∂ν, z ∈ range y)
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : π₀.map Prod.snd = ν) (htarget₁ : π₁.map Prod.snd = ν)
    (c : S → Y → ℝ) (D : Set (S × Y)) (hD : IsOpen D)
    (hlegal₀ : ∀ᵐ z ∂π₀, z ∈ D) (hlegal₁ : ∀ᵐ z ∂π₁, z ∈ D)
    (hcycle : IsTwoCycleMonotoneOn c D
      ((((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) ∩ D))
    (hc : ContinuousOn (Function.uncurry c) D)
    (hatom : ∀ i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource D (y i) (y j))).map
        (fun s ↦ c s (y i) - c s (y j)))) : π₀ = π₁ :=
  ambient_plan_eq_of_countable_target_legal_average_support μ ν π₀ π₁ y hy hν
    hsource₀ hsource₁ htarget₀ htarget₁ c D hD.measurableSet hlegal₀ hlegal₁ hcycle
    (fun i j ↦ aemeasurable_costDifference_on_commonLegalSource μ hD.measurableSet hc (y i) (y j))
    hatom

end OTSelector.Probability

end
end
