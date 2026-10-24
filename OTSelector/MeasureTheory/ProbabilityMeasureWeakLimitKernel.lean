import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Probability.Kernel.Defs

/-!
## Lemma skeleton

* **Conditions:** Measurable probability fields with almost-everywhere weak limits.
* **Objects:** A measurable probability-valued version and its Markov kernel.
* **Proof detail:** Use open-set semicontinuity for the weak-Borel bridge, measurable limit versions, and kernel packaging.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
  https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18

**Relationship to the sources:** The Giry/weak-Borel bridge and null-set repair are formal adapters; the topological hypotheses are those in the Lean statements.
-/

/-!
# Measurable kernels from almost everywhere weak limits of finite iid laws

Only the finite law family is required to be measurable for the weak Borel structure.
A continuous finite family has this property. Portmanteau gives the one-sided passage from
weak Borel measurability to the unchanged Giry structure, without local compactness of the
state space. The almost everywhere limit is replaced on a null set by a measurable
probability-valued field, whose underlying measures form a Markov kernel.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]

/-- Open-set evaluation is lower semicontinuous in the actual weak topology. -/
theorem probabilityMeasure_lowerSemicontinuous_measure_open
    [OpensMeasurableSpace S] [HasOuterApproxClosed S] {U : Set S} (hU : IsOpen U) :
    LowerSemicontinuous (fun p : ProbabilityMeasure S ↦ (p : Measure S) U) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro p
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hU

/-- The unchanged underlying probability law is Giry-measurable from the weak Borel space.
This direction does not require local compactness or second countability of law space. -/
theorem measurable_probabilityMeasure_toMeasure_weakBorel_general
    [BorelSpace S] [HasOuterApproxClosed S] :
    @Measurable (ProbabilityMeasure S) (Measure S) (borel (ProbabilityMeasure S)) inferInstance
      (fun p ↦ (p : Measure S)) := by
  let : MeasurableSpace (ProbabilityMeasure S) := borel (ProbabilityMeasure S)
  have : BorelSpace (ProbabilityMeasure S) := ⟨rfl⟩
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (by rw [BorelSpace.measurable_eq (α := S)]; rfl) isPiSystem_isOpen
  intro U hU
  exact (probabilityMeasure_lowerSemicontinuous_measure_open hU).measurable

/-- A weak-Borel measurable finite family and existence of almost everywhere weak limits
produce an actual Giry-measurable limiting probability field. -/
theorem exists_measurable_probabilityMeasure_ae_weak_limit
    [BorelSpace S] [PseudoMetrizableSpace S] [SeparableSpace S]
    {C : Type*} [MeasurableSpace C] (μ : Measure C)
    (Pn : ℕ → C → ProbabilityMeasure S)
    (hPn : ∀ n, @Measurable C (ProbabilityMeasure S) inferInstance
      (borel (ProbabilityMeasure S)) (Pn n))
    (hlim : ∀ᵐ c ∂μ, ∃ Q : ProbabilityMeasure S,
      Tendsto (fun n ↦ Pn n c) atTop (𝓝 Q)) :
    ∃ Q : C → ProbabilityMeasure S, Measurable Q ∧
      ∀ᵐ c ∂μ, Tendsto (fun n ↦ Pn n c) atTop (𝓝 (Q c)) := by
  have hcoerce := measurable_probabilityMeasure_toMeasure_weakBorel_general (S := S)
  let : MeasurableSpace (ProbabilityMeasure S) := borel (ProbabilityMeasure S)
  have : BorelSpace (ProbabilityMeasure S) := ⟨rfl⟩
  obtain ⟨Q, hQ, hQt⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n ↦ (hPn n).aemeasurable) hlim
  refine ⟨Q, ?_, hQt⟩
  exact (hcoerce.comp hQ).subtype_mk

/-- Continuous finite law fields admit a measurable actual probability limit on the set where
the weak limit exists almost everywhere. -/
theorem exists_measurable_probabilityMeasure_ae_weak_limit_of_continuous
    [BorelSpace S] [PseudoMetrizableSpace S] [SeparableSpace S]
    {C : Type*} [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    (μ : Measure C) (Pn : ℕ → C → ProbabilityMeasure S) (hPn : ∀ n, Continuous (Pn n))
    (hlim : ∀ᵐ c ∂μ, ∃ Q : ProbabilityMeasure S,
      Tendsto (fun n ↦ Pn n c) atTop (𝓝 Q)) :
    ∃ Q : C → ProbabilityMeasure S, Measurable Q ∧
      ∀ᵐ c ∂μ, Tendsto (fun n ↦ Pn n c) atTop (𝓝 (Q c)) := by
  apply exists_measurable_probabilityMeasure_ae_weak_limit μ Pn ?_ hlim
  intro n
  let : MeasurableSpace (ProbabilityMeasure S) := borel (ProbabilityMeasure S)
  have : BorelSpace (ProbabilityMeasure S) := ⟨rfl⟩
  exact (hPn n).measurable

/-- The measurable probability limit supplies an everywhere Markov kernel, with actual weak
convergence to its unmodified underlying laws at almost every root. -/
theorem exists_markovKernel_ae_weak_limit_of_continuous
    [BorelSpace S] [PseudoMetrizableSpace S] [SeparableSpace S]
    {C : Type*} [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    (μ : Measure C) (Pn : ℕ → C → ProbabilityMeasure S) (hPn : ∀ n, Continuous (Pn n))
    (hlim : ∀ᵐ c ∂μ, ∃ Q : ProbabilityMeasure S,
      Tendsto (fun n ↦ Pn n c) atTop (𝓝 Q)) :
    ∃ Q : C → ProbabilityMeasure S, Measurable Q ∧
      ∃ κ : Kernel C S, IsMarkovKernel κ ∧
        (∀ c, κ c = (Q c : Measure S)) ∧
        ∀ᵐ c ∂μ, Tendsto (fun n ↦ Pn n c) atTop (𝓝 (Q c)) := by
  obtain ⟨Q, hQ, hQt⟩ :=
    exists_measurable_probabilityMeasure_ae_weak_limit_of_continuous μ Pn hPn hlim
  let κ : Kernel C S :=
    { toFun := fun c ↦ (Q c : Measure S)
      measurable' := measurable_subtype_coe.comp hQ }
  refine ⟨Q, hQ, κ, ?_, fun _ ↦ rfl, hQt⟩
  exact ⟨fun c ↦ inferInstanceAs (IsProbabilityMeasure (Q c : Measure S))⟩

/-- A specified almost everywhere weak limit is unchanged almost everywhere by the measurable
modification and its Markov kernel. The specified field need not be assumed measurable. -/
theorem exists_markovKernel_ae_eq_of_continuous_ae_weak_limit
    [BorelSpace S] [PseudoMetrizableSpace S] [SeparableSpace S]
    {C : Type*} [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    (μ : Measure C) (Pn : ℕ → C → ProbabilityMeasure S) (hPn : ∀ n, Continuous (Pn n))
    (Q : C → ProbabilityMeasure S)
    (hlim : ∀ᵐ c ∂μ, Tendsto (fun n ↦ Pn n c) atTop (𝓝 (Q c))) :
    ∃ Qm : C → ProbabilityMeasure S, Measurable Qm ∧ Q =ᵐ[μ] Qm ∧
      ∃ κ : Kernel C S, IsMarkovKernel κ ∧
        (∀ c, κ c = (Qm c : Measure S)) ∧
        ∀ᵐ c ∂μ, Tendsto (fun n ↦ Pn n c) atTop (𝓝 (Qm c)) := by
  obtain ⟨Qm, hQm, κ, hκ, hκQm, hQmt⟩ :=
    exists_markovKernel_ae_weak_limit_of_continuous μ Pn hPn
      (hlim.mono (fun c hc ↦ ⟨Q c, hc⟩))
  refine ⟨Qm, hQm, ?_, κ, hκ, hκQm, hQmt⟩
  filter_upwards [hlim, hQmt] with c hc hcm
  exact tendsto_nhds_unique hc hcm

/-- Any asserted profile of the actual almost everywhere weak limits is retained by the
measurable Markov version, by uniqueness of limits. No measurability of the profile is needed. -/
theorem exists_markovKernel_ae_weak_limit_with_profile_of_continuous
    [BorelSpace S] [PseudoMetrizableSpace S] [SeparableSpace S]
    {C : Type*} [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    (μ : Measure C) (Pn : ℕ → C → ProbabilityMeasure S) (hPn : ∀ n, Continuous (Pn n))
    (P : C → ProbabilityMeasure S → Prop)
    (hlim : ∀ᵐ c ∂μ, ∃ Q : ProbabilityMeasure S,
      Tendsto (fun n ↦ Pn n c) atTop (𝓝 Q) ∧ P c Q) :
    ∃ Q : C → ProbabilityMeasure S, Measurable Q ∧
      ∃ κ : Kernel C S, IsMarkovKernel κ ∧
        (∀ c, κ c = (Q c : Measure S)) ∧
        ∀ᵐ c ∂μ, Tendsto (fun n ↦ Pn n c) atTop (𝓝 (Q c)) ∧ P c (Q c) := by
  obtain ⟨Qm, hQm, κ, hκ, hκQm, hQmt⟩ :=
    exists_markovKernel_ae_weak_limit_of_continuous μ Pn hPn
      (hlim.mono (fun _ hc ↦ hc.imp (fun _ hq ↦ hq.1)))
  refine ⟨Qm, hQm, κ, hκ, hκQm, ?_⟩
  filter_upwards [hlim, hQmt] with c hc hcm
  obtain ⟨Q, hQt, hQP⟩ := hc
  exact ⟨hcm, tendsto_nhds_unique hQt hcm ▸ hQP⟩

end OTSelector.Probability
