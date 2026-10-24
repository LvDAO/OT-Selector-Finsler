import OTSelector.Transport.Coupling.MixtureLabelTransfer
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingSplit.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingSplit`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingSplit

**Conditions:** A finite coupling’s chosen marginal is the sum of two finite measures.

**Objects:** Two actual subcouplings with the prescribed marginal parts and exact sum equal to the original coupling.

**Proof detail:** Take the Radon–Nikodym derivative of one marginal part with respect to the whole marginal and pull the density onto the plan; its complementary density gives the second piece and both pushforwards are exact.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Section 235G, integration along an inverse-measure-preserving map; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Genuine finite RN splitting of a transport plan along a sum marginal. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 300000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A plan whose target marginal is a sum admits two actual finite subplans with
exact target marginals. The sum is the original plan even for overlapping laws. -/
theorem exists_finiteStageCoupling_target_split
    (π : Measure (A × B)) [IsFiniteMeasure π]
    (ρ ν : Measure B) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (hπ : π.snd = ρ + ν) :
    ∃ α β : Measure (A × B), IsFiniteMeasure α ∧ IsFiniteMeasure β ∧
      α + β = π ∧ α.snd = ρ ∧ β.snd = ν := by
  classical
  let κ : Unit → Measure A := fun _ ↦ π.fst
  let σ : Fin 2 → Measure B := ![ρ, ν]
  have : ∀ i, IsFiniteMeasure (κ i) := fun _ ↦ inferInstance
  have : ∀ j, IsFiniteMeasure (σ j) := by
    intro j
    fin_cases j <;> dsimp [σ] <;> infer_instance
  have hκ : ∑ i, κ i = π.fst := by simp [κ]
  have hσ : ∑ j, σ j = ρ + ν := by simp [σ, Fin.sum_univ_two]
  have hcouple : Vlasov.IsCoupling π (∑ i, κ i) (∑ j, σ j) :=
    ⟨hκ.symm, hπ.trans hσ.symm⟩
  let α := smoothingEndpointCouplingPart κ σ π () 0
  let β := smoothingEndpointCouplingPart κ σ π () 1
  have hsum : α + β = π := by
    simpa only [Fintype.sum_unique, Fin.sum_univ_two, α, β] using
      smoothingEndpointCouplingPart_sum κ σ π hcouple
  refine ⟨α, β,
    isFiniteMeasure_of_le π (smoothingEndpointCouplingPart_le κ σ π hcouple () 0),
    isFiniteMeasure_of_le π (smoothingEndpointCouplingPart_le κ σ π hcouple () 1), hsum, ?_, ?_⟩
  · simpa [Measure.snd, σ, α] using
      smoothingEndpointCouplingPart_column κ σ π hcouple 0
  · simpa [Measure.snd, σ, β] using
      smoothingEndpointCouplingPart_column κ σ π hcouple 1

/-- The source version retains exact finite subplans with the two prescribed
source marginals. No disjointness or positive-mass assumption is required. -/
theorem exists_finiteStageCoupling_source_split
    (π : Measure (A × B)) [IsFiniteMeasure π]
    (ρ ζ : Measure A) [IsFiniteMeasure ρ] [IsFiniteMeasure ζ]
    (hπ : π.fst = ρ + ζ) :
    ∃ α β : Measure (A × B), IsFiniteMeasure α ∧ IsFiniteMeasure β ∧
      α + β = π ∧ α.fst = ρ ∧ β.fst = ζ := by
  have hswap : (π.map Prod.swap).snd = ρ + ζ := by
    rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
    exact hπ
  obtain ⟨α, β, hα, hβ, hsum, hαρ, hβζ⟩ :=
    exists_finiteStageCoupling_target_split (π.map Prod.swap) ρ ζ hswap
  have : IsFiniteMeasure α := hα
  have : IsFiniteMeasure β := hβ
  refine ⟨α.map Prod.swap, β.map Prod.swap, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [← Measure.map_add _ _ measurable_swap, hsum,
      Measure.map_map measurable_swap measurable_swap]
    simp only [Prod.swap_swap_eq, Measure.map_id]
  · rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    exact hαρ
  · rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    exact hβζ

end OTSelector.Reconstruction

end
end
