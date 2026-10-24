import OTSelector.Finite.FractionalOptimal
import OTSelector.Probability.Dirichlet.CavityExchangeability
import OTSelector.Probability.Dirichlet.CavityLaw
import OTSelector.Probability.Dirichlet.CavitySuccess
import OTSelector.Probability.DirichletReference
import OTSelector.Transport.Semidiscrete.Calibration
import OTSelector.Transport.Semidiscrete.CavityCells
import OTSelector.Transport.Semidiscrete.Cells
import OTSelector.Transport.Semidiscrete.MeanCoupling
import OTSelector.Transport.Semidiscrete.MeanPlan
import OTSelector.Transport.Semidiscrete.MeasurableReadout
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteReadout`; the selected original proof blocks follow. -/
section

/-!
Conditions: Measurable integrable finite target costs and atomless pairwise cost differences under the actual input probability law.

Objects: A measurable Dirichlet-indexed unique semidiscrete optimum readout representing the expected actual iid assignment observable.

Proof detail: Combine the distribution-free cavity-mass law, strict semidiscrete calibration and measurable factor readout, then apply the canonical row-mean identity.

Sources: Gabriel Peyré, Section 5.2, equations (5.6)–(5.8), pp. 94–96 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=98); D. H. Fremlin, 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary (https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Project manuscript, Section “Exact iid cavity disintegration”, Theorem thm:iid-cavity-dirichlet and Proposition prop:iid-cavity-mean, equation eq:iid-cavity-mean-plan (main.tex).
Relation: Project-derived exact identity: main.tex thm:iid-cavity-dirichlet and prop:iid-cavity-mean, especially eq:iid-cavity-mean-plan. External sources support calibration/disintegration, not the distribution-free cavity theorem itself.
-/

/-!
# The Dirichlet semidiscrete mean identity for every empirical optimum

The mass-indexed readout is constructed from the original cavity, is measurable, and
almost everywhere is the paired-test integral of the unique semidiscrete optimum.
Every original empirical optimal fractional matrix has its expected normalized readout
equal to this Dirichlet integral.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

/-- A measurable Dirichlet readout of the actual unique semidiscrete allocation,
with the exact mean identity simultaneously for the whole empirical optimal face. -/
theorem exists_dirichlet_semidiscrete_mean_readout
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hci : ∀ j, Integrable (c j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (g : S → Fin (m + 1) → ℝ)
    (hgm : ∀ j, Measurable (fun s ↦ g s j)) (hgi : ∀ j, Integrable (fun s ↦ g s j) μ) :
    ∃ G : (Fin (m + 1) → ℝ) → ℝ, Measurable G ∧
      (∀ᵐ p ∂dirichletOne m, ∃ a : S → Fin (m + 1) → ℝ,
        IsSemidiscreteAllocation μ p a ∧
        (∀ b, IsSemidiscreteAllocation μ p b →
          semidiscreteAllocationCost μ (fun s j ↦ c j s) a ≤
            semidiscreteAllocationCost μ (fun s j ↦ c j s) b ∧
          (semidiscreteAllocationCost μ (fun s j ↦ c j s) a =
            semidiscreteAllocationCost μ (fun s j ↦ c j s) b → a =ᵐ[μ] b)) ∧
        G p = semidiscreteAllocationCost μ g a) ∧
      (∀ A : (Fin (m + 1) → S) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
        (∀ᵐ x ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ),
          OptimalFractionalAssignment (fun k j ↦ c j (x k)) (A x)) →
        (∫ x, (∑ i, ∑ j, A x i j * g (x i) j) / (m + 1 : ℕ)
          ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ)) = ∫ p, G p ∂dirichletOne m) := by
  let retained := iidCapacityInputCost c (fun (k : Fin m) (w : Fin m → S) ↦ w k)
  let row : (Fin m → S) × S → Fin (m + 1) → ℝ := fun z j ↦ c j z.2
  have hret := measurable_iidCavityRetained c hc
  have hrow j : Measurable (fun z ↦ row z j) := (hc j).comp measurable_snd
  obtain ⟨G, hG, hrep, hfactor⟩ := exists_dirichlet_cavity_readout μ c hc hci hatom g hgm hgi
  refine ⟨G, hG, ?_, ?_⟩
  · filter_upwards [hrep] with p hp
    obtain ⟨w, hw, hGw⟩ := hp
    have hno (j l : Fin (m + 1)) (hjl : j ≠ l) :
        μ {s | cavityScore retained row 0 (w, s) j = cavityScore retained row 0 (w, s) l} = 0 := by
      have := hatom j l hjl
      exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow 0 j l w
    have ha := isSemidiscreteAllocation_cavityAllocation μ retained row hret hrow 0 w hno
    have hmass : (fun j ↦ (cavityCellMass μ retained row 0 j w).toReal) = p := hw
    refine ⟨cavityAllocation retained row 0 w, hmass ▸ ha, ?_, ?_⟩
    · intro b hb
      exact cavityAllocation_unique_optimal μ retained row hret hrow 0 w hno hci b
        (hmass.symm ▸ hb)
    · exact hGw.trans (cavityMeanReadout_eq_allocationCost μ retained row hret hrow 0 w _ hgi)
  · intro A hA
    rw [(integral_iid_optimalFractional_mean_eq_canonical_cavity μ c hc hatom A hA g hgi).2]
    rw [← map_iidCavityMassVector_eq_dirichletOne μ c hc hatom,
      integral_map (measurable_iidCavityMassVector μ c hc).aemeasurable hG.aestronglyMeasurable]
    exact integral_congr_ae hfactor

end OTSelector.Probability

end
end
