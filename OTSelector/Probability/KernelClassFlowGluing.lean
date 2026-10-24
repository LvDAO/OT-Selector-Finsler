import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.Transport.Coupling.FiniteClockMixture
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalPopulationFlowGlue.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalPopulationFlowGlue`; the selected original proof blocks follow. -/
section

/-!
# Probability.KernelClassFlowGluing

## Lemma skeleton

* **Conditions:** Finite class-flow matrices with measurable label-dependent entries, an actual original flow and a replacement retained/residual split on a measurable good-label set.
* **Objects:** Measurable glued flows with the original marginals/legal zero pattern and a residual mass bound paying actual original density outside the good set.
* **Proof detail:** Keep replacement entries on the good set and the original flow on its complement. Check marginals and nonnegativity by cases, then integrate the Markov component-kernel masses.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31): Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20).
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Explicit piecewise finite flow assembly; feasibility and legal support are supplied rather than solved by a matching theorem.
-/

/-!
Replace class flow on selected original labels while retaining the literal original flow outside; charge the actual discarded population in the residual mass.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Retain frozen class flow only on the chosen original label population. -/
def retainedClassFlowOn {I J Z : Type*} (G : Set Z) (P : Z → I → J → ℝ)
    (z : Z) (i : I) (j : J) : ℝ := by
  classical
  exact if z ∈ G then P z i j else 0

/-- Outside the chosen labels, the residual keeps the literal original class
coupling. Inside, it uses the deterministic feasible residual flow. -/
def residualClassFlowOn {I J Z : Type*} (G : Set Z)
    (A Q : Z → I → J → ℝ) (z : Z) (i : I) (j : J) : ℝ := by
  classical
  exact if z ∈ G then Q z i j else A z i j

theorem measurable_retainedClassFlowOn
    {I J Z : Type*} [MeasurableSpace Z] (G : Set Z) (hG : MeasurableSet G)
    (P : Z → I → J → ℝ) (hP : ∀ i j, Measurable (fun z ↦ P z i j)) (i : I) (j : J) :
    Measurable (fun z ↦ retainedClassFlowOn G P z i j) := by
  classical
  exact (hP i j).ite hG measurable_const

theorem measurable_residualClassFlowOn
    {I J Z : Type*} [MeasurableSpace Z] (G : Set Z) (hG : MeasurableSet G)
    (A Q : Z → I → J → ℝ)
    (hA : ∀ i j, Measurable (fun z ↦ A z i j))
    (hQ : ∀ i j, Measurable (fun z ↦ Q z i j)) (i : I) (j : J) :
    Measurable (fun z ↦ residualClassFlowOn G A Q z i j) := by
  classical
  exact (hQ i j).ite hG (hA i j)

/-- Good-label replacement and literal original outside flow preserve both
original class marginals and legal graph support. -/
theorem originalClassFlow_glue_marginals
    {I J Z : Type*} [Fintype I] [Fintype J] [MeasurableSpace Z]
    (r : Measure Z) (G : Set Z) (allowed : I → J → Prop)
    (A P Q : Z → I → J → ℝ) (a : Z → I → ℝ) (b : Z → J → ℝ)
    (hA : ∀ᵐ z ∂r,
      (∀ i j, 0 ≤ A z i j) ∧ (∀ i, ∑ j, A z i j = a z i) ∧
      (∀ j, ∑ i, A z i j = b z j) ∧ ∀ i j, ¬ allowed i j → A z i j = 0)
    (hPQ : ∀ᵐ z ∂r, z ∈ G →
      (∀ i j, 0 ≤ P z i j) ∧ (∀ i j, 0 ≤ Q z i j) ∧
      (∀ i, ∑ j, (P z i j + Q z i j) = a z i) ∧
      (∀ j, ∑ i, (P z i j + Q z i j) = b z j) ∧
      ∀ i j, ¬ allowed i j → P z i j = 0 ∧ Q z i j = 0) :
    ∀ᵐ z ∂r,
      (∀ i j, 0 ≤ retainedClassFlowOn G P z i j) ∧
      (∀ i j, 0 ≤ residualClassFlowOn G A Q z i j) ∧
      (∀ i, ∑ j, (retainedClassFlowOn G P z i j + residualClassFlowOn G A Q z i j) = a z i) ∧
      (∀ j, ∑ i, (retainedClassFlowOn G P z i j + residualClassFlowOn G A Q z i j) = b z j) ∧
      ∀ i j, ¬ allowed i j →
        retainedClassFlowOn G P z i j + residualClassFlowOn G A Q z i j = 0 := by
  classical
  filter_upwards [hA, hPQ] with z hz hq
  by_cases hzG : z ∈ G
  · obtain ⟨hp, hq, hrow, hcol, hzero⟩ := hq hzG
    simp only [retainedClassFlowOn, residualClassFlowOn, ite_eq_left hzG]
    exact ⟨hp, hq, hrow, hcol, fun i j hij ↦ by rw [(hzero i j hij).1, (hzero i j hij).2, add_zero]⟩
  · simp only [retainedClassFlowOn, residualClassFlowOn, ite_eq_right hzG, zero_add]
    exact ⟨fun _ _ ↦ le_refl 0, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩

/-- The actual residual mass charges the original discarded population outside
`G`, plus its deterministic inside-class residual bound. -/
theorem originalClassFlow_glue_residual_mass_le
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (r : Measure Z) [SFinite r] (G : Set Z) (hG : MeasurableSet G)
    (A Q : Z → I → J → ℝ)
    (hmA : ∀ i j, Measurable (fun z ↦ A z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hA : ∀ᵐ z ∂r, ∀ i j, 0 ≤ A z i j)
    (hQ : ∀ᵐ z ∂r, z ∈ G → ∀ i j, 0 ≤ Q z i j)
    (d : Z → ℝ) (hmassA : ∀ᵐ z ∂r, (∑ i, ∑ j, A z i j) = d z)
    (B : ℝ) (hmassQ : ∀ᵐ z ∂r, z ∈ G → (∑ i, ∑ j, Q z i j) ≤ B) :
    sameLabelPopulationCoupling r (residualClassFlowOn G A Q) α β univ ≤
      ENNReal.ofReal B * r G + ∫⁻ z in Gᶜ, ENNReal.ofReal (d z) ∂r := by
  classical
  have hm := measurable_residualClassFlowOn G hG A Q hmA hmQ
  have hnonneg : ∀ᵐ z ∂r, ∀ i j, 0 ≤ residualClassFlowOn G A Q z i j := by
    filter_upwards [hA, hQ] with z ha hq
    by_cases hzG : z ∈ G
    · simpa only [residualClassFlowOn, ite_eq_left hzG] using hq hzG
    · simpa only [residualClassFlowOn, ite_eq_right hzG] using ha
  rw [sameLabelPopulationCoupling_mass r _ hm α β hnonneg]
  calc
    _ ≤ ∫⁻ z, G.piecewise (fun _ ↦ ENNReal.ofReal B) (fun z ↦ ENNReal.ofReal (d z)) z ∂r := by
      apply lintegral_mono_ae
      filter_upwards [hmassA, hmassQ] with z ha hq
      by_cases hzG : z ∈ G
      · simp only [residualClassFlowOn, ite_eq_left hzG, piecewise_eq_of_mem G _ _ hzG]
        exact ENNReal.ofReal_le_ofReal (hq hzG)
      · simp only [residualClassFlowOn, ite_eq_right hzG, piecewise_eq_of_notMem G _ _ hzG]
        exact le_of_eq (congrArg ENNReal.ofReal ha)
    _ = _ := by rw [lintegral_piecewise hG, setLIntegral_const]

end OTSelector.Reconstruction

end
end
