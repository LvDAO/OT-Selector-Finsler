import OTSelector.Probability.FiniteCellClassFlow
import OTSelector.Transport.Coupling.WindowPairFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawMeasurableWindowTransfer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawMeasurableWindowTransfer`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawMeasurableWindowTransfer

**Conditions:** The actual class-flow data are measurable on a prescribed measurable good set, with the stated reference-window bounds.

**Objects:** Measurable retained/residual masked flows equal to the original formulas on that set.

**Proof detail:** Use measurable arithmetic and fixed finite masks to define both pieces globally; apply the deterministic window split pointwise on the good set, retaining all original marginal and mass identities.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Move the original bad reference pair classes into the residual using only
the measurable retained class mass as scalar factor. The construction does not
need measurable original intensity outside the chosen physical cell. -/
theorem exists_measurable_actualReferenceWindow_split
    {I J Z : Type*} [Fintype I] [Fintype J] [MeasurableSpace Z]
    (γ : Measure (ℝ × ℝ)) [IsFiniteMeasure γ]
    (S : I → Set ℝ) (T : J → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (H : Set (ℝ × ℝ)) (allowed : I → J → Prop)
    (P Q : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (a : Z → I → ℝ) (b : Z → J → ℝ) (G : Set Z) (B L : ℝ)
    (htotalRef : (∑ i, ∑ j, actualClockClassFlow γ S T i j) = 1)
    (hloss : γ.real Hᶜ ≤ L)
    (hlocal : ∀ z ∈ G,
      (∀ i j, 0 ≤ P z i j) ∧ (∀ i j, 0 ≤ Q z i j) ∧
      (∀ i, ∑ j, (P z i j + Q z i j) = a z i) ∧
      (∀ j, ∑ i, (P z i j + Q z i j) = b z j) ∧
      (∀ i j, ¬ allowed i j → actualClockClassFlow γ S T i j = 0 ∧ Q z i j = 0) ∧
      (∑ i, ∑ j, Q z i j) ≤ B ∧ (∑ i, a z i) = 1 ∧
      ∃ scale : ℝ, ∀ i j, P z i j = scale * actualClockClassFlow γ S T i j) :
    ∃ Pg Qg : Z → I → J → ℝ,
      (∀ i j, Measurable (fun z ↦ Pg z i j)) ∧
      (∀ i j, Measurable (fun z ↦ Qg z i j)) ∧
      ∀ z ∈ G,
        (∀ i j, 0 ≤ Pg z i j) ∧ (∀ i j, 0 ≤ Qg z i j) ∧
        (∀ i, ∑ j, (Pg z i j + Qg z i j) = a z i) ∧
        (∀ j, ∑ i, (Pg z i j + Qg z i j) = b z j) ∧
        (∀ i j, ¬ allowed i j → Pg z i j = 0 ∧ Qg z i j = 0) ∧
        (∑ i, ∑ j, Qg z i j) ≤ B + L ∧
        ∀ i j, Pg z i j = maskedClockFlow
          (fun i j ↦ ((S i ×ˢ T j) ∩ H).Nonempty) (P z) i j := by
  classical
  let keep := fun i j ↦ ((S i ×ˢ T j) ∩ H).Nonempty
  let scale := fun z ↦ ∑ i, ∑ j, P z i j
  have hmscale : Measurable scale :=
    Finset.measurable_sum _ fun i hi ↦ Finset.measurable_sum _ fun j hj ↦ hmP i j
  let Pg := fun z i j ↦ scale z * maskedClockFlow keep (actualClockClassFlow γ S T) i j
  let Qg := fun z i j ↦ Q z i j +
    scale z * maskedClockFlow (fun i j ↦ ¬ keep i j) (actualClockClassFlow γ S T) i j
  have hmPg (i j) : Measurable (fun z ↦ Pg z i j) :=
    measurable_mul.comp (hmscale.prodMk measurable_const)
  have hmQg (i j) : Measurable (fun z ↦ Qg z i j) :=
    measurable_add.comp ((hmQ i j).prodMk
      (measurable_mul.comp (hmscale.prodMk measurable_const)))
  refine ⟨Pg, Qg, hmPg, hmQg, ?_⟩
  intro z hz
  obtain ⟨hp, hq, hr, hc, hzero, hmass, ht, s, hs⟩ := hlocal z hz
  have hscale : scale z = s := by
    dsimp only [scale]
    simp_rw [hs]
    simp_rw [← Finset.mul_sum]
    rw [htotalRef, mul_one]
  have hscale0 : 0 ≤ scale z :=
    Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦ hp i j
  have hr' (i) : ∑ j, (scale z * actualClockClassFlow γ S T i j + Q z i j) = a z i := by
    simp_rw [hscale, ← hs]
    exact hr i
  have hc' (j) : ∑ i, (scale z * actualClockClassFlow γ S T i j + Q z i j) = b z j := by
    simp_rw [hscale, ← hs]
    exact hc j
  obtain ⟨hp', hq', hr', hc', hz', hm'⟩ := actualReferenceWindow_split γ S T hS hT hdS hdT
    H allowed (Q z) (scale z) (a z) (b z) B hscale0 hq htotalRef ht hr' hc' hzero hmass
  refine ⟨hp', hq', hr', hc', hz', hm'.trans (add_le_add_right hloss B), ?_⟩
  intro i j
  dsimp only [Pg]
  rw [hscale]
  by_cases hij : ((S i ×ˢ T j) ∩ H).Nonempty
  · simp only [maskedClockFlow, keep, ite_eq_left hij, hs]
  · simp only [maskedClockFlow, keep, ite_eq_right hij, mul_zero]

end OTSelector.Reconstruction

end
end
