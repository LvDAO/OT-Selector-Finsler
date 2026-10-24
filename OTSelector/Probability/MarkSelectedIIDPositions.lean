import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic

/-!
# Mark SelectedIID Positions

Conditions: Finite original iid positions and an injective index selection. In the mark-dependent theorem the mark law is an independent product factor and each selected index is measurable.

Objects: The selected iid law, jointly independent of the marks and auxiliary data that choose the injection.

Proof detail: A fixed injection preserves independence and the coordinate marginals. For a variable injection, prove joint measurability by a finite index partition and integrate over each fixed mark, where the selected law is constant.

Relation to primary sources: The auxiliary selector is independent of the original iid position array through the explicit product law. A selector inspecting those positions is not covered. The result is a local finite-coordinate factorization, not the Poisson marking theorem.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
-/
/-! Injective selection of original iid positions by marks and auxiliary data. -/
open Set Function MeasureTheory ProbabilityTheory
noncomputable section
namespace OTSelector.Probability

/-- Selecting distinct original coordinates preserves their actual product law. -/
theorem map_injective_original_iid_positions
    {I J X : Type*} [Fintype I] [Fintype J] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : J ↪ I) :
    (Measure.pi (fun _ : I ↦ μ)).map (fun x j ↦ x (e j)) =
      Measure.pi (fun _ : J ↦ μ) := by
  have hi : iIndepFun (fun i (x : I → X) ↦ x i) (Measure.pi (fun _ : I ↦ μ)) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hj := iIndepFun.precomp e.injective hi
  have h := iIndepFun.map_fun_eq_pi_map
    (fun j ↦ (measurable_pi_apply (e j)).aemeasurable) hj
  have hm (j : J) : (Measure.pi (fun _ : I ↦ μ)).map (fun x ↦ x (e j)) = μ :=
    (measurePreserving_eval (fun _ : I ↦ μ) (e j)).map_eq
  simpa only [hm] using h

/-- A mark-dependent injective index choice remains jointly independent of those marks.
The auxiliary coordinate may include the main scene and every observed mark. -/
theorem map_mark_selected_original_iid_positions
    {I J X Z : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Measure Z) [IsProbabilityMeasure P]
    (e : Z → J ↪ I) (he : ∀ j, Measurable (fun z ↦ e z j)) :
    (P.prod (Measure.pi (fun _ : I ↦ μ))).map
        (fun p ↦ (p.1, fun j ↦ p.2 (e p.1 j))) =
      P.prod (Measure.pi (fun _ : J ↦ μ)) := by
  classical
  have hm : Measurable (fun p : Z × (I → X) ↦ (p.1, fun j ↦ p.2 (e p.1 j))) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro j s hs
    have hset : (fun p : Z × (I → X) ↦ p.2 (e p.1 j)) ⁻¹' s =
        ⋃ i : I, {p : Z × (I → X) | e p.1 j = i} ∩ {p | p.2 i ∈ s} := by
      ext p
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h ↦ ⟨e p.1 j, rfl, h⟩, fun ⟨i, hi, hx⟩ ↦ hi ▸ hx⟩
    rw [hset]
    exact MeasurableSet.iUnion fun i ↦
      (((he j).comp measurable_fst) (measurableSet_singleton i)).inter
        (((measurable_pi_apply i).comp measurable_snd) hs)
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply hm (hs.prod ht), Measure.prod_apply (hm (hs.prod ht)),
    Measure.prod_prod]
  have hf (z : Z) : (Measure.pi (fun _ : I ↦ μ))
      (Prod.mk z ⁻¹' ((fun p : Z × (I → X) ↦ (p.1, fun j ↦ p.2 (e p.1 j))) ⁻¹'
        (s ×ˢ t))) = s.indicator (fun _ ↦ (Measure.pi (fun _ : J ↦ μ)) t) z := by
    by_cases hz : z ∈ s
    · have hset : Prod.mk z ⁻¹' ((fun p : Z × (I → X) ↦
          (p.1, fun j ↦ p.2 (e p.1 j))) ⁻¹' (s ×ˢ t)) =
          (fun x j ↦ x (e z j)) ⁻¹' t := by ext x; simp [hz]
      rw [hset, ← Measure.map_apply (measurable_pi_lambda _ fun j ↦
        measurable_pi_apply (e z j)) ht, map_injective_original_iid_positions]
      simp [hz]
    · have hset : Prod.mk z ⁻¹' ((fun p : Z × (I → X) ↦
          (p.1, fun j ↦ p.2 (e p.1 j))) ⁻¹' (s ×ˢ t)) = ∅ := by
        ext x; simp [hz]
      simp [hset, hz]
  simp_rw [hf]
  simp [hs, mul_comm]

end OTSelector.Probability
