import OTSelector.Reconstruction.OriginalStageReserveFactorization
import OTSelector.Probability.InfiniteProductLaw

/-! Finite selections from the original infinite iid reserve sampler keep their spatial law. -/
open Set Function MeasureTheory ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Probability

/-- A measurable family of observations with a common fibre law retains its joint law with
all auxiliary data. Finite unnormalized auxiliary laws include actual mark/count event fibres. -/
theorem map_original_aux_observation_of_fibre_law
    {Z Ω Y : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace Y]
    (P : Measure Z) [IsFiniteMeasure P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (f : Z × Ω → Y) (hf : Measurable f)
    (hlaw : ∀ z, μ.map (fun x ↦ f (z, x)) = ν) :
    (P.prod μ).map (fun p ↦ (p.1, f p)) = P.prod ν := by
  have hm : Measurable (fun p : Z × Ω ↦ (p.1, f p)) := measurable_fst.prodMk hf
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply hm (hs.prod ht), Measure.prod_apply (hm (hs.prod ht)), Measure.prod_prod]
  have hsection (z : Z) : μ (Prod.mk z ⁻¹' ((fun p : Z × Ω ↦ (p.1, f p)) ⁻¹' (s ×ˢ t))) =
      s.indicator (fun _ ↦ ν t) z := by
    by_cases hz : z ∈ s
    · have hset : Prod.mk z ⁻¹' ((fun p : Z × Ω ↦ (p.1, f p)) ⁻¹' (s ×ˢ t)) =
          (fun x ↦ f (z, x)) ⁻¹' t := by ext x; simp [hz]
      have hmz : Measurable (fun x ↦ f (z, x)) := hf.comp measurable_prodMk_left
      rw [hset, ← Measure.map_apply hmz ht, hlaw z]
      simp [hz]
    · have hset : Prod.mk z ⁻¹' ((fun p : Z × Ω ↦ (p.1, f p)) ⁻¹' (s ×ˢ t)) = ∅ := by
        ext x; simp [hz]
      simp [hset, hz]
  simp_rw [hsection]
  simp [hs, mul_comm]

/-- Any finite injective choice of original Nat coordinates from the actual infinite reserve
sampler has exactly the original finite iid spatial law, including the empty choice. -/
theorem map_injective_original_infinite_iid_positions
    {J X : Type*} [Fintype J] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : J ↪ ℕ) :
    (Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun x j ↦ x (e j)) =
      Measure.pi (fun _ : J ↦ μ) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ μ)
    (f := e) e.injective
  simpa only [Measure.infinitePi_eq_pi] using h

/-- Marks, original counts, main scene and auxiliary indices may choose a finite injection
into the original infinite reserve sampler. The selected positions remain independent of
all those data; restriction of the auxiliary law to an actual count/mark event is permitted. -/
theorem map_mark_selected_original_infinite_iid_positions
    {J X Z : Type*} [Fintype J] [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) [IsProbabilityMeasure μ] (P : Measure Z) [IsFiniteMeasure P]
    (e : Z → J ↪ ℕ) (he : ∀ j, Measurable (fun z ↦ e z j)) :
    (P.prod (Measure.infinitePi (fun _ : ℕ ↦ μ))).map
      (fun p ↦ (p.1, fun j ↦ p.2 (e p.1 j))) = P.prod (Measure.pi (fun _ : J ↦ μ)) := by
  have hm : Measurable (fun p : Z × (ℕ → X) ↦ fun j ↦ p.2 (e p.1 j)) := by
    apply measurable_pi_lambda
    intro j s hs
    have hset : (fun p : Z × (ℕ → X) ↦ p.2 (e p.1 j)) ⁻¹' s =
        ⋃ i : ℕ, {p : Z × (ℕ → X) | e p.1 j = i} ∩ {p | p.2 i ∈ s} := by
      ext p
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h ↦ ⟨e p.1 j, rfl, h⟩, fun ⟨i, hi, hx⟩ ↦ hi ▸ hx⟩
    rw [hset]
    exact MeasurableSet.iUnion fun i ↦
      (((he j).comp measurable_fst) (measurableSet_singleton i)).inter
        (((measurable_pi_apply i).comp measurable_snd) hs)
  exact map_original_aux_observation_of_fibre_law P _ _ _ hm
    (fun z ↦ map_injective_original_infinite_iid_positions μ (e z))

end OTSelector.Probability
