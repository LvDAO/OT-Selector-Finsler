import OTSelector.Probability.ConditionalEndpointRecovery
import OTSelector.Transport.Coupling.FiniteClockMixture

/-!
Conditions: The same measurable a.e. original label-clock inverse for two finite populations with common label law, a retained pair kernel dominated by their actual conditional marginals and a measurable label coordinate map.

Objects: A.e. coordinate recovery and an exact raw retained-pair pushforward identity in the literal retained label/clock coordinates.

Proof detail: Transfer the original left-inverse identity through the joint conditional laws, restrict it to the dominated pair marginals and rewrite the two coordinate maps a.e. inside the original composition product.

References: D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary; D. H. Fremlin: 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.
Relation: An actual a.e.-inverse readout identity. It reuses the existing inverse; no new inverse is selected separately for a sampled point or empirical array.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawRetainedCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawRetainedCoordinates`; the selected original proof blocks follow. -/
section

/-! The original almost-everywhere label-clock inverse recovers literal retained
Haar coordinates. No inverse is selected again for the empirical sample. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Original physical recovery gives the opposite inverse identity on the
literal original conditional clocks. -/
theorem ae_condDistrib_original_labelClock_right_inverse
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z]
    (μ : Measure X) [IsFiniteMeasure μ] (a : X → Z) (u : X → ℝ)
    (ha : Measurable a) (hu : Measurable u) (b : Z × ℝ → X) (hb : Measurable b)
    (hinv : ∀ᵐ x ∂μ, b (a x, u x) = x) :
    ∀ᵐ z ∂μ.map a,
      (∀ᵐ s ∂condDistrib u a μ z, a (b (z, s)) = z) ∧
      (∀ᵐ s ∂condDistrib u a μ z, u (b (z, s)) = s) := by
  have hlabel := ae_condDistrib_recovery_eq μ a u ha hu
    (a ∘ b) Prod.fst (ha.comp hb) measurable_fst (hinv.mono fun x hx ↦ by simp [hx])
  have hclock := ae_condDistrib_recovery_eq μ a u ha hu
    (u ∘ b) Prod.snd (hu.comp hb) measurable_snd (hinv.mono fun x hx ↦ by simp [hx])
  exact hlabel.and hclock

/-- Reading original labels and clocks from the SAME recovered physical
endpoints recovers the exact original retained latent pair law. -/
theorem original_retained_pair_read_coordinates
    {X Z W : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableEq Z] (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x)
    (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    {L : Set Z} (K : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel K]
    (hmarginals : ∀ᵐ z ∂lambda.restrict L,
      (K z).map Prod.fst ≤ condDistrib u a μ z ∧ (K z).map Prod.snd ≤ condDistrib u a ν z)
    (R : Z → W) (hR : Measurable R) :
    ((((lambda.restrict L ⊗ₘ K).map sameLabelPopulationPair).map (Prod.map b b)).map
      (Prod.map (fun x ↦ (R (a x), u x)) (fun y ↦ (R (a y), u y)))) =
      ((lambda.restrict L ⊗ₘ K).map (Prod.map R id)).map sameLabelPopulationPair := by
  have hs := ae_condDistrib_original_labelClock_right_inverse μ a u ha hu b hb hμinv
  have ht := ae_condDistrib_original_labelClock_right_inverse ν a u ha hu b hb hνinv
  rw [hlabel0] at hs
  rw [hlabel1] at ht
  have hends : ∀ᵐ p ∂lambda.restrict L ⊗ₘ K,
      (a (b (p.1, p.2.1)) = p.1 ∧ u (b (p.1, p.2.1)) = p.2.1) ∧
      (a (b (p.1, p.2.2)) = p.1 ∧ u (b (p.1, p.2.2)) = p.2.2) := by
    apply Measure.ae_compProd_of_ae_ae
    · have hbs : Measurable (fun p : Z × (ℝ × ℝ) ↦ b (p.1, p.2.1)) :=
        hb.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hbt : Measurable (fun p : Z × (ℝ × ℝ) ↦ b (p.1, p.2.2)) :=
        hb.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      exact ((measurableSet_eq_fun (ha.comp hbs) measurable_fst).inter
        (measurableSet_eq_fun (hu.comp hbs) (measurable_fst.comp measurable_snd))).inter
        ((measurableSet_eq_fun (ha.comp hbt) measurable_fst).inter
          (measurableSet_eq_fun (hu.comp hbt) (measurable_snd.comp measurable_snd)))
    · filter_upwards [hmarginals, ae_restrict_of_ae hs, ae_restrict_of_ae ht] with z hm hs ht
      exact ae_pair_endpoints_of_dominated_original_marginals (K z)
        (condDistrib u a μ z) (condDistrib u a ν z) hm.1 hm.2
        (fun t ↦ (a (b (z, t)), u (b (z, t)))) (fun t ↦ (z, t))
        ((hs.1.and hs.2).mono fun t ht ↦ Prod.ext ht.1 ht.2)
        ((ht.1.and ht.2).mono fun t ht ↦ Prod.ext ht.1 ht.2) |>.mono fun p hp ↦
          ⟨⟨congrArg Prod.fst hp.1, congrArg Prod.snd hp.1⟩,
            ⟨congrArg Prod.fst hp.2, congrArg Prod.snd hp.2⟩⟩
  have hread : Measurable (fun x ↦ (R (a x), u x)) := (hR.comp ha).prodMk hu
  rw [sameLabelPair_physical_map_eq _ _ b hb,
    Measure.map_map (hread.prodMap hread) (measurable_labelClockPairPhysicalMap hb),
    Measure.map_map measurable_sameLabelPopulationPair (hR.prodMap measurable_id)]
  apply Measure.map_congr
  filter_upwards [hends] with p hp
  exact Prod.ext (Prod.ext (congrArg R hp.1.1) hp.1.2)
    (Prod.ext (congrArg R hp.2.1) hp.2.2)

end OTSelector.Reconstruction

end
end
