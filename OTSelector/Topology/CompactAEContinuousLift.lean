import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Topology.CompactAEContinuousLift

Conditions: A continuous map injective on a compact phase set, and a continuous interval image equal a.e. to the image of an a.e. compact-valued phase.

Objects: A continuous lift on the whole closed interval, lying in the same compact phase set and agreeing a.e. with the original phase.

Proof detail: The compact image is closed, so a continuous nonnegative distance to it vanishing a.e. vanishes everywhere. Use the compact-to-Hausdorff homeomorphism inverse on that image and injectivity for a.e. equality.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=111): Section 1.8.1, Lemma 1.8.1 and Corollary 1.8.2, p. 102.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6): Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products).

Source relation: Derived compact inverse and positive-interval-measure assembly; a chosen inverse branch is a conclusion, not a premise.
-/

/-!
# Continuous lifts of almost-everywhere compact phases

A continuous injective map on a compact phase set has a continuous inverse on its
closed image. If a continuous interval curve agrees almost everywhere with images
of phases in that set, its entire closed interval lies in the image. It therefore
has a continuous phase lift equal to the original phase almost everywhere.
-/

open Set Filter MeasureTheory Metric Topology
open scoped Topology

noncomputable section

namespace OTSelector.Geometry

/-- Reconstruct a continuous phase on a closed interval from its continuous image
and an almost-everywhere compact phase. No chosen inverse branch is an input. -/
theorem exists_continuous_lift_of_compact_ae
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {K : Set X} {T : X → Y} {z : ℝ → X} {α : ℝ → Y} {a b : ℝ}
    (hab : a < b) (hK : IsCompact K) (hT : ContinuousOn T K) (hinj : InjOn T K)
    (hα : ContinuousOn α (Icc a b))
    (hz : ∀ᵐ t ∂volume.restrict (Ioo a b), z t ∈ K)
    (heq : α =ᵐ[volume.restrict (Ioo a b)] T ∘ z) :
    ∃ zbar : ℝ → X, ContinuousOn zbar (Icc a b) ∧ MapsTo zbar (Icc a b) K ∧
      EqOn (T ∘ zbar) α (Icc a b) ∧
      (zbar =ᵐ[volume.restrict (Ioo a b)] z) := by
  classical
  have hKne : K.Nonempty := by
    by_contra h
    have hfalse : ∀ᵐ t ∂volume.restrict (Ioo a b), False := by
      filter_upwards [hz] with t ht
      exact h ⟨z t, ht⟩
    have hnull : volume.restrict (Ioo a b) = 0 := by
      simpa only [ae_iff, not_false_eq_true, Set.ofPred_true, Measure.measure_univ_eq_zero]
        using hfalse
    have hle := (Measure.measure_Ioo_eq_zero volume).mp (Measure.restrict_eq_zero.mp hnull)
    exact (not_le.mpr hab) hle
  obtain ⟨k, hk⟩ := hKne
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T' : K → Y := fun w ↦ T w
  have hTc : Continuous T' := continuousOn_iff_continuous_domRestrict.mp hT
  have hTi : Function.Injective T' := by
    intro u v huv
    exact Subtype.ext (hinj u.property v.property huv)
  have hemb : IsClosedEmbedding T' := hTc.isClosedEmbedding hTi
  let S : Set Y := range T'
  have hSc : IsClosed S := hemb.isClosed_range
  have hSne : S.Nonempty := ⟨T k, ⟨⟨k, hk⟩, rfl⟩⟩
  have hzero : (fun t ↦ infDist (α t) S) =ᵐ[volume.restrict (Icc a b)] (fun _ ↦ 0) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hz, heq] with t hzt ht
    apply infDist_zero_of_mem
    exact ⟨⟨z t, hzt⟩, ht.symm⟩
  have hall : EqOn (fun t ↦ infDist (α t) S) (fun _ ↦ 0) (Icc a b) :=
    Measure.eqOn_Icc_of_ae_eq volume hab.ne hzero
      ((continuous_infDist_pt S).comp_continuousOn hα) continuousOn_const
  have hαS (t : ℝ) (ht : t ∈ Icc a b) : α t ∈ S :=
    (hSc.mem_iff_infDist_zero hSne).mpr (hall ht)
  let e : K ≃ₜ S := hemb.isEmbedding.toHomeomorph
  let β : Icc a b → S := fun t ↦ ⟨α t, hαS t t.property⟩
  have hβ : Continuous β := (continuousOn_iff_continuous_domRestrict.mp hα).subtype_mk _
  let zbar : ℝ → X := fun t ↦ if ht : t ∈ Icc a b then
    (e.symm ⟨α t, hαS t ht⟩).val else k
  have hzbar (t : ℝ) (ht : t ∈ Icc a b) :
      zbar t = (e.symm ⟨α t, hαS t ht⟩).val := by simp only [zbar, dite_eq_left ht]
  have hzcont : ContinuousOn zbar (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun t : Icc a b ↦ zbar t) =
        (fun t : Icc a b ↦ (e.symm (β t)).val) := by
      funext t
      exact hzbar t t.property
    change Continuous (fun t : Icc a b ↦ zbar t)
    rw [he]
    exact continuous_subtype_val.comp (e.symm.continuous.comp hβ)
  have hzK : MapsTo zbar (Icc a b) K := by
    intro t ht
    rw [hzbar t ht]
    exact (e.symm ⟨α t, hαS t ht⟩).property
  have hzT : EqOn (T ∘ zbar) α (Icc a b) := by
    intro t ht
    change T (zbar t) = α t
    rw [hzbar t ht]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨α t, hαS t ht⟩)
  refine ⟨zbar, hzcont, hzK, hzT, ?_⟩
  filter_upwards [hz, heq, ae_restrict_mem measurableSet_Ioo] with t hzt ht htin
  exact hinj (hzK (Ioo_subset_Icc_self htin)) hzt
    ((hzT (Ioo_subset_Icc_self htin)).trans ht)

end OTSelector.Geometry
