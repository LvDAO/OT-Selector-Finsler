import OTSelector.MeasureTheory.HaarLipschitzDistortion
import OTSelector.Topology.CompactFlowMeasurableImage
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FlowScalarAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FlowScalarAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.FlowScalarAbsoluteContinuity

* **Conditions:** A measurable injective time–position map preserves a measurable label, translates its clock, and has the stated lower image-volume bound on a positive-measure time set.
* **Objects:** Absolute continuity of the actual label–clock pushforward with respect to its actual label marginal times Lebesgue measure, including absolutely continuous input populations.
* **Proof detail:** Remove exceptional labels first, apply Fubini to translated null sections, and transfer image nullity back using the lower-volume inequality; compact and half-Lipschitz variants construct the embedding or volume bound.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38): Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.

Source relation (derived): A measure-theoretic flow criterion motivated by ray disintegration; actual geometric flow and clock identities remain explicit inputs.
-/

/-!
# Absolute continuity from label-preserving short translations

A jointly measurable injective time-position map, clock translation, and a lower
image-volume estimate imply absolute continuity of the actual label-clock law with
respect to its actual label marginal times Lebesgue measure. The proof removes the
exceptional labels before applying Fubini to the time-position image. It does not
use limits of measures. The geometric construction of the maps is a separate input.
-/

open Set MeasureTheory Filter
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
  {μ : Measure M} [SFinite μ] {K : Set M} {I : Set ℝ}
  {a : M → Z} {u : M → ℝ} {T : ℝ → M → M}

/-- A clock-translation family with lower image-volume control forces the original
label-clock law on the core to be absolutely continuous with respect to the original
label marginal times Lebesgue measure, for every population absolutely continuous
with respect to the reference volume. The time set only needs positive measure;
no finiteness of the core or time set is needed for this null-set argument. -/
theorem map_label_clock_absolutelyContinuous_of_flow_of_absolutelyContinuous
    (ν : Measure M) (hν : ν ≪ μ)
    (hK : MeasurableSet K) (hI : volume I ≠ 0)
    (ha : Measurable a) (hu : Measurable u)
    (hemb : MeasurableEmbedding
      (fun q : I × K ↦ ((q.1 : ℝ), T q.1 q.2)))
    (hlabel : ∀ t ∈ I, ∀ x ∈ K, a (T t x) = a x)
    (hclock : ∀ t ∈ I, ∀ x ∈ K, u (T t x) = u x + t)
    (C : ℝ≥0∞)
    (hlower : ∀ t ∈ I, ∀ A : Set M, MeasurableSet A → A ⊆ K →
      μ A ≤ C * μ (T t '' A)) :
    (ν.restrict K).map (fun x ↦ (a x, u x)) ≪ ((ν.restrict K).map a).prod volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hBzero
  have hgood : ∀ᵐ z ∂(ν.restrict K).map a, volume (Prod.mk z ⁻¹' B) = 0 :=
    (Measure.measure_prod_null hB).mp hBzero
  have hgoodK : ∀ᵐ x ∂ν.restrict K, volume (Prod.mk (a x) ⁻¹' B) = 0 :=
    ae_of_ae_map ha.aemeasurable hgood
  let A : Set M := {x | x ∈ K ∧ (a x, u x) ∈ B ∧ volume (Prod.mk (a x) ⁻¹' B) = 0}
  have hAm : MeasurableSet A := by
    exact hK.inter (((ha.prodMk hu) hB).inter
      (((measurable_measure_prodMk_left hB).comp ha) (measurableSet_singleton 0)))
  have hAK : A ⊆ K := fun x hx ↦ hx.1
  let S : Set (ℝ × M) :=
    (fun q : I × K ↦ ((q.1 : ℝ), T q.1 q.2)) '' {q | (q.2 : M) ∈ A}
  have hSm : MeasurableSet S :=
    hemb.measurableSet_image.mpr
      (hAm.preimage (measurable_subtype_coe.comp measurable_snd))
  have htimes (y : M) : volume ((fun t ↦ (t, y)) ⁻¹' S) = 0 := by
    by_cases hy : volume (Prod.mk (a y) ⁻¹' B) = 0
    · apply measure_mono_null (t := (fun t ↦ u y - t) ⁻¹' (Prod.mk (a y) ⁻¹' B))
      · intro t ht
        obtain ⟨q, hq, hqt⟩ := ht
        have htq : (q.1 : ℝ) = t := congrArg Prod.fst hqt
        have hyq : T q.1 q.2 = y := congrArg Prod.snd hqt
        change (a y, u y - t) ∈ B
        rw [← hyq, hlabel _ q.1.property _ q.2.property,
          hclock _ q.1.property _ q.2.property, htq, add_sub_cancel_right]
        exact hq.2.1
      · exact (volume.measurePreserving_sub_left (u y)).quasiMeasurePreserving.preimage_null hy
    · have hempty : (fun t ↦ (t, y)) ⁻¹' S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        obtain ⟨q, hq, hqt⟩ := ht
        have hyq : T q.1 q.2 = y := congrArg Prod.snd hqt
        apply hy
        rw [← hyq, hlabel _ q.1.property _ q.2.property]
        exact hq.2.2
      rw [hempty, measure_empty]
  have hSzero : (volume.prod μ) S = 0 := by
    rw [Measure.prod_apply_symm hSm]
    simp only [htimes, lintegral_zero]
  have hsections : ∀ᵐ t ∂volume, μ (Prod.mk t ⁻¹' S) = 0 :=
    (Measure.measure_prod_null hSm).mp hSzero
  obtain ⟨t, ht, htzero⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hI (ae_restrict_of_ae hsections)
  have hsection : Prod.mk t ⁻¹' S = T t '' A := by
    ext y
    constructor
    · rintro ⟨q, hq, hqy⟩
      have htq : (q.1 : ℝ) = t := congrArg Prod.fst hqy
      exact ⟨q.2, hq, htq ▸ congrArg Prod.snd hqy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟨t, ht⟩, ⟨x, hAK hx⟩), hx, rfl⟩
  rw [hsection] at htzero
  have hAzero : μ A = 0 := by
    have h : μ A ≤ 0 := by
      simpa only [htzero, mul_zero] using hlower t ht A hAm hAK
    exact le_antisymm h zero_le
  have hnotA : ∀ᵐ x ∂ν.restrict K, x ∉ A := by
    apply ae_restrict_of_ae
    apply ae_iff.mpr
    simpa using hν hAzero
  have hnotB : ∀ᵐ x ∂ν.restrict K, (a x, u x) ∉ B := by
    filter_upwards [hgoodK, ae_restrict_mem hK, hnotA] with x hxgood hxK hxA
    exact fun hxB ↦ hxA ⟨hxK, hxB, hxgood⟩
  rw [Measure.map_apply (ha.prodMk hu) hB]
  change (ν.restrict K) {x | (a x, u x) ∈ B} = 0
  simpa only [not_not] using (ae_iff.mp hnotB)

/-- The reference-measure specialization uses the actual reference label marginal. -/
theorem map_label_clock_absolutelyContinuous_of_flow
    (hK : MeasurableSet K) (hI : volume I ≠ 0)
    (ha : Measurable a) (hu : Measurable u)
    (hemb : MeasurableEmbedding
      (fun q : I × K ↦ ((q.1 : ℝ), T q.1 q.2)))
    (hlabel : ∀ t ∈ I, ∀ x ∈ K, a (T t x) = a x)
    (hclock : ∀ t ∈ I, ∀ x ∈ K, u (T t x) = u x + t)
    (C : ℝ≥0∞)
    (hlower : ∀ t ∈ I, ∀ A : Set M, MeasurableSet A → A ⊆ K →
      μ A ≤ C * μ (T t '' A)) :
    (μ.restrict K).map (fun x ↦ (a x, u x)) ≪ ((μ.restrict K).map a).prod volume :=
  map_label_clock_absolutelyContinuous_of_flow_of_absolutelyContinuous μ
    Measure.AbsolutelyContinuous.rfl hK hI ha hu hemb hlabel hclock C hlower

/-- Compactness, continuity and slice injectivity construct the measurable embedding
used in the Fubini argument. No separate image-measurability input is needed. -/
theorem map_label_clock_absolutelyContinuous_of_compact_flow
    [TopologicalSpace M] [T2Space M] [BorelSpace M]
    (ν : Measure M) (hν : ν ≪ μ)
    (hK : IsCompact K) (hI : IsCompact I) (hIpos : volume I ≠ 0)
    (ha : Measurable a) (hu : Measurable u)
    (hT : ContinuousOn (fun q : ℝ × M ↦ (q.1, T q.1 q.2)) (I ×ˢ K))
    (hinj : ∀ t ∈ I, InjOn (T t) K)
    (hlabel : ∀ t ∈ I, ∀ x ∈ K, a (T t x) = a x)
    (hclock : ∀ t ∈ I, ∀ x ∈ K, u (T t x) = u x + t)
    (C : ℝ≥0∞)
    (hlower : ∀ t ∈ I, ∀ A : Set M, MeasurableSet A → A ⊆ K →
      μ A ≤ C * μ (T t '' A)) :
    (ν.restrict K).map (fun x ↦ (a x, u x)) ≪ ((ν.restrict K).map a).prod volume :=
  map_label_clock_absolutelyContinuous_of_flow_of_absolutelyContinuous ν hν
    hK.measurableSet hIpos ha hu
    (Geometry.measurableEmbedding_compact_skewFlow hI hK hT hinj)
    hlabel hclock C hlower

/-- For an actual half-Lipschitz displacement in a finite-dimensional space, Haar
image distortion supplies all lower-volume and injectivity inputs. The conclusion
uses the original population's own label marginal, with no density lower bound. -/
theorem map_label_clock_absolutelyContinuous_of_half_lipschitz_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (m ν : Measure E) [m.IsAddHaarMeasure] (hν : ν ≪ m)
    {K S : Set E} {I : Set ℝ} {a : E → Z} {u : E → ℝ} {T : ℝ → E → E}
    (hK : IsCompact K) (hKS : K ⊆ S) (hI : IsCompact I) (hIpos : volume I ≠ 0)
    (ha : Measurable a) (hu : Measurable u)
    (hT : ContinuousOn (fun q : ℝ × E ↦ (q.1, T q.1 q.2)) (I ×ˢ K))
    (hres : ∀ t ∈ I, LipschitzOnWith (1 / 2) (fun x ↦ T t x - x) S)
    (hlabel : ∀ t ∈ I, ∀ x ∈ K, a (T t x) = a x)
    (hclock : ∀ t ∈ I, ∀ x ∈ K, u (T t x) = u x + t) :
    (ν.restrict K).map (fun x ↦ (a x, u x)) ≪ ((ν.restrict K).map a).prod volume := by
  apply map_label_clock_absolutelyContinuous_of_flow_of_absolutelyContinuous ν hν
    hK.measurableSet hIpos ha hu
    (Geometry.measurableEmbedding_compact_skewFlow_of_half_lipschitz_displacement
      hI hK hKS hT hres) hlabel hclock ((2 : ℝ≥0∞) ^ Module.finrank ℝ E)
  intro t ht A _ hAK
  exact (Geometry.haar_image_distortion_of_half_lipschitz_displacement m
    (hres t ht)).2.2.2 A (hAK.trans hKS) |>.2

end OTSelector.Reconstruction

end
