import OTSelector.Probability.LabelClockConditionalDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.NormalizedLabelClockDensity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.NormalizedLabelClockDensity`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.NormalizedLabelClockDensity

## Lemma skeleton

* **Conditions:** A finite original joint label-clock law with a measurable product density relative to a sigma-finite label reference, plus inherited measurable maps.
* **Objects:** The actual label density is the scalar section normalizer; normalized sections give the original conditional laws and their positive finite reciprocal density.
* **Proof detail:** Compute the first marginal by Tonelli, show the normalizer finite reference-almost everywhere and positive actual-label-almost everywhere, change the reference by its reciprocal and identify conditional densities.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.

Source relation (composition): Normalizer is derived from the actual joint law. Zero-mass labels are removed only almost everywhere under the actual label marginal.
-/

/-!
# Normalizing the original label-clock density

A density of the original joint law with respect to a sigma-finite label reference
determines its own normalizer. Its section mass is the actual label density, and
division by that mass gives the original conditional clock laws. Zero-mass labels
are discarded only almost everywhere under the actual label law.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- The mass of a clock section of a joint density. -/
noncomputable def labelClockNormalizer {Z : Type*} (G : Z × ℝ → ℝ≥0∞) (z : Z) : ℝ≥0∞ :=
  ∫⁻ t, G (z, t)

section

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
  (eta : Measure M) [IsFiniteMeasure eta]
  {a : M → Z} {u : M → ℝ} (hu : Measurable u)
  (beta : Measure Z) [SigmaFinite beta]
  {G : Z × ℝ → ℝ≥0∞} (hG : Measurable G)
  (hjoint : eta.map (fun x ↦ (a x, u x)) =
    (beta.prod (volume : Measure ℝ)).withDensity G)

include hu hG hjoint

omit [IsFiniteMeasure eta] in
/-- The section mass is the density of the original label marginal. -/
theorem map_label_eq_withDensity_normalizer :
    eta.map a = beta.withDensity (labelClockNormalizer G) := by
  have hfst : beta.withDensity (labelClockNormalizer G) =
      ((beta.prod (volume : Measure ℝ)).withDensity G).fst := by
    ext A hA
    rw [withDensity_apply _ hA, Measure.fst_apply hA,
      withDensity_apply _ (measurable_fst hA), ← prod_univ]
    simpa only [labelClockNormalizer, setLIntegral_univ] using
      (setLIntegral_prod (μ := beta) (ν := (volume : Measure ℝ)) (s := A) (t := univ)
        G hG.aemeasurable.restrict).symm
  rw [← hjoint, Measure.fst_map_prodMk hu] at hfst
  exact hfst.symm

/-- Finite population mass makes the section mass finite at reference-almost every label. -/
theorem ae_labelClockNormalizer_lt_top_reference :
    ∀ᵐ z ∂beta, labelClockNormalizer G z < ∞ := by
  apply ae_lt_top (f := labelClockNormalizer G) hG.lintegral_prod_right'
  have hmass : (∫⁻ z, labelClockNormalizer G z ∂beta) = (eta.map a) univ := by
    rw [map_label_eq_withDensity_normalizer eta hu beta hG hjoint,
      withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [hmass]
  exact measure_ne_top _ _

/-- The constructed normalizer is positive and finite under the actual label law. -/
theorem ae_labelClockNormalizer_pos_lt_top :
    ∀ᵐ z ∂eta.map a, 0 < labelClockNormalizer G z ∧ labelClockNormalizer G z < ∞ := by
  have htheta : Measurable (labelClockNormalizer G) := hG.lintegral_prod_right'
  rw [map_label_eq_withDensity_normalizer eta hu beta hG hjoint,
    ae_withDensity_iff htheta]
  filter_upwards [ae_labelClockNormalizer_lt_top_reference eta hu beta hG hjoint] with z hz
  exact fun hzero ↦ ⟨pos_iff_ne_zero.mpr hzero, hz⟩

/-- The inverse normalizer is the reverse Radon–Nikodym derivative on actual labels;
positivity on all labels of the original reference is unnecessary. -/
theorem ae_rnDeriv_label_eq_inv_normalizer :
    beta.rnDeriv (eta.map a) =ᵐ[eta.map a] fun z ↦ (labelClockNormalizer G z)⁻¹ := by
  have hlabel := map_label_eq_withDensity_normalizer eta hu beta hG hjoint
  have hac : eta.map a ≪ beta := by
    rw [hlabel]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (eta.map a).rnDeriv beta =ᵐ[beta] labelClockNormalizer G := by
    rw [hlabel]
    exact Measure.rnDeriv_withDensity beta hG.lintegral_prod_right'
  filter_upwards [Measure.inv_rnDeriv hac, hac.ae_eq hrn] with z hinv hz
  exact hinv.symm.trans (congrArg Inv.inv hz)

/-- Dividing by the derived section mass rewrites the same original joint law
over its actual label marginal. Zero section masses require no extra hypothesis. -/
theorem map_labelClock_eq_withDensity_normalized :
    eta.map (fun x ↦ (a x, u x)) =
      ((eta.map a).prod (volume : Measure ℝ)).withDensity
        (fun y ↦ G y / labelClockNormalizer G y.1) := by
  have htheta : Measurable (labelClockNormalizer G) := hG.lintegral_prod_right'
  have hthetafst : Measurable (fun y : Z × ℝ ↦ labelClockNormalizer G y.1) :=
    htheta.comp measurable_fst
  have hh : Measurable (fun y : Z × ℝ ↦ G y / labelClockNormalizer G y.1) :=
    hG.div hthetafst
  have hcancel : (fun y : Z × ℝ ↦ labelClockNormalizer G y.1 *
      (G y / labelClockNormalizer G y.1)) =ᵐ[beta.prod (volume : Measure ℝ)] G := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun (hthetafst.mul hh) hG)).mpr
    filter_upwards [ae_labelClockNormalizer_lt_top_reference eta hu beta hG hjoint] with z hz
    by_cases hzero : labelClockNormalizer G z = 0
    · have hsection : (fun t ↦ G (z, t)) =ᵐ[(volume : Measure ℝ)] 0 :=
        (lintegral_eq_zero_iff (hG.comp measurable_prodMk_left)).mp hzero
      filter_upwards [hsection] with t ht
      change labelClockNormalizer G z * (G (z, t) / labelClockNormalizer G z) = G (z, t)
      simp only [hzero, zero_mul, ht, Pi.zero_apply]
    · exact Filter.Eventually.of_forall fun t ↦ ENNReal.mul_div_cancel hzero hz.ne
  rw [map_label_eq_withDensity_normalizer eta hu beta hG hjoint,
    prod_withDensity_left htheta, ← withDensity_mul _ hthetafst hh]
  exact hjoint.trans (withDensity_congr_ae hcancel).symm

/-- A density over any sigma-finite label reference supplies the joint absolute
continuity needed by the original conditional and countable-atlas consumers. -/
theorem map_labelClock_absolutelyContinuous_of_density :
    eta.map (fun x ↦ (a x, u x)) ≪ (eta.map a).prod (volume : Measure ℝ) := by
  rw [map_labelClock_eq_withDensity_normalized eta hu beta hG hjoint]
  exact withDensity_absolutelyContinuous _ _

/-- The normalized sections are the existing conditional clock distributions
of the original finite population measure. -/
theorem ae_condDistrib_eq_withDensity_normalized :
    ∀ᵐ z ∂eta.map a, condDistrib u a eta z =
      (volume : Measure ℝ).withDensity (fun t ↦ G (z, t) / labelClockNormalizer G z) := by
  have hh : Measurable (fun y : Z × ℝ ↦ G y / labelClockNormalizer G y.1) :=
    hG.div (hG.lintegral_prod_right'.comp measurable_fst)
  filter_upwards [ae_withDensity_clock_eq_condDistrib eta hu hh
    (map_labelClock_eq_withDensity_normalized eta hu beta hG hjoint).symm] with z hz
  exact hz.symm

end

/-- A normalized section with interval-supported real density has the exact real
normalizer used by the Jacobi moment estimates. No density lower bound is required. -/
theorem withDensity_div_eq_restrict_ofReal
    {I : Set ℝ} (hI : MeasurableSet I) {d : ℝ → ℝ} {G : ℝ → ℝ≥0∞}
    {θ : ℝ≥0∞} (hθ0 : 0 < θ) (hθtop : θ < ∞)
    (hG : G =ᵐ[(volume : Measure ℝ)] I.indicator (fun t ↦ ENNReal.ofReal (d t))) :
    (volume : Measure ℝ).withDensity (fun t ↦ G t / θ) =
      (volume.restrict I).withDensity (fun t ↦ ENNReal.ofReal (d t / θ.toReal)) := by
  rw [← withDensity_indicator hI]
  apply withDensity_congr_ae
  filter_upwards [hG] with t ht
  rw [ht]
  by_cases htI : t ∈ I
  · simp only [indicator_of_mem htI]
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos_iff.mpr ⟨hθ0, hθtop⟩),
      ENNReal.ofReal_toReal hθtop.ne]
  · simp only [indicator_of_notMem htI, ENNReal.zero_div]

end OTSelector.Reconstruction

end
