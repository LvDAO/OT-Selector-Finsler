import OTSelector.MeasureTheory.ProductReferenceDensity
import OTSelector.Probability.LabelClockConditionalDensity

/-!
Conditions: A finite original measure, a measurable label-clock map with measurable a.e. left inverse, absolute continuity of the actual joint law and an exact product-reference density for the window restriction.

Objects: Measurable clock window sections and the raw restriction of the actual conditional law as a Lebesgue density multiplied by the fixed label RN factor; overlap density uniqueness.

Proof detail: Push restriction through the a.e. inverse, disintegrate the exact restricted joint density and compare actual conditional kernels using RN uniqueness; restrict overlapping formulas again to identify densities a.e.

References: D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary; D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: A raw conditional restriction/density transport theorem. The restricted population is not probability-normalized, and the label reference RN factor is retained rather than silently canceled.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConditionalWindowRestriction.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConditionalWindowRestriction`; the selected original proof blocks follow. -/
section

/-!
# Restricting the original conditional law to a geometric window

A measurable inverse of the original label-clock map turns a physical window
into measurable clock sections. Its exact product-reference density then gives
the restriction of the original conditional distribution, with the fixed label
Radon--Nikodym factor. No normalization of the restricted population is used.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- An almost-everywhere left inverse transports restriction to its inverse image. -/
theorem map_restrict_eq_restrict_map_of_ae_leftInverse
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (η : Measure X) {f : X → Y} {b : Y → X}
    (hf : Measurable f) (hb : Measurable b)
    (hinv : ∀ᵐ x ∂η, b (f x) = x) {C : Set X} (hC : MeasurableSet C) :
    (η.restrict C).map f = (η.map f).restrict (b ⁻¹' C) := by
  rw [Measure.restrict_map hf (hC.preimage hb)]
  congr 1
  apply Measure.restrict_congr_set
  filter_upwards [hinv] with x hx
  change (x ∈ C) = (b (f x) ∈ C)
  rw [hx]

/-- A product-reference density of a joint-law restriction identifies the same
restriction of its original conditional clock laws. -/
theorem ae_condDistrib_restrict_eq_withDensity_of_joint_restriction
    (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} (hu : Measurable u)
    (hjoint : η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume)
    {S : Set (Z × ℝ)} (hS : MeasurableSet S)
    (β : Measure Z) [SigmaFinite β]
    {G : Z × ℝ → ℝ≥0∞} (hG : Measurable G)
    (hwindow : (η.map (fun x ↦ (a x, u x))).restrict S =
      (β.prod (volume : Measure ℝ)).withDensity G) :
    ∀ᵐ z ∂η.map a, β.rnDeriv (η.map a) z < ∞ ∧
      (condDistrib u a η z).restrict {t | (z, t) ∈ S} =
        (volume : Measure ℝ).withDensity (fun t ↦ β.rnDeriv (η.map a) z * G (z, t)) := by
  let R := (η.map a).prod (volume : Measure ℝ)
  let H := (η.map (fun x ↦ (a x, u x))).rnDeriv R
  have hH : Measurable H := Measure.measurable_rnDeriv _ _
  have hden : R.withDensity H = η.map (fun x ↦ (a x, u x)) :=
    Measure.withDensity_rnDeriv_eq _ _ hjoint
  have hrestrict : (η.map (fun x ↦ (a x, u x))).restrict S =
      R.withDensity (S.indicator H) := by
    rw [← hden, restrict_withDensity hS, ← withDensity_indicator hS]
  have hRN : ((η.map (fun x ↦ (a x, u x))).restrict S).rnDeriv R =ᵐ[R]
      S.indicator H := by
    rw [hrestrict]
    exact Measure.rnDeriv_withDensity R (hH.indicator hS)
  have hRN' : ((η.map (fun x ↦ (a x, u x))).restrict S).rnDeriv R =ᵐ[R]
      (fun y ↦ β.rnDeriv (η.map a) y.1 * G y) := by
    rw [hwindow]
    exact rnDeriv_prod_withDensity (η.map a) β volume hG
  have hsections := Measure.ae_ae_of_ae_prod (hRN.symm.trans hRN')
  have hcond := ae_withDensity_clock_eq_condDistrib η hu hH hden
  filter_upwards [β.rnDeriv_lt_top (η.map a), hsections, hcond] with z hz hs hc
  refine ⟨hz, ?_⟩
  have hSz : MeasurableSet {t | (z, t) ∈ S} := hS.preimage measurable_prodMk_left
  rw [← hc, restrict_withDensity hSz, ← withDensity_indicator hSz]
  exact withDensity_congr_ae hs

/-- The physical window density is the density of the original conditional law
restricted to that window's clock section. The label factor is finite almost everywhere. -/
theorem ae_condDistrib_restrict_eq_withDensity_window
    (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    {b : Z × ℝ → M} (hb : Measurable b)
    (hinv : ∀ᵐ x ∂η, b (a x, u x) = x)
    (hjoint : η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume)
    {C : Set M} (hC : MeasurableSet C)
    (β : Measure Z) [SigmaFinite β]
    {G : Z × ℝ → ℝ≥0∞} (hG : Measurable G)
    (hwindow : (η.restrict C).map (fun x ↦ (a x, u x)) =
      (β.prod (volume : Measure ℝ)).withDensity G) :
    ∀ᵐ z ∂η.map a, β.rnDeriv (η.map a) z < ∞ ∧
      (condDistrib u a η z).restrict {t | b (z, t) ∈ C} =
        (volume : Measure ℝ).withDensity (fun t ↦ β.rnDeriv (η.map a) z * G (z, t)) := by
  apply ae_condDistrib_restrict_eq_withDensity_of_joint_restriction η hu hjoint
    (hC.preimage hb) β hG
  rw [← map_restrict_eq_restrict_map_of_ae_leftInverse η (ha.prodMk hu) hb hinv hC]
  exact hwindow

/-- A window in recovered coordinates, including the actual label and clock readouts. -/
def labelClockWindowRegion (a : M → Z) (u : M → ℝ) (b : Z × ℝ → M)
    (C : Set M) : Set (Z × ℝ) :=
  {y | b y ∈ C ∧ a (b y) = y.1 ∧ u (b y) = y.2}

/-- The exact clock section of a recovered geometric window. -/
def labelClockWindowSection (a : M → Z) (u : M → ℝ) (b : Z × ℝ → M)
    (C : Set M) (z : Z) : Set ℝ :=
  {t | (z, t) ∈ labelClockWindowRegion a u b C}

/-- The recovered window is measurable. -/
theorem measurableSet_labelClockWindowRegion [MeasurableEq Z]
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M} {C : Set M}
    (ha : Measurable a) (hu : Measurable u) (hb : Measurable b) (hC : MeasurableSet C) :
    MeasurableSet (labelClockWindowRegion a u b C) :=
  (hC.preimage hb).inter
    ((measurableSet_eq_fun (ha.comp hb) measurable_fst).inter
      (measurableSet_eq_fun (hu.comp hb) measurable_snd))

omit [MeasurableSpace M] [MeasurableSpace Z] in
/-- The recovered region is exactly the label-clock image wherever the inverse is valid. -/
theorem labelClockWindowRegion_eq_image
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M} {C : Set M}
    (hinv : ∀ x ∈ C, b (a x, u x) = x) :
    labelClockWindowRegion a u b C = (fun x ↦ (a x, u x)) '' C := by
  ext y
  constructor
  · intro hy
    exact ⟨b y, hy.1, Prod.ext hy.2.1 hy.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rwa [hinv x hx], by rw [hinv x hx], by rw [hinv x hx]⟩

/-- Requiring correct readout removes arbitrary values of the inverse outside its image
while preserving the exact restriction of the original conditional law. -/
theorem ae_condDistrib_restrict_windowSection [MeasurableEq Z]
    (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    {b : Z × ℝ → M} (hb : Measurable b)
    (hinv : ∀ᵐ x ∂η, b (a x, u x) = x)
    (hjoint : η.map (fun x ↦ (a x, u x)) ≪ (η.map a).prod volume)
    {C : Set M} (hC : MeasurableSet C)
    (β : Measure Z) [SigmaFinite β]
    {G : Z × ℝ → ℝ≥0∞} (hG : Measurable G)
    (hwindow : (η.restrict C).map (fun x ↦ (a x, u x)) =
      (β.prod (volume : Measure ℝ)).withDensity G) :
    ∀ᵐ z ∂η.map a, β.rnDeriv (η.map a) z < ∞ ∧
      (condDistrib u a η z).restrict (labelClockWindowSection a u b C z) =
        (volume : Measure ℝ).withDensity (fun t ↦ β.rnDeriv (η.map a) z * G (z, t)) := by
  have hS := measurableSet_labelClockWindowRegion ha hu hb hC
  apply ae_condDistrib_restrict_eq_withDensity_of_joint_restriction η hu hjoint hS β hG
  rw [Measure.restrict_map (ha.prodMk hu) hS]
  have heq : η.restrict ((fun x ↦ (a x, u x)) ⁻¹'
      labelClockWindowRegion a u b C) = η.restrict C := by
    apply Measure.restrict_congr_set
    filter_upwards [hinv] with x hx
    change (b (a x, u x) ∈ C ∧ a (b (a x, u x)) = a x ∧
      u (b (a x, u x)) = u x) = (x ∈ C)
    simp only [hx, and_self, and_true]
  rw [heq]
  exact hwindow

/-- Two densities of restrictions of the same measure agree on their overlap. -/
theorem density_eq_ae_on_overlap_of_restrict_eq
    (μ : Measure ℝ) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hμS : μ.restrict S = volume.withDensity f)
    (hμT : μ.restrict T = volume.withDensity g) :
    f =ᵐ[volume.restrict (S ∩ T)] g := by
  have hI : MeasurableSet (S ∩ T) := hS.inter hT
  have hfI := congrArg (fun ν : Measure ℝ ↦ ν.restrict (S ∩ T)) hμS
  have hgI := congrArg (fun ν : Measure ℝ ↦ ν.restrict (S ∩ T)) hμT
  rw [Measure.restrict_restrict_of_subset inter_subset_left, restrict_withDensity hI] at hfI
  rw [Measure.restrict_restrict_of_subset inter_subset_right, restrict_withDensity hI] at hgI
  exact (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).mp
    (hfI.symm.trans hgI)

end OTSelector.Reconstruction

end
