import OTSelector.Reconstruction.FinslerSeedLabelReference

/-!
# Selecting an actual seed from the original conditional population

The normalized original conditional density selects an actual calibrated seed with
nonzero fixed label reference. Haar-almost-everywhere geometric producers therefore
apply to the original common label law, without a supplied good-label selector.
-/

open Set MeasureTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] [BorelSpace M] [MeasurableSpace.CountablySeparated Z] in
/-- Normalization selects a genuine original window label with nonzero reference density. -/
theorem PopulationConditionalWindowLaw.ae_exists_window_reference_ne_zero
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowSelectionMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (horder : let _instWindowSelectionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∀ᵐ z ∂lambda, ∃ (j : ℕ) (x : (P j).domain),
      a ((P j).seed.curve x.val.2 0) = z ∧
        (populationWindowLabelReference P a κ j).rnDeriv lambda z ≠ 0 := by
  classical
  filter_upwards [hlaw.normalized] with z hz
  have hex : ∃ s : ℝ, populationConditionalDensity P a κ lambda ρ v (z, s) ≠ 0 := by
    by_contra hn
    push Not at hn
    simp only [hn, lintegral_zero] at hz
    exact zero_ne_one hz
  obtain ⟨s, hs⟩ := hex
  have hexj : ∃ j : ℕ, (populationWindowLabelReference P a κ j).rnDeriv lambda z *
      populationWindowDensity P a ρ v j (z, s) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hs
    unfold populationConditionalDensity
    simp only [hn, tsum_zero]
  obtain ⟨j, hj⟩ := hexj
  have hfactor := (mul_ne_zero_iff.mp hj)
  have hrange : (z, s) ∈ range (fun x : (P j).domain ↦
      (a ((P j).toManifold x), u ((P j).toManifold x))) := by
    by_contra hn
    apply hfactor.2
    exact Function.extend_apply' _ _ _ hn
  obtain ⟨x, hx⟩ := hrange
  refine ⟨j, x, ?_, hfactor.1⟩
  exact ((P j).label_toManifold_eq_initial hF hcomplete hu horder x.property).symm.trans
    (congrArg Prod.fst hx)

/-- The original common label law selects a complete seed with a finite nonzero
full-seed factor. This same seed can be used for both physical populations. -/
theorem PopulationConditionalWindowLaw.ae_exists_seed_reference_ne_zero
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedSelectionMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instSeedSelectionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j)) :
    ∀ᵐ z ∂lambda, ∃ (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z ≠ 0 ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z < (∞ : ℝ≥0∞) := by
  have hLabelFinite : IsFiniteMeasure lambda := hlaw.label_law ▸ inferInstance
  have hRN (j : ℕ) := by
    let _instSeedSelectionReference : SigmaFinite (κ j) := hκ j
    exact ae_populationWindow_rnDeriv_eq_seed (P j) hF hcomplete hu ha hinj (κ j) lambda
  filter_upwards [hlaw.ae_exists_window_reference_ne_zero hF hcomplete hu horder,
    ae_all_iff.mpr hRN] with z hz hsame
  obtain ⟨j, x, hx, hnonzero⟩ := hz
  have hw := ((Set.ext_iff.mp (P j).domain_eq_prod x.val).mp x.property).2
  have heq := (hsame j).2 x.val.2 hw hx
  refine ⟨j, x.val.2, hw.1.1, hx, ?_, (hsame j).1⟩
  exact heq ▸ hnonzero

/-- A Haar-almost-everywhere geometric producer on each original seed supplies
one good seed for almost every common population label. The seed is selected
from the normalized physical conditional law, with finite nonzero reference factor. -/
theorem PopulationConditionalWindowLaw.ae_exists_good_seed
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda η ρ v)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGoodSeedMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instGoodSeedOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j)) (Good : ∀ j, (P j).seed.covector.ker → Prop)
    (hgood : ∀ j, ∀ᵐ w ∂(κ j).restrict (P j).seed.labels, Good j w) :
    ∀ᵐ z ∂lambda, ∃ (j : ℕ) (w : (P j).seed.covector.ker),
      w ∈ (P j).seed.labels ∧ a ((P j).seed.curve w 0) = z ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z ≠ 0 ∧
        (populationSeedLabelReference (P j).seed a (κ j)).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
        Good j w := by
  have hLabelFinite : IsFiniteMeasure lambda := hlaw.label_law ▸ inferInstance
  have hGoodLabel (j : ℕ) := by
    let _instGoodSeedReference : SigmaFinite (κ j) := hκ j
    exact ae_populationSeedLabel_property (P j).seed hF hcomplete hu ha hinj (κ j)
      lambda (hgood j)
  filter_upwards [hlaw.ae_exists_seed_reference_ne_zero hF hcomplete hu ha hinj horder hκ,
    ae_all_iff.mpr hGoodLabel] with z hz hG
  obtain ⟨j, w, hw, hwz, hnonzero, hfinite⟩ := hz
  exact ⟨j, w, hw, hwz, hnonzero, hfinite, hG j hnonzero w hw hwz⟩

end OTSelector.Reconstruction
