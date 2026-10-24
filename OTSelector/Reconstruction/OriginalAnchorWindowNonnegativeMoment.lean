import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell

/-! Arbitrary mark-dependent physical anchor windows have the same original
Haar/true-Palm moment. Target anchoring uses the actual displacement as anchor. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The actual original first-edge kernel readout in a deterministic physical
source window with an arbitrary nonnegative complete paired-mark weight. -/
def legalMarkedAnchorWindowMoment (q : ℕ)
    (anchor : PhysicalPairPalmMark (Fin q) → Fin q → ℝ)
    (h : (Fin q → ℝ) → ℝ≥0∞) (p : PhysicalPairPalmMark (Fin q) → ℝ≥0∞)
    (s : LegalMarkedOptimalInputScene q) : ℝ≥0∞ :=
  ∫⁻ a, h (a.1 + anchor a.2) * p a.2 ∂physicalScenePairKernel s.1

/-- The same original source-window moment is a measurable scene observable. -/
theorem measurable_legalMarkedAnchorWindowMoment {q : ℕ}
    (anchor : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (ha : Measurable anchor)
    {h : (Fin q → ℝ) → ℝ≥0∞} {p : PhysicalPairPalmMark (Fin q) → ℝ≥0∞}
    (hh : Measurable h) (hp : Measurable p) :
    Measurable (legalMarkedAnchorWindowMoment q anchor h p) :=
  ((hh.comp (measurable_fst.add (ha.comp measurable_snd))).mul (hp.comp measurable_snd)).lintegral_kernel.comp measurable_fst

/-- The whole original stationary scene has the exact physical Haar times
true-Palm source-window moment, even for correlated clock/momentum marks. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_anchorWindowMoment
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (anchor : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (ha : Measurable anchor)
    {h : (Fin q → ℝ) → ℝ≥0∞} {p : PhysicalPairPalmMark (Fin q) → ℝ≥0∞}
    (hh : Measurable h) (hp : Measurable p) :
    (∫⁻ s, legalMarkedAnchorWindowMoment q anchor h p s
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      (∫⁻ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫⁻ m, p m ∂legalMarkedJointPalm q M.law := by
  have : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)) :=
    legalMarkedInputPairLaw q M.law
  let G : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞ := fun a ↦ h (a.1 + anchor a.2) * p a.2
  have hG : Measurable G := (hh.comp (measurable_fst.add (ha.comp measurable_snd))).mul (hp.comp measurable_snd)
  have hi := Measure.lintegral_bind (m := P)
    (Kernel.measurable (physicalScenePairKernel : Kernel
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))).aemeasurable hG.aemeasurable
  have hm := lintegral_map (hG.lintegral_kernel (κ := physicalScenePairKernel))
    (measurable_fst : Measurable (Prod.fst : LegalMarkedOptimalInputScene q → _))
    (μ := (M.law : Measure (LegalMarkedOptimalInputScene q)))
  change (∫⁻ a, G a ∂physicalScenePairCampbell P) = _ at hi
  rw [M.campbell_eq_volume_prod_palm] at hi
  exact hm.symm.trans (hi.symm.trans (lintegral_markDependentAnchorTranslation _ anchor ha hh hp))

end OTSelector.Reconstruction
