import OTSelector.PointProcess.LocalConfigurationMaskedTuple
import OTSelector.Probability.IIDLaplaceLimit

/-!
# Actual original iid laws on masked local configurations

Each color is sampled from its unchanged full probability law. Its deterministic
endpoint mask selects original labels before the existing local-configuration
encoding, retaining coincident observations and their multiplicities. The joint
law is the pushforward of the original independent product, without conditioning,
normalizing restricted laws or changing the coupling.

The only asymptotic inputs are scaled one-point defects on the original masked
sets. Identifying their geometric limits and identifying a limiting Poisson law
are separate steps.
-/

open Set Function MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported

noncomputable section
namespace OTSelector.Probability
open OTSelector.PointProcess

section Finite

variable {ΩS ΩT X Y : Type*} [MeasurableSpace ΩS] [MeasurableSpace ΩT]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]

/-- Actual joint law of the two masked configuration observations, obtained by
pushing forward the full original independent finite-array law. -/
def originalIidMaskedConfigurationPairLaw
    (μ : Measure ΩS) (ν : Measure ΩT) (NS NT : ℕ) (baseX : X) (baseY : Y)
    (HS : Set ΩS) (HT : Set ΩT) (obsS : ΩS → X) (obsT : ΩT → Y) :
    Measure (LocalConfiguration baseX × LocalConfiguration baseY) :=
  ((Measure.pi (fun _ : Fin NS ↦ μ)).prod (Measure.pi (fun _ : Fin NT ↦ ν))).map
    (fun z ↦ (LocalConfiguration.ofMaskedTuple baseX HS obsS z.1,
      LocalConfiguration.ofMaskedTuple baseY HT obsT z.2))

private theorem measurable_maskedConfigurationPair
    (NS NT : ℕ) (baseX : X) (baseY : Y) {HS : Set ΩS} {HT : Set ΩT}
    (hHS : MeasurableSet HS) (hHT : MeasurableSet HT)
    {obsS : ΩS → X} {obsT : ΩT → Y} (hobsS : Measurable obsS) (hobsT : Measurable obsT) :
    Measurable (fun z : (Fin NS → ΩS) × (Fin NT → ΩT) ↦
      (LocalConfiguration.ofMaskedTuple baseX HS obsS z.1,
        LocalConfiguration.ofMaskedTuple baseY HT obsT z.2)) :=
  ((LocalConfiguration.measurable_ofMaskedTuple baseX hHS hobsS NS).comp measurable_fst).prodMk
    ((LocalConfiguration.measurable_ofMaskedTuple baseY hHT hobsT NT).comp measurable_snd)

/-- The actual pushforward is a probability law even when either retained set
has zero mass or empty interior. -/
theorem isProbabilityMeasure_originalIidMaskedConfigurationPairLaw
    (μ : Measure ΩS) (ν : Measure ΩT) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (NS NT : ℕ) (baseX : X) (baseY : Y) {HS : Set ΩS} {HT : Set ΩT}
    (hHS : MeasurableSet HS) (hHT : MeasurableSet HT)
    {obsS : ΩS → X} {obsT : ΩT → Y} (hobsS : Measurable obsS) (hobsT : Measurable obsT) :
    IsProbabilityMeasure
      (originalIidMaskedConfigurationPairLaw μ ν NS NT baseX baseY HS HT obsS obsT) :=
  Measure.isProbabilityMeasure_map
    (measurable_maskedConfigurationPair NS NT baseX baseY hHS hHT hobsS hobsT).aemeasurable

/-- Reading compact tests under the actual configuration law is exactly reading
their masked values on the original finite arrays. -/
theorem integral_originalIidMaskedConfigurationPairLaw_laplace_eq_sum
    (μ : Measure ΩS) (ν : Measure ΩT) (NS NT : ℕ) (baseX : X) (baseY : Y)
    {HS : Set ΩS} {HT : Set ΩT} (hHS : MeasurableSet HS) (hHT : MeasurableSet HT)
    {obsS : ΩS → X} {obsT : ΩT → Y} (hobsS : Measurable obsS) (hobsT : Measurable obsT)
    (F : C_c(X, ℝ)) (G : C_c(Y, ℝ)) :
    (∫ c, Real.exp (-(LocalConfiguration.testIntegral c.1 F +
      LocalConfiguration.testIntegral c.2 G))
      ∂originalIidMaskedConfigurationPairLaw μ ν NS NT baseX baseY HS HT obsS obsT) =
    ∫ z : (Fin NS → ΩS) × (Fin NT → ΩT),
      Real.exp (-((∑ i : Fin NS, HS.indicator (fun x ↦ F (obsS x)) (z.1 i)) +
        (∑ j : Fin NT, HT.indicator (fun y ↦ G (obsT y)) (z.2 j))))
      ∂(Measure.pi (fun _ : Fin NS ↦ μ)).prod (Measure.pi (fun _ : Fin NT ↦ ν)) := by
  have hm : Measurable (fun c : LocalConfiguration baseX × LocalConfiguration baseY ↦
      Real.exp (-(LocalConfiguration.testIntegral c.1 F +
        LocalConfiguration.testIntegral c.2 G))) :=
    (((LocalConfiguration.measurable_testIntegral F).comp measurable_fst).add
      ((LocalConfiguration.measurable_testIntegral G).comp measurable_snd)).neg.exp
  rw [originalIidMaskedConfigurationPairLaw,
    integral_map (measurable_maskedConfigurationPair NS NT baseX baseY hHS hHT
      hobsS hobsT).aemeasurable hm.aestronglyMeasurable]
  simp only [LocalConfiguration.testIntegral_ofMaskedTuple]

/-- Exact joint Laplace functional under the actual two-color configuration law;
the one-point defects use the unnormalized restricted original laws. -/
theorem integral_originalIidMaskedConfigurationPairLaw_laplace_eq_pow_defects
    (μ : Measure ΩS) (ν : Measure ΩT) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (NS NT : ℕ) (baseX : X) (baseY : Y) {HS : Set ΩS} {HT : Set ΩT}
    (hHS : MeasurableSet HS) (hHT : MeasurableSet HT)
    {obsS : ΩS → X} {obsT : ΩT → Y} (hobsS : Measurable obsS) (hobsT : Measurable obsT)
    (F : C_c(X, ℝ)) (G : C_c(Y, ℝ)) (hF : ∀ x, 0 ≤ F x) (hG : ∀ y, 0 ≤ G y) :
    (∫ c, Real.exp (-(LocalConfiguration.testIntegral c.1 F +
      LocalConfiguration.testIntegral c.2 G))
      ∂originalIidMaskedConfigurationPairLaw μ ν NS NT baseX baseY HS HT obsS obsT) =
      (1 - ∫ x, (1 - Real.exp (-F (obsS x))) ∂μ.restrict HS) ^ NS *
        (1 - ∫ y, (1 - Real.exp (-G (obsT y))) ∂ν.restrict HT) ^ NT := by
  rw [integral_originalIidMaskedConfigurationPairLaw_laplace_eq_sum μ ν NS NT baseX baseY
    hHS hHT hobsS hobsT F G]
  exact integral_exp_neg_twoMaskedIidSums_eq_pow_defects μ ν hHS hHT
    (F.continuous.measurable.comp hobsS) (G.continuous.measurable.comp hobsT)
    (fun x ↦ hF (obsS x)) (fun y ↦ hG (obsT y)) NS NT

end Finite

/-- The joint compact-test Laplace limit of the actual independently sampled
original configuration pair follows from its two scaled restricted defects. -/
theorem tendsto_integral_originalIidMaskedConfigurationPairLaw_laplace
    {ΩS ΩT : ℕ → Type*} [∀ n, MeasurableSpace (ΩS n)] [∀ n, MeasurableSpace (ΩT n)]
    {X Y : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    (μ : (n : ℕ) → Measure (ΩS n)) (ν : (n : ℕ) → Measure (ΩT n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (NS NT : ℕ → ℕ) (baseX : X) (baseY : Y)
    (HS : (n : ℕ) → Set (ΩS n)) (HT : (n : ℕ) → Set (ΩT n))
    (obsS : (n : ℕ) → ΩS n → X) (obsT : (n : ℕ) → ΩT n → Y)
    (F : C_c(X, ℝ)) (G : C_c(Y, ℝ))
    {a b : ℝ} (hNS : Tendsto NS atTop atTop) (hNT : Tendsto NT atTop atTop)
    (hHS : ∀ n, MeasurableSet (HS n)) (hHT : ∀ n, MeasurableSet (HT n))
    (hobsS : ∀ n, Measurable (obsS n)) (hobsT : ∀ n, Measurable (obsT n))
    (hF : ∀ x, 0 ≤ F x) (hG : ∀ y, 0 ≤ G y)
    (hdefS : Tendsto (fun n ↦ (NS n : ℝ) *
      ∫ x, (1 - Real.exp (-F (obsS n x))) ∂(μ n).restrict (HS n)) atTop (𝓝 a))
    (hdefT : Tendsto (fun n ↦ (NT n : ℝ) *
      ∫ y, (1 - Real.exp (-G (obsT n y))) ∂(ν n).restrict (HT n)) atTop (𝓝 b)) :
    Tendsto (fun n ↦ ∫ c, Real.exp (-(LocalConfiguration.testIntegral c.1 F +
      LocalConfiguration.testIntegral c.2 G))
      ∂originalIidMaskedConfigurationPairLaw (μ n) (ν n) (NS n) (NT n)
        baseX baseY (HS n) (HT n) (obsS n) (obsT n)) atTop (𝓝 (Real.exp (-(a + b)))) := by
  simp_rw [integral_originalIidMaskedConfigurationPairLaw_laplace_eq_sum
    (μ _) (ν _) (NS _) (NT _) baseX baseY (hHS _) (hHT _) (hobsS _) (hobsT _) F G]
  exact tendsto_integral_exp_neg_twoMaskedIidSums μ ν NS NT HS HT
    (fun n x ↦ F (obsS n x)) (fun n y ↦ G (obsT n y)) hNS hNT hHS hHT
    (fun n ↦ F.continuous.measurable.comp (hobsS n))
    (fun n ↦ G.continuous.measurable.comp (hobsT n))
    (fun n x ↦ hF (obsS n x)) (fun n y ↦ hG (obsT n y)) hdefS hdefT

end OTSelector.Probability
