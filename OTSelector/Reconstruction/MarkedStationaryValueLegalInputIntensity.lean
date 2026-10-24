import OTSelector.Reconstruction.MarkedStationaryValueLegalInputPoissonMoment
import OTSelector.Reconstruction.MarkedStationaryValuePalmMarginals
import OTSelector.MeasureTheory.CompactTestDetermination

/-!
# Exact original input intensity of the same actual joint weak law

The colored input is disintegrated only by its immutable finite color. Its
original compact-test mean determines the whole locally finite physical mean
measure. No input intensity, local moment or first-moment equality is assumed.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputIntensityInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputIntensityPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual same-scene input measure of one unchanged finite color. -/
def legalMarkedInputColorKernel (q : ℕ) (c : Fin 2) :
    Kernel (LegalMarkedOptimalInputScene q) (LegalMarkedPhysicalPoint q) :=
  ((localFiniteMeasureKernel.comap Prod.snd measurable_snd).restrict
    (measurable_snd (measurableSet_singleton c))).map Prod.fst

theorem legalMarkedInputColorKernel_apply (q : ℕ) (c : Fin 2) (s : LegalMarkedOptimalInputScene q) :
    legalMarkedInputColorKernel q c s = legalInputColorMeasure q s.2 c := by
  rw [legalMarkedInputColorKernel, Kernel.map_apply _ measurable_fst]
  rfl

/-- The physical first moment of the original color on its actual joint law. -/
def legalMarkedInputColorIntensity (q : ℕ) (P : Measure (LegalMarkedOptimalInputScene q))
    (c : Fin 2) : Measure (LegalMarkedPhysicalPoint q) := P.bind (legalMarkedInputColorKernel q c)

theorem lintegral_legalMarkedInputColorIntensity_compactTest (q : ℕ)
    (P : Measure (LegalMarkedOptimalInputScene q)) (c : Fin 2)
    (f : C_c(LegalMarkedPhysicalPoint q, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂legalMarkedInputColorIntensity q P c) =
      ∫⁻ s, ENNReal.ofReal (LocalFiniteMeasure.testIntegral s.2
        (cavityProductTest f (legalInputColorTest c))) ∂P := by
  rw [legalMarkedInputColorIntensity]
  have hfm : Measurable (fun x ↦ ENNReal.ofReal (f x)) := f.continuous.measurable.ennreal_ofReal
  rw [Measure.lintegral_bind (μ := legalMarkedInputColorKernel q c) (m := P)
    (f := fun x ↦ ENNReal.ofReal (f x)) (Kernel.measurable _).aemeasurable hfm.aemeasurable]
  apply lintegral_congr
  intro s
  rw [legalMarkedInputColorKernel_apply,
    ← ofReal_integral_eq_lintegral_ofReal f.integrable (.of_forall hf), integral_legalInputColorMeasure]

private theorem measure_eq_of_nonnegative_compact_lintegrals
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (μ ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (h : ∀ (f : C_c(X, ℝ)), (∀ x, 0 ≤ f x) →
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂ν) : μ = ν := by
  exact OTSelector.Probability.measure_eq_of_nonnegative_compact_lintegrals μ ν h

/-- The exact original Poisson compact Laplace law produces the complete
physical source and target input intensities on the same actual weak scene. -/
theorem legalMarkedInputColorIntensities_eq_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    legalMarkedInputColorIntensity q (Q : Measure (LegalMarkedOptimalInputScene q)) 0 =
        (volume : Measure (Fin q → ℝ)).prod α ∧
      legalMarkedInputColorIntensity q (Q : Measure (LegalMarkedOptimalInputScene q)) 1 =
        (volume : Measure (Fin q → ℝ)).prod β := by
  constructor
  · apply measure_eq_of_nonnegative_compact_lintegrals
    intro f hf
    let F := cavityProductTest f (legalInputColorTest 0)
    have hF : ∀ x, 0 ≤ F x := by
      intro x
      change 0 ≤ f x.1 * (if x.2 = 0 then 1 else 0)
      split <;> simp_all
    rw [lintegral_legalMarkedInputColorIntensity_compactTest q _ 0 f hf]
    have he := lintegral_legalMarkedInput_testIntegral_eq_of_tendsto q α β kin hk g hg t L hL hlarge hweak F hF
    have h0 (x : LegalMarkedPhysicalPoint q) : F (x, 0) = f x := by
      change f x * (if (0 : Fin 2) = 0 then 1 else 0) = f x
      simp
    have h1 (x : LegalMarkedPhysicalPoint q) : F (x, 1) = 0 := by
      change f x * (if (1 : Fin 2) = 0 then 1 else 0) = 0
      norm_num
    simp_rw [h0, h1] at he
    simpa only [ENNReal.ofReal_zero, lintegral_zero, add_zero] using he
  · apply measure_eq_of_nonnegative_compact_lintegrals
    intro f hf
    let F := cavityProductTest f (legalInputColorTest 1)
    have hF : ∀ x, 0 ≤ F x := by
      intro x
      change 0 ≤ f x.1 * (if x.2 = 1 then 1 else 0)
      split <;> simp_all
    rw [lintegral_legalMarkedInputColorIntensity_compactTest q _ 1 f hf]
    have he := lintegral_legalMarkedInput_testIntegral_eq_of_tendsto q α β kin hk g hg t L hL hlarge hweak F hF
    have h0 (x : LegalMarkedPhysicalPoint q) : F (x, 0) = 0 := by
      change f x * (if (0 : Fin 2) = 1 then 1 else 0) = 0
      norm_num
    have h1 (x : LegalMarkedPhysicalPoint q) : F (x, 1) = f x := by
      change f x * (if (1 : Fin 2) = 1 then 1 else 0) = f x
      simp
    simp_rw [h0, h1] at he
    simpa only [ENNReal.ofReal_zero, lintegral_zero, zero_add] using he

end OTSelector.Reconstruction
