import OTSelector.Reconstruction.FinslerConcreteUpperClassObservation

/-! The actual original finite class split has legal raw support before Haar normalization. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Raw fixed class weights vanish outside the original mask, including null total mass. -/
theorem clockClassPairMeasure_legal {I J : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSpace J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (P : I → J → ℝ) (allowed : I → J → Prop)
    (hzero : ∀ i j, ¬allowed i j → P i j = 0) :
    ∀ᵐ p ∂clockClassPairMeasure P, allowed p.1 p.2 := by
  unfold clockClassPairMeasure finiteClassPopulationCoupling
  simp only [ae_finsetSum_measure_iff]
  intro i _ j _
  by_cases hij : allowed i j
  · rw [Measure.dirac_prod_dirac]
    have h : ∀ᵐ p ∂Measure.dirac (i, j), allowed p.1 p.2 :=
      (ae_dirac_iff (Set.to_countable {p : I × J | allowed p.1 p.2}).measurableSet).mpr hij
    exact Measure.ae_smul_measure h (ENNReal.ofReal (P i j))
  · rw [hzero i j hij, ENNReal.ofReal_zero, zero_smul]
    simp

/-- Exact ORIGINAL class rows and columns supply nonzero bin masses internally.
Thus the normalized within-bin clocks in the actual retained population carry
only allowed pair classes, with no uniform-density or positive-mass premise. -/
theorem original_class_split_raw_classes_legal
    {Z X Y I J : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype I] [Fintype J] [MeasurableSpace I] [MeasurableSpace J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (μ : Measure Z) [SFinite μ] (κs : Kernel Z X) (κt : Kernel Z Y)
    [∀ z, IsFiniteMeasure (κs z)] [∀ z, IsFiniteMeasure (κt z)]
    (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (fallbackS : I → X) (fallbackT : J → Y)
    (classS : X → I) (classT : Y → J) (hmS : Measurable classS) (hmT : Measurable classT)
    (hclassS : ∀ i x, x ∈ S i → classS x = i)
    (hclassT : ∀ j y, y ∈ T j → classT y = j)
    (P₀ : I → J → ℝ) (hP₀ : ∀ i j, 0 ≤ P₀ i j)
    (density : Z → ℝ) (residual Pf : Z → I → J → ℝ)
    (hmPf : ∀ i j, Measurable (fun z ↦ Pf z i j))
    (hPf : ∀ᵐ z ∂μ, ∀ i j, Pf z i j = P₀ i j / density z)
    (hdensity : ∀ᵐ z ∂μ, 0 < density z)
    (hresidual : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ residual z i j)
    (hrow : ∀ᵐ z ∂μ, ∀ i, ∑ j, (P₀ i j / density z + residual z i j) = (κs z).real (S i))
    (hcol : ∀ᵐ z ∂μ, ∀ j, ∑ i, (P₀ i j / density z + residual z i j) = (κt z).real (T j))
    (allowed : I → J → Prop) (hzero : ∀ i j, ¬allowed i j → P₀ i j = 0) :
    let raw := μ ⊗ₘ finiteClassPopulationKernel Pf
      (fun i ↦ normalizedActualBinKernel κs (S i) (hS i) (fallbackS i))
      (fun j ↦ normalizedActualBinKernel κt (T j) (hT j) (fallbackT j))
    ∀ᵐ p ∂raw, allowed (classS p.2.1) (classT p.2.2) := by
  have hpositive := fixed_reference_bin_masses_ne_zero_of_original_split μ κs κt S T
    P₀ hP₀ density residual hdensity hresidual hrow hcol
  apply Measure.ae_compProd_of_ae_ae
  · exact (Set.to_countable {p : I × J | allowed p.1 p.2}).measurableSet.preimage
      ((hmS.comp (measurable_fst.comp measurable_snd)).prodMk
        (hmT.comp (measurable_snd.comp measurable_snd)))
  · filter_upwards [hpositive, hPf] with z hz hPfz
    rw [finiteClassPopulationKernel_apply Pf hmPf]
    have hpositivePf : ∀ i j, Pf z i j ≠ 0 → κs z (S i) ≠ 0 ∧ κt z (T j) ≠ 0 := by
      intro i j hp
      apply hz i j
      intro hp₀
      apply hp
      rw [hPfz, hp₀, zero_div]
    have hlegal : ∀ᵐ p ∂clockClassPairMeasure (Pf z), allowed p.1 p.2 :=
      clockClassPairMeasure_legal (Pf z) allowed fun i j hij ↦ by
        rw [hPfz, hzero i j hij, zero_div]
    rw [← finiteClassPopulationCoupling_map_actual_classes κs κt S T hS hT
      fallbackS fallbackT classS classT hmS hmT hclassS hclassT (Pf z) z hpositivePf] at hlegal
    exact ae_of_ae_map (hmS.prodMap hmT).aemeasurable hlegal

end OTSelector.Reconstruction
