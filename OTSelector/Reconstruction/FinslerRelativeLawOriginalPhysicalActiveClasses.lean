import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.FinslerRelativeLawOriginalActiveClassLaw
import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell

/-! Actual original physical retained cells inherit their frozen class-mask support. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Original physical pair-class support gives both active-class marginal laws
on that same literal cell, without asserting independence of any selected vertices. -/
theorem pair_class_support_original_marginals_active
    {X Z I J : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype I] [Fintype J] [MeasurableSpace I] [MeasurableSpace J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (χ : Measure (X × X)) (a : X → Z) (u : X → ℝ)
    (ha : Measurable a) (hu : Measurable u) {L : Set Z} (hL : MeasurableSet L)
    (classS : ℝ → I) (classT : ℝ → J) (hmS : Measurable classS) (hmT : Measurable classT)
    (allowed : I → J → Prop)
    (hlegal : ∀ side : Bool,
      ∀ᵐ p ∂χ.restrict {p | a (if side then p.2 else p.1) ∈ L},
        allowed (classS (u p.1)) (classT (u p.2))) :
    (∀ᵐ x ∂(χ.map Prod.fst).restrict (a ⁻¹' L), ∃ j, allowed (classS (u x)) j) ∧
      (∀ᵐ y ∂(χ.map Prod.snd).restrict (a ⁻¹' L), ∃ i, allowed i (classT (u y))) := by
  constructor
  · rw [Measure.restrict_map measurable_fst (ha hL)]
    apply (ae_map_iff measurable_fst.aemeasurable ?_).mpr
    · exact (hlegal false).mono fun p hp ↦ ⟨classT (u p.2), hp⟩
    · exact (Set.to_countable {i : I | ∃ j, allowed i j}).measurableSet.preimage (hmS.comp hu)
  · rw [Measure.restrict_map measurable_snd (ha hL)]
    apply (ae_map_iff measurable_snd.aemeasurable ?_).mpr
    · exact (hlegal true).mono fun p hp ↦ ⟨classS (u p.1), hp⟩
    · exact (Set.to_countable {j : J | ∃ i, allowed i j}).measurableSet.preimage (hmT.comp hu)

/-- The actual original physical retained population has allowed observed clock
classes on each fixed original cell. Exact conditional class restoration and
the SAME original inverse discharge both positive-bin and physical-readout premises. -/
theorem original_physical_retained_cell_classes_legal
    {X Z C I J : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z]
    [Fintype C] [Fintype I] [Fintype J] [MeasurableSpace I] [MeasurableSpace J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : C → Kernel Z (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (Qglobal : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a μ z) (condDistrib u a ν z))
    (c : C) (S : I → Set ℝ) (T : J → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (fallbackS : I → ℝ) (fallbackT : J → ℝ)
    (classS : ℝ → I) (classT : ℝ → J) (hmS : Measurable classS) (hmT : Measurable classT)
    (hclassS : ∀ i x, x ∈ S i → classS x = i)
    (hclassT : ∀ j y, y ∈ T j → classT y = j)
    (P₀ : I → J → ℝ) (hP₀ : ∀ i j, 0 ≤ P₀ i j)
    (density : Z → ℝ) (residual Pf : Z → I → J → ℝ)
    (hmPf : ∀ i j, Measurable (fun z ↦ Pf z i j))
    (hPf : ∀ᵐ z ∂lambda.restrict (cell c), ∀ i j, Pf z i j = P₀ i j / density z)
    (hdensity : ∀ᵐ z ∂lambda.restrict (cell c), 0 < density z)
    (hresidual : ∀ᵐ z ∂lambda.restrict (cell c), ∀ i j, 0 ≤ residual z i j)
    (hrow : ∀ᵐ z ∂lambda.restrict (cell c), ∀ i,
      ∑ j, (P₀ i j / density z + residual z i j) = (condDistrib u a μ z).real (S i))
    (hcol : ∀ᵐ z ∂lambda.restrict (cell c), ∀ j,
      ∑ i, (P₀ i j / density z + residual z i j) = (condDistrib u a ν z).real (T j))
    (hKc : K c = finiteClassPopulationKernel Pf
      (fun i ↦ normalizedActualBinKernel (condDistrib u a μ) (S i) (hS i) (fallbackS i))
      (fun j ↦ normalizedActualBinKernel (condDistrib u a ν) (T j) (hT j) (fallbackT j)))
    (allowed : I → J → Prop) (hzero : ∀ i j, ¬allowed i j → P₀ i j = 0)
    (side : Bool) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map
      (Prod.map b b))
    ∀ᵐ p ∂χ.restrict {p | a (if side then p.2 else p.1) ∈ cell c},
      allowed (classS (u p.1)) (classT (u p.2)) := by
  let Kg := finiteCellPairKernel cell hcell K
  let α := fun i ↦ normalizedActualBinKernel (condDistrib u a μ) (S i) (hS i) (fallbackS i)
  let β := fun j ↦ normalizedActualBinKernel (condDistrib u a ν) (T j) (hT j) (fallbackT j)
  let raw := lambda.restrict (cell c) ⊗ₘ finiteClassPopulationKernel Pf α β
  have hraw : ∀ᵐ p ∂raw, allowed (classS p.2.1) (classT p.2.2) :=
    original_class_split_raw_classes_legal (lambda.restrict (cell c))
      (condDistrib u a μ) (condDistrib u a ν) S T hS hT fallbackS fallbackT
      classS classT hmS hmT hclassS hclassT P₀ hP₀ density residual Pf hmPf hPf
      hdensity hresidual hrow hcol allowed hzero
  have hpred : MeasurableSet {p : (Z × ℝ) × (Z × ℝ) |
      allowed (classS p.1.2) (classT p.2.2)} :=
    (Set.to_countable {p : I × J | allowed p.1 p.2}).measurableSet.preimage
      ((hmS.comp (measurable_snd.comp measurable_fst)).prodMk
        (hmT.comp (measurable_snd.comp measurable_snd)))
  have hpairs : ∀ᵐ p ∂raw.map sameLabelPopulationPair,
      allowed (classS p.1.2) (classT p.2.2) :=
    (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable hpred).mpr hraw
  have hdom : ∀ᵐ z ∂lambda,
      (Kg z).map Prod.fst ≤ condDistrib u a μ z ∧
        (Kg z).map Prod.snd ≤ condDistrib u a ν z :=
    hwhole.mono fun _ h ↦ clockPair_marginals_le_of_original_split _ _ _ _ h
  have hread := original_retained_pair_restrict_read_coordinates μ ν lambda a u ha hu b hb
    hμinv hνinv hlabel0 hlabel1 Kg hdom (hcell c) id measurable_id side
  have hlocal := compProd_finiteCellPairKernel_restrict lambda cell hcell hdisj K c
  rw [hKc] at hlocal
  simp only [Prod.map_id, Measure.map_id] at hread
  rw [hlocal] at hread
  rw [← hread] at hpairs
  exact ae_of_ae_map ((ha.prodMk hu).prodMap (ha.prodMk hu)).aemeasurable hpairs

end OTSelector.Reconstruction
