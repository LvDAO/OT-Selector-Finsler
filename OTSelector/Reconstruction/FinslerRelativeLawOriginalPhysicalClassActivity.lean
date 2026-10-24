import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalActiveClasses

/-! All fixed original cells inherit active class support from their literal conditional splits. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The same original retained physical population supplies active source and target
classes in every fixed reference cell. The finite class sets may depend on the reference;
zero classes, empty retained cells and arbitrary zero-bin fallbacks are included. -/
theorem original_physical_retained_class_activity
    {X Z C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z]
    [Fintype C] {I J : C → Type*}
    [∀ c, Fintype (I c)] [∀ c, Fintype (J c)]
    [∀ c, MeasurableSpace (I c)] [∀ c, MeasurableSpace (J c)]
    [∀ c, MeasurableSingletonClass (I c)] [∀ c, MeasurableSingletonClass (J c)]
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
    (S : ∀ c, I c → Set ℝ) (T : ∀ c, J c → Set ℝ)
    (hS : ∀ c i, MeasurableSet (S c i)) (hT : ∀ c j, MeasurableSet (T c j))
    (fallbackS : ∀ c, I c → ℝ) (fallbackT : ∀ c, J c → ℝ)
    (classS : ∀ c, ℝ → I c) (classT : ∀ c, ℝ → J c)
    (hmS : ∀ c, Measurable (classS c)) (hmT : ∀ c, Measurable (classT c))
    (hclassS : ∀ c i x, x ∈ S c i → classS c x = i)
    (hclassT : ∀ c j y, y ∈ T c j → classT c y = j)
    (P₀ : ∀ c, I c → J c → ℝ) (hP₀ : ∀ c i j, 0 ≤ P₀ c i j)
    (density : C → Z → ℝ) (residual Pf : ∀ c, Z → I c → J c → ℝ)
    (hmPf : ∀ c i j, Measurable (fun z ↦ Pf c z i j))
    (hPf : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ i j, Pf c z i j = P₀ c i j / density c z)
    (hdensity : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), 0 < density c z)
    (hresidual : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ i j, 0 ≤ residual c z i j)
    (hrow : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ i,
      ∑ j, (P₀ c i j / density c z + residual c z i j) = (condDistrib u a μ z).real (S c i))
    (hcol : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j,
      ∑ i, (P₀ c i j / density c z + residual c z i j) = (condDistrib u a ν z).real (T c j))
    (hK : ∀ c, K c = finiteClassPopulationKernel (Pf c)
      (fun i ↦ normalizedActualBinKernel (condDistrib u a μ) (S c i) (hS c i) (fallbackS c i))
      (fun j ↦ normalizedActualBinKernel (condDistrib u a ν) (T c j) (hT c j) (fallbackT c j)))
    (allowed : ∀ c, I c → J c → Prop) (hzero : ∀ c i j, ¬allowed c i j → P₀ c i j = 0) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map
      (Prod.map b b))
    (∀ᵐ x ∂χ.map Prod.fst, ∀ c, a x ∈ cell c → ∃ j, allowed c (classS c (u x)) j) ∧
      (∀ᵐ y ∂χ.map Prod.snd, ∀ c, a y ∈ cell c → ∃ i, allowed c i (classT c (u y))) := by
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map
    (Prod.map b b))
  have hactive c := pair_class_support_original_marginals_active χ a u ha hu (hcell c)
    (classS c) (classT c) (hmS c) (hmT c) (allowed c)
    (fun side ↦ original_physical_retained_cell_classes_legal μ ν lambda a u ha hu b hb
      hμinv hνinv hlabel0 hlabel1 cell hcell hdisj K Qglobal hwhole c
      (S c) (T c) (hS c) (hT c) (fallbackS c) (fallbackT c)
      (classS c) (classT c) (hmS c) (hmT c) (hclassS c) (hclassT c)
      (P₀ c) (hP₀ c) (density c) (residual c) (Pf c) (hmPf c) (hPf c)
      (hdensity c) (hresidual c) (hrow c) (hcol c) (hK c) (allowed c) (hzero c) side)
  exact ⟨ae_all_iff.mpr fun c ↦ ae_imp_of_ae_restrict (hactive c).1,
    ae_all_iff.mpr fun c ↦ ae_imp_of_ae_restrict (hactive c).2⟩

end OTSelector.Reconstruction
