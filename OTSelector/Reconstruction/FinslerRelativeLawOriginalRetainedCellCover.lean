import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell

/-! The literal original glued retained law is supported in its fixed physical cell cover. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The fixed original inverse and actual glued conditional split discharge the
physical cell-cover condition used by the uniform compact approximation. -/
theorem original_physical_retained_cell_cover
    {X Z C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z]
    [Fintype C] (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Kernel Z (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (Qglobal : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z)) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c := by
  let Kg := finiteCellPairKernel cell hcell K
  let G := ⋃ c, cell c
  have hG : MeasurableSet G := MeasurableSet.iUnion hcell
  have hraw : ∀ᵐ p ∂lambda ⊗ₘ Kg, p.1 ∈ G := by
    apply Measure.ae_compProd_of_ae_ae (measurable_fst hG)
    exact Filter.Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ G
      · exact Filter.Eventually.of_forall fun _ ↦ hz
      · have hzero : Kg z = 0 := finiteCellPairKernel_eq_zero cell hcell K hz
        rw [hzero]
        simp
  have hlatent : ∀ᵐ p ∂(lambda ⊗ₘ Kg).map sameLabelPopulationPair, p.1.1 ∈ G := by
    apply (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable
      ((measurable_fst.comp measurable_fst) hG)).mpr
    exact hraw
  have hdom : ∀ᵐ z ∂lambda,
      (Kg z).map Prod.fst ≤ condDistrib u a μ z ∧
        (Kg z).map Prod.snd ≤ condDistrib u a ν z :=
    hwhole.mono fun _ h ↦ clockPair_marginals_le_of_original_split _ _ _ _ h
  have hread := original_retained_pair_read_coordinates μ ν lambda a u ha hu b hb
    hμinv hνinv hlabel0 hlabel1 (L := univ) Kg (by simpa using hdom) id measurable_id
  simp only [Measure.restrict_univ, Prod.map_id, Measure.map_id, id_eq] at hread
  rw [← hread] at hlatent
  exact ae_of_ae_map ((ha.prodMk hu).prodMap (ha.prodMk hu)).aemeasurable hlatent

end OTSelector.Reconstruction
