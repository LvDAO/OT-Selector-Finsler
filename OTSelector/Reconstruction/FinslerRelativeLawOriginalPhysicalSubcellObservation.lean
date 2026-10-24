import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalCellObservation

/-! Original retained physical cell observations recover the literal original
label/clock-kernel observation under the same fixed original inverse. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- On every measurable subcell of a retained macrocell the glued original
kernel is still literally that macrocell's original clock-pair kernel. -/
theorem compProd_finiteCellPairKernel_restrict_subcell
    {C Z Y : Type*} [Fintype C] [MeasurableSpace Z] [MeasurableSpace Y]
    (lambda : Measure Z) [SFinite lambda]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : C → Kernel Z Y) [∀ c, IsSFiniteKernel (K c)] (c : C)
    {L : Set Z} (hL : MeasurableSet L) (hsub : L ⊆ cell c) :
    lambda.restrict L ⊗ₘ finiteCellPairKernel cell hcell K = lambda.restrict L ⊗ₘ K c := by
  apply Measure.compProd_congr
  filter_upwards [ae_restrict_mem hL] with z hz
  exact finiteCellPairKernel_eq cell hcell hdisj K c (hsub hz)

/-- Reading the original fixed inverse preserves the literal shared label of
the whole retained population, before any prescribed spatial truncation. -/
theorem original_global_retained_shared_labels
    {X Z C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z] [Fintype C]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Kernel Z (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (Qglobal : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a μ z) (condDistrib u a ν z)) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    ∀ᵐ p ∂χ, a p.1 = a p.2 := by
  let Kg := finiteCellPairKernel cell hcell K
  have hdom : ∀ᵐ z ∂lambda, (Kg z).map Prod.fst ≤ condDistrib u a μ z ∧
      (Kg z).map Prod.snd ≤ condDistrib u a ν z :=
    hwhole.mono fun z hz ↦ clockPair_marginals_le_of_original_split _ _ _ _ hz
  have hread := original_retained_pair_read_coordinates μ ν lambda a u ha hu b hb
    hμinv hνinv hlabel0 hlabel1 (L := univ) Kg (by simpa using hdom) id measurable_id
  simp only [Measure.restrict_univ, Prod.map_id, Measure.map_id, id_eq] at hread
  have hlatent : ∀ᵐ p ∂(lambda ⊗ₘ Kg).map sameLabelPopulationPair, p.1.1 = p.2.1 := by
    apply (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable
      (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
        (measurable_fst.comp measurable_snd))).mpr
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  rw [← hread] at hlatent
  exact ae_of_ae_map ((ha.prodMk hu).prodMap (ha.prodMk hu)).aemeasurable hlatent

/-- Reading one actual physical retained marginal in any prescribed subcell
recovers the corresponding original clock-kernel observation. The clock read
can be the exact finite class map produced by the original bin construction. -/
theorem original_global_retained_subcell_observation
    {X Z W A C : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace W] [MeasurableSpace A] [MeasurableEq Z] [Fintype C]
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
    (R : Z → W) (hR : Measurable R) (classify : ℝ → A) (hc : Measurable classify)
    (c : C) {L : Set Z} (hL : MeasurableSet L) (hsub : L ⊆ cell c) (side : Bool) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map
      (Prod.map b b))
    (((χ.map (fun p ↦ if side then p.2 else p.1)).restrict (a ⁻¹' L)).map
      (fun x ↦ (R (a x), classify (u x)))) =
      (lambda.restrict L ⊗ₘ K c).map
        (fun p ↦ (R p.1, classify (if side then p.2.2 else p.2.1))) := by
  let Kg := finiteCellPairKernel cell hcell K
  let χ := (((lambda ⊗ₘ Kg).map sameLabelPopulationPair).map (Prod.map b b))
  let project := fun p : X × X ↦ if side then p.2 else p.1
  let read := fun x ↦ (R (a x), u x)
  let observe := fun p : (W × ℝ) × (W × ℝ) ↦
    ((if side then p.2 else p.1).1, classify (if side then p.2 else p.1).2)
  have hproject : Measurable project := by cases side <;> dsimp [project] <;> fun_prop
  have hread : Measurable read := (hR.comp ha).prodMk hu
  have hreadClass : Measurable (fun x ↦ (R (a x), classify (u x))) :=
    (hR.comp ha).prodMk (hc.comp hu)
  have hobserve : Measurable observe := by cases side <;> dsimp [observe] <;> fun_prop
  have hdom : ∀ᵐ z ∂lambda, (Kg z).map Prod.fst ≤ condDistrib u a μ z ∧
      (Kg z).map Prod.snd ≤ condDistrib u a ν z :=
    hwhole.mono fun z hz ↦ clockPair_marginals_le_of_original_split _ _ _ _ hz
  have hpair := original_retained_pair_restrict_read_coordinates μ ν lambda a u ha hu b hb
    hμinv hνinv hlabel0 hlabel1 Kg hdom hL R hR side
  have hlocal := compProd_finiteCellPairKernel_restrict_subcell lambda cell hcell hdisj K c hL hsub
  calc
    _ = ((χ.restrict {p | a (project p) ∈ L}).map (Prod.map read read)).map observe := by
      rw [Measure.restrict_map hproject (ha hL),
        Measure.map_map hreadClass hproject, Measure.map_map hobserve (hread.prodMap hread)]
      cases side <;> rfl
    _ = (((lambda.restrict L ⊗ₘ Kg).map (Prod.map R id)).map
        sameLabelPopulationPair).map observe := congrArg (Measure.map observe) hpair
    _ = _ := by
      rw [Measure.map_map hobserve measurable_sameLabelPopulationPair,
        Measure.map_map (hobserve.comp measurable_sameLabelPopulationPair) (hR.prodMap measurable_id), hlocal]
      cases side <;> rfl

end OTSelector.Reconstruction
