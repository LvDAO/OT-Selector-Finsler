import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell

/-! Original retained physical cell observations recover the literal original
label/clock-kernel observation under the same fixed original inverse. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Reading one actual physical retained marginal in one actual finite cell
recovers the corresponding original clock-kernel observation. The clock read
can be the exact finite class map produced by the original bin construction. -/
theorem original_global_retained_cell_observation
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
    (c : C) (side : Bool) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map
      (Prod.map b b))
    (((χ.map (fun p ↦ if side then p.2 else p.1)).restrict (a ⁻¹' cell c)).map
      (fun x ↦ (R (a x), classify (u x)))) =
      (lambda.restrict (cell c) ⊗ₘ K c).map
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
    hμinv hνinv hlabel0 hlabel1 Kg hdom (hcell c) R hR side
  have hlocal := compProd_finiteCellPairKernel_restrict lambda cell hcell hdisj K c
  calc
    _ = ((χ.restrict {p | a (project p) ∈ cell c}).map (Prod.map read read)).map observe := by
      rw [Measure.restrict_map hproject (ha (hcell c)),
        Measure.map_map hreadClass hproject, Measure.map_map hobserve (hread.prodMap hread)]
      cases side <;> rfl
    _ = (((lambda.restrict (cell c) ⊗ₘ Kg).map (Prod.map R id)).map
        sameLabelPopulationPair).map observe := congrArg (Measure.map observe) hpair
    _ = _ := by
      rw [Measure.map_map hobserve measurable_sameLabelPopulationPair,
        Measure.map_map (hobserve.comp measurable_sameLabelPopulationPair) (hR.prodMap measurable_id), hlocal]
      cases side <;> rfl

end OTSelector.Reconstruction
