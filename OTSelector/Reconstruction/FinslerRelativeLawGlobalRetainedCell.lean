import OTSelector.Probability.RetainedCoordinateReadout
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling
import OTSelector.Probability.CellwisePopulation

/-! Select one retained cell inside the global original residual experiment. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The original endpoint labels select the same latent cell before and after
physical reconstruction, while the global retained population is unchanged. -/
theorem original_retained_pair_restrict_read_coordinates
    {X Z W : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableEq Z] (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x)
    (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (K : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel K]
    (hmarginals : ∀ᵐ z ∂lambda,
      (K z).map Prod.fst ≤ condDistrib u a μ z ∧ (K z).map Prod.snd ≤ condDistrib u a ν z)
    {L : Set Z} (hL : MeasurableSet L) (R : Z → W) (hR : Measurable R) (side : Bool) :
    (((((lambda ⊗ₘ K).map sameLabelPopulationPair).map (Prod.map b b)).restrict
      {p | a (if side then p.2 else p.1) ∈ L}).map
        (Prod.map (fun x ↦ (R (a x), u x)) (fun y ↦ (R (a y), u y)))) =
      ((lambda.restrict L ⊗ₘ K).map (Prod.map R id)).map sameLabelPopulationPair := by
  have hfull := original_retained_pair_read_coordinates μ ν lambda a u ha hu b hb
    hμinv hνinv hlabel0 hlabel1 (L := univ) K (by simpa using hmarginals) id measurable_id
  simp only [Measure.restrict_univ, Prod.map_id, Measure.map_id, id_eq] at hfull
  let F := Prod.map (fun x ↦ (a x, u x)) (fun y ↦ (a y, u y))
  have hF : Measurable F := (ha.prodMk hu).prodMap (ha.prodMk hu)
  let A : Set ((Z × ℝ) × (Z × ℝ)) := {p | (if side then p.2 else p.1).1 ∈ L}
  have hA : MeasurableSet A := by
    cases side
    · exact (measurable_fst.comp measurable_fst) hL
    · exact (measurable_fst.comp measurable_snd) hL
  have hrestrict := congrArg (fun ρ : Measure ((Z × ℝ) × (Z × ℝ)) ↦ ρ.restrict A) hfull
  rw [Measure.restrict_map hF hA, Measure.restrict_map measurable_sameLabelPopulationPair hA] at hrestrict
  have hpre : sameLabelPopulationPair ⁻¹' A = L ×ˢ univ := by
    ext p
    cases side <;> simp [A, sameLabelPopulationPair]
  rw [hpre, ← restrict_label_compProd lambda K hL] at hrestrict
  let G := Prod.map (Prod.map R (id : ℝ → ℝ)) (Prod.map R (id : ℝ → ℝ))
  have hG : Measurable G := (hR.prodMap measurable_id).prodMap (hR.prodMap measurable_id)
  have h := congrArg (fun ρ ↦ ρ.map G) hrestrict
  rw [Measure.map_map hG hF, Measure.map_map hG measurable_sameLabelPopulationPair] at h
  rw [Measure.map_map measurable_sameLabelPopulationPair (hR.prodMap measurable_id)]
  cases side <;> exact h

/-- On its original cell a finite glued retained kernel is literally that
cell's unchanged continuous clock-pair kernel. -/
theorem compProd_finiteCellPairKernel_restrict
    {C Z Y : Type*} [Fintype C] [MeasurableSpace Z] [MeasurableSpace Y]
    (lambda : Measure Z) [SFinite lambda]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : C → Kernel Z Y) [∀ c, IsSFiniteKernel (K c)] (c : C) :
    lambda.restrict (cell c) ⊗ₘ finiteCellPairKernel cell hcell K =
      lambda.restrict (cell c) ⊗ₘ K c := by
  apply Measure.compProd_congr
  filter_upwards [ae_restrict_mem (hcell c)] with z hz
  exact finiteCellPairKernel_eq cell hcell hdisj K c hz

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))]

/-- Aggregating all retained atlas marks recovers the entire original
retained marginal, before selecting any particular cell or optimizer. -/
theorem refineSubplan_retained_physical_laws
    (η : Measure (X × Y)) (hη : η ≤ π) :
    let R := D.refineSubplan η hη
    ((R.types.sourceMarkedLaw μ).restrict {p | subplanRetentionFlag p.2 = false}).map Prod.fst =
      (π - η).map Prod.fst ∧
    ((R.types.targetMarkedLaw ν).restrict {p | subplanRetentionFlag p.2 = false}).map Prod.fst =
      (π - η).map Prod.snd := by
  let R := D.refineSubplan η hη
  have htag : Injective (fun t : T ↦ some (false, t)) := by
    intro t t' h
    exact (Prod.mk.inj (Option.some.inj h)).2
  have heX : {p : X × Option (Bool × T) | subplanRetentionFlag p.2 = false} =
      {p | ∃ t : T, p.2 = some (false, t)} := by
    ext p
    cases hp : p.2 with
    | none => simp [hp, subplanRetentionFlag]
    | some bt => cases bt with | mk flag t => cases flag <;> simp [hp, subplanRetentionFlag]
  have heY : {p : Y × Option (Bool × T) | subplanRetentionFlag p.2 = false} =
      {p | ∃ t : T, p.2 = some (false, t)} := by
    ext p
    cases hp : p.2 with
    | none => simp [hp, subplanRetentionFlag]
    | some bt => cases bt with | mk flag t => cases flag <;> simp [hp, subplanRetentionFlag]
  have hfalse : ∑ t, R.types.component (false, t) = π - η :=
    D.types.rnSubplanTypes_complementary_sum_eq η hη D.sum_eq
  constructor
  · rw [heX, PopulationSubcouplingTypes.sourceMarkedLaw,
      finiteRNMarkLaw_restrict_tags_map_fst μ _ _ htag]
    change (∑ t, (R.types.component (false, t)).map Prod.fst) = _
    rw [← Measure.map_finset_sum' measurable_fst.aemeasurable, hfalse]
  · rw [heY, PopulationSubcouplingTypes.targetMarkedLaw,
      finiteRNMarkLaw_restrict_tags_map_fst ν _ _ htag]
    change (∑ t, (R.types.component (false, t)).map Prod.snd) = _
    rw [← Measure.map_finset_sum' measurable_snd.aemeasurable, hfalse]

/-- Restricting the retained flag to an actual physical cell gives its literal
original retained marginal law; the residual subplan used to create the marks
is still the same global η. -/
theorem refineSubplan_retained_cell_observation_laws
    {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (η : Measure (X × Y)) (hη : η ≤ π)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g) :
    let R := D.refineSubplan η hη
    ((R.types.sourceMarkedLaw μ).restrict
      {p | subplanRetentionFlag p.2 = false ∧ p.1 ∈ A}).map (fun p ↦ f p.1) =
        (((π - η).map Prod.fst).restrict A).map f ∧
    ((R.types.targetMarkedLaw ν).restrict
      {p | subplanRetentionFlag p.2 = false ∧ p.1 ∈ B}).map (fun p ↦ g p.1) =
        (((π - η).map Prod.snd).restrict B).map g := by
  constructor
  · rw [← (D.refineSubplan_retained_physical_laws η hη).1,
      Measure.restrict_map measurable_fst hA,
      Measure.map_map hf measurable_fst, Measure.restrict_restrict (measurable_fst hA)]
    congr 1
    congr 1
    ext p
    exact and_comm
  · rw [← (D.refineSubplan_retained_physical_laws η hη).2,
      Measure.restrict_map measurable_fst hB,
      Measure.map_map hg measurable_fst, Measure.restrict_restrict (measurable_fst hB)]
    congr 1
    congr 1
    ext p
    exact and_comm

/-- Before any matching, every prescribed original retained-cell attribution
has the raw independent component laws inside the same global residual repair
experiment. The two color counts may be different. -/
theorem refineSubplan_retained_cell_iid_observation_laws
    {I J Z W : Type*} [Fintype I] [Fintype J] [MeasurableSpace Z] [MeasurableSpace W]
    (η : Measure (X × Y)) (hη : η ≤ π)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g) :
    let R := D.refineSubplan η hη
    (((Measure.pi (fun _ : I ↦ R.types.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.types.targetMarkedLaw ν))).restrict
        ((univ.pi (fun _ ↦ {p | subplanRetentionFlag p.2 = false ∧ p.1 ∈ A})) ×ˢ
          (univ.pi (fun _ ↦ {p | subplanRetentionFlag p.2 = false ∧ p.1 ∈ B})))).map
            (Prod.map (fun x i ↦ f (x i).1) (fun y j ↦ g (y j).1)) =
      (Measure.pi (fun _ : I ↦ (((π - η).map Prod.fst).restrict A).map f)).prod
        (Measure.pi (fun _ : J ↦ (((π - η).map Prod.snd).restrict B).map g)) := by
  have hx : Measurable (fun p : X × Option (Bool × T) ↦ f p.1) := hf.comp measurable_fst
  have hy : Measurable (fun p : Y × Option (Bool × T) ↦ g p.1) := hg.comp measurable_fst
  have hxs : Measurable (fun x : I → X × Option (Bool × T) ↦ fun i ↦ f (x i).1) :=
    measurable_pi_lambda _ fun i ↦ hx.comp (measurable_pi_apply i)
  have hys : Measurable (fun y : J → Y × Option (Bool × T) ↦ fun j ↦ g (y j).1) :=
    measurable_pi_lambda _ fun j ↦ hy.comp (measurable_pi_apply j)
  dsimp only
  rw [← Measure.prod_restrict, ← Measure.map_prod_map _ _ hxs hys,
    Measure.restrict_pi_pi, Measure.restrict_pi_pi,
    Measure.pi_map_pi (fun _ ↦ hx.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ hy.aemeasurable)]
  simp_rw [(D.refineSubplan_retained_cell_observation_laws η hη hA hB f g hf hg).1,
    (D.refineSubplan_retained_cell_observation_laws η hη hA hB f g hf hg).2]

end PopulationTypedCostData

end OTSelector.Reconstruction
