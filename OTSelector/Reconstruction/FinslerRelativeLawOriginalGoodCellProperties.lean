import OTSelector.Reconstruction.FinslerRelativeLawOriginalGoodCoordinateFacts
import OTSelector.Reconstruction.FinslerRelativeLawOriginalSelectedCoordinateMass
import OTSelector.Reconstruction.FinslerRelativeLawRetainedCellLabels

/-! Good vertices retain their original cell and compact coordinate carrier on one fine sample. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Only good retained marks read an original cell; all other fine marks read none. -/
def cellRefinedGoodCell {X Z C T : Type*} (label : X → Z) (cell : C → Set Z)
    (p : X × Option (CellRefinedType C T)) : Option C :=
  if (p.2.bind cellRefinedGoodType).isSome then finiteOriginalCellLabel cell (label p.1) else none

theorem cellRefinedGoodCell_eq_some_of_good {X Z C T : Type*}
    (label : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (p : X × Option (CellRefinedType C T)) {t : T} {c : C}
    (ht : p.2.bind cellRefinedGoodType = some t) (hc : label p.1 ∈ cell c) :
    cellRefinedGoodCell label cell p = some c := by
  simp only [cellRefinedGoodCell, ht, Option.isSome_some, ↓reduceIte]
  exact (finiteOriginalCellLabel_eq_some_iff cell hdisj _ _).mpr hc

theorem cellRefinedGoodCell_some_implies_good {X Z C T : Type*}
    (label : X → Z) (cell : C → Set Z) (p : X × Option (CellRefinedType C T)) {c : C}
    (hc : cellRefinedGoodCell label cell p = some c) :
    ∃ t, p.2.bind cellRefinedGoodType = some t := by
  cases h : p.2.bind cellRefinedGoodType with
  | none => simp [cellRefinedGoodCell, h] at hc
  | some t => exact ⟨t, rfl⟩

namespace PopulationTypedCostData
variable {X Y Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Joint original good component carriers give actual cell/coordinate carriers for
all good observed vertices at once, before any sample-dependent core is selected. -/
theorem rnCellRefinedTypes_good_cell_properties
    (hπ : Vlasov.IsCoupling π μ ν) (left : X → Z) (right : Y → Z)
    (hleft : Measurable left) (hright : Measurable right)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : T → C → Set (DyadicUnitCube q)) (hK : ∀ t c, MeasurableSet (K t c))
    (hcarriers : ∀ t, ∀ᵐ p ∂good t, ∃ c,
      left p.1 ∈ cell c ∧ right p.2 ∈ cell c ∧
        D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c)
    (n : ℕ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∀ᵐ sample ∂P,
      (∀ i t, (sample.1 i).2.bind cellRefinedGoodType = some t → ∃ c,
        cellRefinedGoodCell left cell (sample.1 i) = some c ∧
          D.sourceCoordinate t (sample.1 i).1 ∈ K t c) ∧
      (∀ j t, (sample.2 j).2.bind cellRefinedGoodType = some t → ∃ c,
        cellRefinedGoodCell right cell (sample.2 j) = some c ∧
          D.targetCoordinate t (sample.2 j).1 ∈ K t c) := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let G := D.types.rnCellGoodTypes η hη good bad hsplit
  have hs (t : T) : ∀ᵐ x ∂G.source t,
      ∃ c, left x ∈ cell c ∧ D.sourceCoordinate t x ∈ K t c := by
    rw [PopulationSubcouplingTypes.source, PopulationSubcouplingTypes.rnCellGoodTypes_component]
    have hm : MeasurableSet {x | ∃ c, left x ∈ cell c ∧ D.sourceCoordinate t x ∈ K t c} := by
      have he : {x | ∃ c, left x ∈ cell c ∧ D.sourceCoordinate t x ∈ K t c} =
          ⋃ c, left ⁻¹' cell c ∩ D.sourceCoordinate t ⁻¹' K t c := by ext x; simp
      rw [he]
      exact MeasurableSet.iUnion fun c ↦ (hleft (hcell c)).inter
        ((D.measurable_sourceCoordinate t) (hK t c))
    exact (ae_map_iff measurable_fst.aemeasurable hm).mpr
      ((hcarriers t).mono fun p ⟨c, hc, _, hs, _⟩ ↦ ⟨c, hc, hs⟩)
  have ht (t : T) : ∀ᵐ y ∂G.target t,
      ∃ c, right y ∈ cell c ∧ D.targetCoordinate t y ∈ K t c := by
    rw [PopulationSubcouplingTypes.target, PopulationSubcouplingTypes.rnCellGoodTypes_component]
    have hm : MeasurableSet {y | ∃ c, right y ∈ cell c ∧ D.targetCoordinate t y ∈ K t c} := by
      have he : {y | ∃ c, right y ∈ cell c ∧ D.targetCoordinate t y ∈ K t c} =
          ⋃ c, right ⁻¹' cell c ∩ D.targetCoordinate t ⁻¹' K t c := by ext y; simp
      rw [he]
      exact MeasurableSet.iUnion fun c ↦ (hright (hcell c)).inter
        ((D.measurable_targetCoordinate t) (hK t c))
    exact (ae_map_iff measurable_snd.aemeasurable hm).mpr
      ((hcarriers t).mono fun p ⟨c, _, hc, _, ht⟩ ↦ ⟨c, hc, ht⟩)
  have hg := G.iid_marked_type_properties (μ := μ) (ν := ν) (I := Fin n) (J := Fin n)
    (fun t x ↦ ∃ c, left x ∈ cell c ∧ D.sourceCoordinate t x ∈ K t c)
    (fun t y ↦ ∃ c, right y ∈ cell c ∧ D.targetCoordinate t y ∈ K t c) hs ht
  have hx : Measurable (fun sample : Fin n → X × Option (CellRefinedType C T) ↦
      fun i ↦ ((sample i).1, (sample i).2.bind cellRefinedGoodType)) :=
    measurable_pi_lambda _ (fun i ↦ ((measurable_pi_apply i).fst).prodMk
      ((measurable_of_countable
        (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedGoodType)).comp
          (measurable_pi_apply i).snd))
  have hy : Measurable (fun sample : Fin n → Y × Option (CellRefinedType C T) ↦
      fun j ↦ ((sample j).1, (sample j).2.bind cellRefinedGoodType)) :=
    measurable_pi_lambda _ (fun j ↦ ((measurable_pi_apply j).fst).prodMk
      ((measurable_of_countable
        (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedGoodType)).comp
          (measurable_pi_apply j).snd))
  have hlaw := D.types.rnCellRefinedTypes_iid_good_law (I := Fin n) (J := Fin n)
    η hη good bad hsplit hπ
  rw [← hlaw] at hg
  have hgf := ae_of_ae_map (hx.prodMap hy).aemeasurable hg
  filter_upwards [hgf] with sample hsample
  constructor
  · intro i t hi
    obtain ⟨c, hc, hKc⟩ := hsample.1 i t hi
    exact ⟨c, cellRefinedGoodCell_eq_some_of_good left cell hdisj _ hi hc, hKc⟩
  · intro j t hj
    obtain ⟨c, hc, hKc⟩ := hsample.2 j t hj
    exact ⟨c, cellRefinedGoodCell_eq_some_of_good right cell hdisj _ hj hc, hKc⟩


/-- Actual compact separation discharges the hierarchy's cell hypotheses on the same fine sample. -/
theorem rnCellRefinedTypes_good_cell_colors
    (hπ : Vlasov.IsCoupling π μ ν) (left : X → Z) (right : Y → Z)
    (hleft : Measurable left) (hright : Measurable right)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : T → C → Set (DyadicUnitCube q)) (hK : ∀ t c, MeasurableSet (K t c))
    (hcarriers : ∀ t, ∀ᵐ p ∂good t, ∃ c,
      left p.1 ∈ cell c ∧ right p.2 ∈ cell c ∧
        D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c)
    (k : ℕ) (hsep : ∀ t c c', ∀ x ∈ K t c, ∀ y ∈ K t c',
      dyadicCubeCell k x = dyadicCubeCell k y → c = c') (n : ℕ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let xs := fun i sample ↦ populationFineGoodCoordinate D.sourceCoordinate
      (cubeOrigin (q := q)) (sample.1 i)
    let ys := fun j sample ↦ populationFineGoodCoordinate D.targetCoordinate
      (cubeOrigin (q := q)) (sample.2 j)
    ∀ᵐ sample ∂P,
      (∀ i, (xs i sample).1 ∈ presentTypeTags T →
        ∃ c, cellRefinedGoodCell left cell (sample.1 i) = some c) ∧
      (∀ j, (ys j sample).1 ∈ presentTypeTags T →
        ∃ c, cellRefinedGoodCell right cell (sample.2 j) = some c) ∧
      ∀ i j c c', cellRefinedGoodCell left cell (sample.1 i) = some c →
        cellRefinedGoodCell right cell (sample.2 j) = some c' →
        (xs i sample).1 = (ys j sample).1 →
        dyadicCubeCell k (xs i sample).2 = dyadicCubeCell k (ys j sample).2 → c = c' := by
  have h := D.rnCellRefinedTypes_good_cell_properties η hη good bad hsplit
    hπ left right hleft hright cell hcell hdisj K hK hcarriers n
  dsimp only
  filter_upwards [h] with sample hsample
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨t, _, he⟩ := Finset.mem_image.mp hi
    obtain ⟨c, hc, _⟩ := hsample.1 i t he.symm
    exact ⟨c, hc⟩
  · intro j hj
    obtain ⟨t, _, he⟩ := Finset.mem_image.mp hj
    obtain ⟨c, hc, _⟩ := hsample.2 j t he.symm
    exact ⟨c, hc⟩
  · intro i j c c' hsource htarget htype hcoord
    obtain ⟨t, ht⟩ := cellRefinedGoodCell_some_implies_good left cell (sample.1 i) hsource
    have ht' : (sample.2 j).2.bind cellRefinedGoodType = some t := htype.symm.trans ht
    obtain ⟨c0, hc0, hKx⟩ := hsample.1 i t ht
    obtain ⟨c1, hc1, hKy⟩ := hsample.2 j t ht'
    have hc0' : c0 = c := Option.some.inj (hc0.symm.trans hsource)
    have hc1' : c1 = c' := Option.some.inj (hc1.symm.trans htarget)
    subst c0 c1
    apply hsep t c c' _ hKx _ hKy
    simpa only [populationFineGoodCoordinate, populationTypedCoordinate,
      ht, ht', Option.elim_some] using hcoord

end PopulationTypedCostData
end OTSelector.Reconstruction
