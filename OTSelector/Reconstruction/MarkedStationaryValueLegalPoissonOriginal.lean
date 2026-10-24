import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonMap

/-!
# Original scalar populations produce the legal Poisson count bound

The original coupling's finite scalar-bin restrictions construct both RN type
laws, their common type probabilities and same-type forward legality. Full
population retention removes the residual type on the actual input law. Exact
mark pushforwards then remove all auxiliary RN tags and return the square-root
Hall-defect estimate to the original independent marked Poisson clouds.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The actual original scalar-bin RN construction gives the Poisson Hall-defect
bound on the unchanged, unmarked original two-color Poisson inputs. -/
theorem scalarBinPopulationTypes_poisson_legalMaximumCard_defect
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
    [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
    (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1) (q : ℕ) (r : ℝ≥0) :
    let P₀ := twoMarkedCloudLaw q X Y μ ν r
    let deficit := fun ω : TwoMarkedCloudSpace q X Y ↦
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
        legalMarkedMaximumCard q source target ω
    Integrable deficit P₀ ∧ (∫ ω, deficit ω ∂P₀) ≤ (1 / 2 : ℝ) *
      Real.sqrt (2 * (r : ℝ) * Fintype.card (Option (J × Fin D.count × Fin D.count))) := by
  classical
  let Types := scalarBinPopulationTypes D chart source target π hchart hs ht
  let Tag := Option (J × Fin D.count × Fin D.count)
  let K := Fintype.card Tag
  let e : Tag ≃ Fin K := Fintype.equivFin Tag
  let α := Types.sourceMarkedLaw μ
  let β := Types.targetMarkedLaw ν
  have hprob := Types.marked_probabilities hπ
  let : IsProbabilityMeasure α := hprob.1
  let : IsProbabilityMeasure β := hprob.2.1
  let : IsProbabilityMeasure Types.typeLaw := hprob.2.2
  have he : Measurable e := measurable_of_countable _
  let L := Types.typeLaw.map e
  let : IsProbabilityMeasure L := Measure.isProbabilityMeasure_map he.aemeasurable
  have hA : Measurable (fun x : X × Tag ↦ e x.2) := he.comp measurable_snd
  have hB : Measurable (fun y : Y × Tag ↦ e y.2) := he.comp measurable_snd
  have hLA : α.map (fun x : X × Tag ↦ e x.2) = L := by
    rw [show (fun x : X × Tag ↦ e x.2) = e ∘ Prod.snd from rfl,
      ← Measure.map_map he measurable_snd, (Types.marked_type_laws hπ).1]
  have hLB : β.map (fun y : Y × Tag ↦ e y.2) = L := by
    rw [show (fun y : Y × Tag ↦ e y.2) = e ∘ Prod.snd from rfl,
      ← Measure.map_map he measurable_snd, (Types.marked_type_laws hπ).2]
  have hfull : ∑ t, Types.component t = π :=
    scalarBinPopulationTypes_sum_eq D chart source target π hchart hs ht hI
  have hsome := Types.iid_marked_ae_some_of_sum_eq (I := Unit) (J := Unit) hπ hfull
  have hhalf := scalarBinPopulationTypes_iid_half_gap D chart source target π
    (μ := μ) (ν := ν) hchart hs ht (NS := Unit) (NT := Unit) hgap
  let Pone := (Measure.pi (fun _ : Unit ↦ α)).prod (Measure.pi (fun _ : Unit ↦ β))
  let read : ((Unit → X × Tag) × (Unit → Y × Tag)) → ((X × Tag) × (Y × Tag)) :=
    fun ω ↦ (ω.1 (), ω.2 ())
  have hread : Measurable read := by fun_prop
  have hmap : Pone.map read = α.prod β := by
    change ((Measure.pi (fun _ : Unit ↦ α)).prod (Measure.pi (fun _ : Unit ↦ β))).map
      (Prod.map (Function.eval ()) (Function.eval ())) = _
    rw [← Measure.map_prod_map _ _ (measurable_pi_apply ()) (measurable_pi_apply ()),
      Measure.pi_map_eval, Measure.pi_map_eval]
    simp
  have htypeMeas : MeasurableSet {p : (X × Tag) × (Y × Tag) |
      e p.1.2 = e p.2.2 → source p.1.1 < target p.2.1} := by
    have htags : MeasurableSet {p : (X × Tag) × (Y × Tag) | e p.1.2 = e p.2.2} :=
      measurableSet_eq_fun (hA.comp measurable_fst) (hB.comp measurable_snd)
    have hclock : MeasurableSet {p : (X × Tag) × (Y × Tag) |
        source p.1.1 < target p.2.1} := measurableSet_lt
      (hs.comp (measurable_fst.comp measurable_fst))
      (ht.comp (measurable_fst.comp measurable_snd))
    have hrepr : {p : (X × Tag) × (Y × Tag) |
        e p.1.2 = e p.2.2 → source p.1.1 < target p.2.1} =
        {p | e p.1.2 = e p.2.2}ᶜ ∪ {p | source p.1.1 < target p.2.1} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [hrepr]
    exact htags.compl.union hclock
  have htype : ∀ᵐ p ∂α.prod β, e p.1.2 = e p.2.2 → source p.1.1 < target p.2.1 := by
    rw [← hmap]
    apply (ae_map_iff hread.aemeasurable htypeMeas).mpr
    filter_upwards [hsome, hhalf] with ω hωs hωg
    intro hij
    have htag : (ω.1 ()).2 = (ω.2 ()).2 := e.injective hij
    obtain ⟨t, hit⟩ := hωs.1 ()
    have hjt : (ω.2 ()).2 = some t := htag.symm.trans hit
    have h := hωg () () t hit hjt
    change source (ω.1 ()).1 < target (ω.2 ()).1
    linarith
  have hKpos : 0 < K := Fintype.card_pos_iff.mpr (show Nonempty Tag from ⟨none⟩)
  let : NeZero K := ⟨hKpos.ne'⟩
  have haux := integral_legalMarkedMaximumCard_defect_le_of_typeRectangles q
    (hs.comp measurable_fst) (ht.comp measurable_fst) α β hA hB L hLA hLB r htype
  let P₀ := twoMarkedCloudLaw q X Y μ ν r
  let deficit := fun ω : TwoMarkedCloudSpace q X Y ↦
    ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
      legalMarkedMaximumCard q source target ω
  let forget := Prod.map (mapMarkedCloud (q := q) (Prod.fst : X × Tag → X))
    (mapMarkedCloud (q := q) (Prod.fst : Y × Tag → Y))
  have hf : Measurable forget :=
    (measurable_mapMarkedCloud measurable_fst).prodMap (measurable_mapMarkedCloud measurable_fst)
  have hforget : (twoMarkedCloudLaw q (X × Tag) (Y × Tag) α β r).map forget = P₀ :=
    map_twoMarkedCloudLaw_marks q α β μ ν measurable_fst measurable_fst
      (Types.marked_physical_laws hπ).1 (Types.marked_physical_laws hπ).2 r
  have hdm : Measurable deficit :=
    (measurable_from_nat.comp ((measurable_mSourceCount q).min (measurable_mTargetCount q))).sub
      (measurable_legalMarkedMaximumCard_cast q hs ht)
  have hid : (∫ ω, deficit ω ∂P₀) = ∫ ω, deficit (forget ω)
      ∂twoMarkedCloudLaw q (X × Tag) (Y × Tag) α β r := by
    rw [← hforget, integral_map hf.aemeasurable hdm.aestronglyMeasurable]
  exact ⟨integrable_legalMarkedMaximumCard_defect q hs ht μ ν r, hid.trans_le haux⟩

end OTSelector.Reconstruction
