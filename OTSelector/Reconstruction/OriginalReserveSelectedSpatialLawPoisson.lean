import OTSelector.Reconstruction.OriginalStageReservePoissonFactorization
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawInfinite

/-! The actual Poisson reserve observation supplies selected-position joint laws on mark fibres. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Probability

/-- Include any independent original main/other-color data in the auxiliary count/mark law. -/
def originalReserveAuxSplit {q : ℕ} {A Z : Type*} (p : Z × MarkedCloudSpace q A) :
    (Z × (ℕ × (ℕ → A))) × (ℕ → (Fin q → ℝ)) :=
  ((p.1, p.2.1, fun i ↦ (p.2.2 i).2), fun i ↦ (p.2.2 i).1)

/-- The same original experiment factors with all independent auxiliary data retained. -/
theorem map_originalReserveAuxSplit_markedPoissonLaw
    {Z A : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    (P : Measure Z) [IsFiniteMeasure P] (q : ℕ) (α : Measure A) [IsProbabilityMeasure α] (rate : ℝ≥0) :
    (P.prod (markedPoissonLaw q A α rate)).map originalReserveAuxSplit =
      (P.prod (originalReserveCountMarkLaw α rate)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1)) := by
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have hm : Measurable (originalReserveCloudSplit (q := q) (A := A)) := by
    unfold originalReserveCloudSplit
    fun_prop
  rw [show originalReserveAuxSplit = MeasurableEquiv.prodAssoc.symm ∘
      Prod.map id (originalReserveCloudSplit (q := q) (A := A)) from rfl,
    ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap hm),
    ← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id,
    map_originalReserveCloudSplit_markedPoissonLaw]
  have hassoc := Measure.prodAssoc_prod (μ := P) (ν := originalReserveCountMarkLaw α rate)
    (τ := Measure.infinitePi (fun _ : ℕ ↦ cubeMeasure (Fin q) 1))
  conv_lhs => rw [← hassoc]
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable MeasurableEquiv.prodAssoc.measurable]
  simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]

/-- Actual original Poisson positions selected by an auxiliary/count/mark-only injection keep
the exact joint finite iid law. No desired selected-position law is assumed. -/
theorem map_originalReserveSelectedPositions_joint
    {Z A J : Type*} [MeasurableSpace Z] [MeasurableSpace A] [Fintype J]
    (P : Measure Z) [IsFiniteMeasure P] (q : ℕ) (α : Measure A) [IsProbabilityMeasure α] (rate : ℝ≥0)
    (e : (Z × (ℕ × (ℕ → A))) → J ↪ ℕ) (he : ∀ j, Measurable (fun z ↦ e z j)) :
    (P.prod (markedPoissonLaw q A α rate)).map
      (fun p ↦ ((p.1, p.2.1, fun i ↦ (p.2.2 i).2),
        fun j ↦ (p.2.2 (e (p.1, p.2.1, fun i ↦ (p.2.2 i).2) j)).1)) =
      (P.prod (originalReserveCountMarkLaw α rate)).prod
        (Measure.pi (fun _ : J ↦ cubeMeasure (Fin q) 1)) := by
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have heval : Measurable (fun p : ℕ × (ℕ → (Fin q → ℝ)) ↦ p.2 p.1) :=
    measurable_from_prod_countable_right (fun i ↦ measurable_pi_apply i)
  have hselect : Measurable (fun p : (Z × (ℕ × (ℕ → A))) × (ℕ → (Fin q → ℝ)) ↦
      (p.1, fun j ↦ p.2 (e p.1 j))) :=
    measurable_fst.prodMk (measurable_pi_lambda _ (fun j ↦
      heval.comp (((he j).comp measurable_fst).prodMk measurable_snd)))
  have hsplit : Measurable (originalReserveAuxSplit (q := q) (A := A) (Z := Z)) := by
    unfold originalReserveAuxSplit
    fun_prop
  change (P.prod (markedPoissonLaw q A α rate)).map
    ((fun p : (Z × (ℕ × (ℕ → A))) × (ℕ → (Fin q → ℝ)) ↦
      (p.1, fun j ↦ p.2 (e p.1 j))) ∘ originalReserveAuxSplit) = _
  rw [← Measure.map_map hselect hsplit, map_originalReserveAuxSplit_markedPoissonLaw,
    map_mark_selected_original_infinite_iid_positions _ _ e he]

/-- Restrict to an actual count/mark event, including a fixed actual kept-cardinality fibre.
The unnormalized event law factors with the exact same iid selected positions. -/
theorem map_originalReserveSelectedPositions_joint_restrict_aux
    {Z A J : Type*} [MeasurableSpace Z] [MeasurableSpace A] [Fintype J]
    (P : Measure Z) [IsFiniteMeasure P] (q : ℕ) (α : Measure A) [IsProbabilityMeasure α] (rate : ℝ≥0)
    (e : (Z × (ℕ × (ℕ → A))) → J ↪ ℕ) (he : ∀ j, Measurable (fun z ↦ e z j))
    {E : Set (Z × (ℕ × (ℕ → A)))} (hE : MeasurableSet E) :
    ((P.prod (markedPoissonLaw q A α rate)).restrict
      {p | (p.1, p.2.1, fun i ↦ (p.2.2 i).2) ∈ E}).map
      (fun p ↦ ((p.1, p.2.1, fun i ↦ (p.2.2 i).2),
        fun j ↦ (p.2.2 (e (p.1, p.2.1, fun i ↦ (p.2.2 i).2) j)).1)) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict E).prod
        (Measure.pi (fun _ : J ↦ cubeMeasure (Fin q) 1)) := by
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  have heval : Measurable (fun p : ℕ × (ℕ → (Fin q → ℝ)) ↦ p.2 p.1) :=
    measurable_from_prod_countable_right (fun i ↦ measurable_pi_apply i)
  have haux : Measurable (fun p : Z × MarkedCloudSpace q A ↦
      (p.1, p.2.1, fun i ↦ (p.2.2 i).2)) := by fun_prop
  have hpositions : Measurable (fun p : Z × MarkedCloudSpace q A ↦
      fun i ↦ (p.2.2 i).1) := by fun_prop
  have hm : Measurable (fun p : Z × MarkedCloudSpace q A ↦
      ((p.1, p.2.1, fun i ↦ (p.2.2 i).2),
        fun j ↦ (p.2.2 (e (p.1, p.2.1, fun i ↦ (p.2.2 i).2) j)).1)) :=
    haux.prodMk (measurable_pi_lambda _ (fun j ↦
      heval.comp (((he j).comp haux).prodMk hpositions)))
  rw [show {p : Z × MarkedCloudSpace q A | (p.1, p.2.1, fun i ↦ (p.2.2 i).2) ∈ E} =
      (fun p : Z × MarkedCloudSpace q A ↦ ((p.1, p.2.1, fun i ↦ (p.2.2 i).2),
        fun j ↦ (p.2.2 (e (p.1, p.2.1, fun i ↦ (p.2.2 i).2) j)).1)) ⁻¹' (E ×ˢ univ) from by ext p; simp,
    ← Measure.restrict_map hm (hE.prod MeasurableSet.univ),
    map_originalReserveSelectedPositions_joint P q α rate e he,
    ← Measure.prod_restrict, Measure.restrict_univ]

end OTSelector.Probability
