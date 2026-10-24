import OTSelector.Transport.Coupling.FiniteMarginalSplit
import OTSelector.Transport.Coupling.FiniteMeasureGluing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingSplice.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingSplice`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingSplice

**Conditions:** Two finite plans share a continuing middle submeasure and have separate exit/birth remainders on a standard Borel gluing space.

**Objects:** A genuine three-point continuing joint and the three allowed ancestry branches in the labelled splice.

**Proof detail:** Use Radon–Nikodym splitting to isolate the common middle mass, glue its two parts, and retain the two one-sided branches; direct marginal calculation excludes a birth-to-earlier-exit branch.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4).

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Actual one-cut splicing keeps the three allowed source/target ancestry
branches and their genuine three-point joint. -/
open MeasureTheory ProbabilityTheory Set
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 500000
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [StandardBorelSpace C] [Nonempty C]

/-- The actual finite subplans and three-point joint at one class cut. -/
structure FiniteStageSpliceWitness (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    (ρ ν ζ : Measure B) where
  leftContinue : Measure (A × B)
  leftExit : Measure (A × B)
  rightContinue : Measure (B × C)
  rightBirth : Measure (B × C)
  triple : Measure ((A × B) × C)
  leftContinue_finite : IsFiniteMeasure leftContinue
  leftExit_finite : IsFiniteMeasure leftExit
  rightContinue_finite : IsFiniteMeasure rightContinue
  rightBirth_finite : IsFiniteMeasure rightBirth
  triple_finite : IsFiniteMeasure triple
  left_decomp : leftContinue + leftExit = π₁
  right_decomp : rightContinue + rightBirth = π₂
  leftContinue_snd : leftContinue.snd = ρ
  leftExit_snd : leftExit.snd = ν
  rightContinue_fst : rightContinue.fst = ρ
  rightBirth_fst : rightBirth.fst = ζ
  triple_fst : triple.fst = leftContinue
  triple_snd_pair : triple.map (fun z ↦ (z.1.2, z.2)) = rightContinue

/-- The witness is constructed from the two actual finite plans by RN splitting
and disintegration, with no completed gluing or ancestry input. -/
theorem exists_finiteStageSpliceWitness
    (π₁ : Measure (A × B)) (π₂ : Measure (B × C))
    [IsFiniteMeasure π₁] [IsFiniteMeasure π₂]
    (ρ ν ζ : Measure B) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] [IsFiniteMeasure ζ]
    (h₁ : π₁.snd = ρ + ν) (h₂ : π₂.fst = ρ + ζ) :
    Nonempty (FiniteStageSpliceWitness π₁ π₂ ρ ν ζ) := by
  obtain ⟨α, β, hα, hβ, hsum₁, hαρ, hβν⟩ :=
    exists_finiteStageCoupling_target_split π₁ ρ ν h₁
  obtain ⟨γ, δ, hγ, hδ, hsum₂, hγρ, hδζ⟩ :=
    exists_finiteStageCoupling_source_split π₂ ρ ζ h₂
  have : IsFiniteMeasure α := hα
  have : IsFiniteMeasure γ := hγ
  obtain ⟨θ, hθ, hθα, hθγ⟩ := exists_finiteStageCouplingJoint α γ (hαρ.trans hγρ.symm)
  exact ⟨⟨α, β, γ, δ, θ, hα, hβ, hγ, hδ, hθ, hsum₁, hsum₂,
    hαρ, hβν, hγρ, hδζ, hθα, hθγ⟩⟩

/-- The actual labelled plan consists of old exits, continuing old paths and
fresh births. There is no fresh-source to old-target branch. -/
def FiniteStageSpliceWitness.labelPlan
    {π₁ : Measure (A × B)} {π₂ : Measure (B × C)} {ρ ν ζ : Measure B}
    (w : FiniteStageSpliceWitness π₁ π₂ ρ ν ζ) : Measure ((A ⊕ B) × (B ⊕ C)) :=
  w.leftExit.map (Prod.map Sum.inl Sum.inl) +
    w.triple.map (fun z ↦ (Sum.inl z.1.1, Sum.inr z.2)) +
      w.rightBirth.map (Prod.map Sum.inr Sum.inr)

omit [StandardBorelSpace C] [Nonempty C] in
/-- Both labelled marginals are exact, so the source and target class labels
are retained through the physical middle marginal. -/
theorem FiniteStageSpliceWitness.labelPlan_isCoupling
    {π₁ : Measure (A × B)} {π₂ : Measure (B × C)} {ρ ν ζ : Measure B}
    (w : FiniteStageSpliceWitness π₁ π₂ ρ ν ζ) :
    Vlasov.IsCoupling w.labelPlan
      (π₁.fst.map Sum.inl + ζ.map Sum.inr)
      (ν.map Sum.inl + π₂.snd.map Sum.inr) := by
  have hleft : w.leftContinue.fst + w.leftExit.fst = π₁.fst := by
    simpa only [Measure.fst, Measure.map_add _ _ measurable_fst] using
      congrArg Measure.fst w.left_decomp
  have hright : w.rightContinue.snd + w.rightBirth.snd = π₂.snd := by
    simpa only [Measure.snd, Measure.map_add _ _ measurable_snd] using
      congrArg Measure.snd w.right_decomp
  have hpair : Measurable (fun z : (A × B) × C ↦ (z.1.2, z.2)) := by fun_prop
  have hcoord : Measurable (fun z : (A × B) × C ↦ z.1.1) := by fun_prop
  have htag : Measurable (fun z : (A × B) × C ↦
      ((Sum.inl z.1.1 : A ⊕ B), (Sum.inr z.2 : B ⊕ C))) := by fun_prop
  have htripleL : w.triple.map (fun z ↦ z.1.1) = w.leftContinue.fst := by
    calc
      _ = w.triple.fst.fst := by
        change _ = (w.triple.map Prod.fst).map Prod.fst
        rw [Measure.map_map measurable_fst measurable_fst]
        rfl
      _ = _ := congrArg Measure.fst w.triple_fst
  have htripleR : w.triple.map Prod.snd = w.rightContinue.snd := by
    calc
      _ = (w.triple.map (fun z ↦ (z.1.2, z.2))).snd := by
        change _ = (w.triple.map (fun z ↦ (z.1.2, z.2))).map Prod.snd
        rw [Measure.map_map measurable_snd hpair]
        rfl
      _ = _ := congrArg Measure.snd w.triple_snd_pair
  constructor
  · simp only [labelPlan, Measure.map_add _ _ measurable_fst,
      Measure.map_map measurable_fst (measurable_inl.prodMap measurable_inl),
      Measure.map_map measurable_fst htag,
      Measure.map_map measurable_fst (measurable_inr.prodMap measurable_inr)]
    change w.leftExit.map (Sum.inl ∘ Prod.fst) +
      w.triple.map (Sum.inl ∘ (fun z ↦ z.1.1)) +
      w.rightBirth.map (Sum.inr ∘ Prod.fst) = _
    rw [← Measure.map_map measurable_inl measurable_fst,
      ← Measure.map_map measurable_inl hcoord,
      ← Measure.map_map measurable_inr measurable_fst]
    change w.leftExit.fst.map Sum.inl +
      (w.triple.map (fun z ↦ z.1.1)).map Sum.inl +
      w.rightBirth.fst.map Sum.inr = _
    rw [htripleL, w.rightBirth_fst]
    rw [← Measure.map_add _ _ measurable_inl, add_comm w.leftExit.fst, hleft]
  · simp only [labelPlan, Measure.map_add _ _ measurable_snd,
      Measure.map_map measurable_snd (measurable_inl.prodMap measurable_inl),
      Measure.map_map measurable_snd htag,
      Measure.map_map measurable_snd (measurable_inr.prodMap measurable_inr)]
    change w.leftExit.map (Sum.inl ∘ Prod.snd) +
      w.triple.map (Sum.inr ∘ Prod.snd) +
      w.rightBirth.map (Sum.inr ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_inl measurable_snd,
      ← Measure.map_map measurable_inr measurable_snd,
      ← Measure.map_map measurable_inr measurable_snd]
    change w.leftExit.snd.map Sum.inl + (w.triple.map Prod.snd).map Sum.inr +
      w.rightBirth.snd.map Sum.inr = _
    rw [w.leftExit_snd, htripleR]
    rw [add_assoc, ← Measure.map_add _ _ measurable_inr, hright]

omit [StandardBorelSpace C] [Nonempty C] in
/-- The forbidden fresh-source to old-target class rectangle has exactly zero
mass in the constructed plan; ancestry is a proved property of the construction. -/
theorem FiniteStageSpliceWitness.labelPlan_no_birth_to_earlier_target
    {π₁ : Measure (A × B)} {π₂ : Measure (B × C)} {ρ ν ζ : Measure B}
    (w : FiniteStageSpliceWitness π₁ π₂ ρ ν ζ) :
    w.labelPlan (range (Sum.inr : B → A ⊕ B) ×ˢ range (Sum.inl : B → B ⊕ C)) = 0 := by
  let s : Set ((A ⊕ B) × (B ⊕ C)) :=
    range (Sum.inr : B → A ⊕ B) ×ˢ range (Sum.inl : B → B ⊕ C)
  have hs : MeasurableSet s := measurableSet_range_inr.prod measurableSet_range_inl
  have hleft : (Prod.map (Sum.inl : A → A ⊕ B) (Sum.inl : B → B ⊕ C)) ⁻¹' s = ∅ := by
    ext p
    simp [s]
  have hmid : (fun p : (A × B) × C ↦
      ((Sum.inl p.1.1 : A ⊕ B), (Sum.inr p.2 : B ⊕ C))) ⁻¹' s = ∅ := by
    ext p
    simp [s]
  have hright : (Prod.map (Sum.inr : B → A ⊕ B) (Sum.inr : C → B ⊕ C)) ⁻¹' s = ∅ := by
    ext p
    simp [s]
  have hm : Measurable (fun p : (A × B) × C ↦
      ((Sum.inl p.1.1 : A ⊕ B), (Sum.inr p.2 : B ⊕ C))) := by fun_prop
  change w.labelPlan s = 0
  simp only [labelPlan, Measure.add_apply,
    Measure.map_apply (measurable_inl.prodMap measurable_inl) hs,
    Measure.map_apply hm hs,
    Measure.map_apply (measurable_inr.prodMap measurable_inr) hs,
    hleft, hmid, hright, measure_empty, zero_add]

end OTSelector.Reconstruction

end
end
