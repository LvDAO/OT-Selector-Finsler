import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Instances.Real.Lemmas
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerIntrinsicActiveMatching.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerIntrinsicActiveMatching`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.BorelEmbeddingCoordinateMatching

## Lemma skeleton

* **Conditions:** A measurable embedding into block coordinates, another measurable block map and, for balance, finite measures with equal first observed laws.
* **Objects:** Measurable coordinate matching, Borel active images, quotient-law balance and conullness.
* **Proof detail:** Use the embedding inverse on its measurable range and a default elsewhere; compose the exact observation identity, commute pushforwards and transport the active null complement.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (composition): Generic measurable-embedding matching; no Finsler parametrization or geometric two-cover theorem is used.
-/

/-!
# Borel block matching and quotient-law balance

This module supplies the Borel/measure-theoretic layer of the structural
invariance theorem (main.tex:958), closing the injective-image/Borel-inverse
step, the conullness of the active block set inside the quotient law, and the
propagation of the quotient-law balance eq:intrinsic-active-quotient across a
block matching T (as used by FinslerIntrinsicActiveInvariance.lean and
FinslerIntrinsicActiveRayDataFinsler.lean).

Given two block maps b_phi, b_psi : X -> Y on a physical law space X (the
active ray component maps of two optimal potentials phi, psi), with b_phi a
measurable embedding (injective with Borel image, the paper's
injective-image/Borel-inverse condition) and b_psi measurable, we prove:

* exists_measurable_matching: there is a Borel block matching T : Y -> Y with
  T (b_phi x) = b_psi x for all x, i.e. b_psi = T o b_phi (the Borel block
  map of the paper's identification step);
* measurableSet_blockImage: b_phi '' A is Borel for Borel A, and for an active
  set A carried by the physical law the quotient law is carried by the active
  block set b_phi '' A (conullness of the active block set);
* quotientLaw_balance_of_matching: if the phi-quotient laws of two physical
  marginals mu, nu agree, (b_phi)_#mu = (b_phi)_#nu, then so do the
  psi-quotient laws, (b_psi)_#mu = (b_psi)_#nu — the paper's balance step
  eq:intrinsic-active-quotient;
* exists_borelBlockMatching_with_balance: the bundled conclusion (Borel T,
  matching identity, quotient-law balance, and conullness in both quotient
  laws) abstractly closing gaps (ii)/(iii)/(iv) of
  FinslerIntrinsicFinslerRayCoupling.lean.

Remaining sub-gaps: (a) atomlessness of the conditional scalar laws — absolute
continuity of the conditional laws is not derivable from the window/input laws
alone and remains an explicit a.e. hypothesis of the flux construction;
(e) the geometric two-cover containment of the paper: the abstract order-set
core is in FinslerIntrinsicActiveInvariance.lean, whose geometric instantiation
needs the transported minimal calibrated arcs. This file does not depend on the
specific Finsler ray parametrization; it consumes only the Borel block maps.
-/

open Set Function MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false

/-- **Injective-image Borel step.** The image of a Borel set under a block map
which is a measurable embedding is Borel. -/
theorem measurableSet_blockImage {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {b : X → Y} (hb : MeasurableEmbedding b)
    {A : Set X} (hA : MeasurableSet A) : MeasurableSet (b '' A) :=
  hb.measurableSet_image' hA

/-- **Borel block matching.** If b_phi is a measurable embedding and b_psi is
Borel, there is a Borel map T with b_psi = T o b_phi (the paper's block
matching is Borel, hence so is its inverse on the image). -/
theorem exists_measurable_matching {X Y Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [Nonempty Z]
    (bφ : X → Y) (bψ : X → Z) (hbφ : MeasurableEmbedding bφ)
    (hbψ : Measurable bψ) :
    ∃ T : Y → Z, Measurable T ∧ ∀ x : X, T (bφ x) = bψ x := by
  classical
  let T : Y → Z := fun y ↦
    if h : ∃ x, bφ x = y then bψ (Classical.choose h) else Classical.arbitrary Z
  have hTval : ∀ x : X, T (bφ x) = bψ x := by
    intro x
    have hy : ∃ x', bφ x' = bφ x := ⟨x, rfl⟩
    show (if h : ∃ x', bφ x' = bφ x then bψ (Classical.choose h)
      else Classical.arbitrary Z) = bψ x
    rw [dif_pos hy]
    rw [hbφ.injective (Classical.choose_spec hy)]
  refine ⟨T, ?_, hTval⟩
  intro s hs
  have hEq : T ⁻¹' s = (range bφ ∩ bφ '' (bψ ⁻¹' s)) ∪
      ((range bφ)ᶜ ∩ (if Classical.arbitrary Z ∈ s then univ else ∅)) := by
    ext y
    constructor
    · intro hys
      change T y ∈ s at hys
      by_cases hy : ∃ x, bφ x = y
      · have hval : T y = bψ (Classical.choose hy) := dif_pos hy
        have hmem : bψ (Classical.choose hy) ∈ s := by
          rw [← hval]
          exact hys
        refine Or.inl ⟨hy, ?_⟩
        exact ⟨Classical.choose hy, hmem, Classical.choose_spec hy⟩
      · have hval : T y = Classical.arbitrary Z := dif_neg hy
        have hc : Classical.arbitrary Z ∈ s := by
          rw [hval] at hys
          exact hys
        exact Or.inr ⟨hy, by rw [if_pos hc]; exact mem_univ y⟩
    · rintro (⟨hy, himg⟩ | ⟨hy, hc⟩)
      · obtain ⟨x, hxs, hxy⟩ := himg
        show T y ∈ s
        have hval : T y = bψ (Classical.choose hy) := dif_pos hy
        rw [hval]
        have hx : Classical.choose hy = x := by
          apply hbφ.injective
          rw [Classical.choose_spec hy]
          exact hxy.symm
        rw [hx]
        exact hxs
      · show T y ∈ s
        have hval : T y = Classical.arbitrary Z := dif_neg hy
        rw [hval]
        by_cases hcin : Classical.arbitrary Z ∈ s
        · exact hcin
        · rw [if_neg hcin] at hc
          exact absurd hc (by simp)
  rw [hEq]
  refine MeasurableSet.union ?_ ?_
  · exact hbφ.measurableSet_range.inter (hbφ.measurableSet_image' (hbψ hs))
  · refine hbφ.measurableSet_range.compl.inter ?_
    by_cases hc : Classical.arbitrary Z ∈ s
    · rw [if_pos hc]
      exact MeasurableSet.univ
    · rw [if_neg hc]
      exact MeasurableSet.empty

/-- Evaluation form of the matching: b_psi = T o b_phi. -/
theorem blockMap_eq_matching {X Y : Type*} (bφ bψ : X → Y) (T : Y → Y)
    (hT : ∀ x : X, T (bφ x) = bψ x) : bψ = T ∘ bφ :=
  funext fun x ↦ (hT x).symm

/-- **Quotient-law balance propagation** (eq:intrinsic-active-quotient): if the
phi-quotient laws of two physical marginals agree, then the matched
psi-quotient laws agree. -/
theorem quotientLaw_balance_of_matching {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (bφ bψ : X → Y) (T : Y → Y)
    (hbφ : MeasurableEmbedding bφ) (hTmeas : Measurable T)
    (hT : ∀ x : X, T (bφ x) = bψ x)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hbal : μ.map bφ = ν.map bφ) : μ.map bψ = ν.map bψ := by
  have hcongr : ∀ ξ : Measure X, bψ =ᵐ[ξ] T ∘ bφ := fun ξ ↦
    Filter.Eventually.of_forall fun x ↦ (hT x).symm
  calc μ.map bψ = μ.map (T ∘ bφ) := Measure.map_congr (hcongr μ)
    _ = (μ.map bφ).map T := (Measure.map_map hTmeas hbφ.measurable).symm
    _ = (ν.map bφ).map T := by rw [hbal]
    _ = ν.map (T ∘ bφ) := Measure.map_map hTmeas hbφ.measurable
    _ = ν.map bψ := Measure.map_congr (hcongr ν).symm

/-- **Conullness of the active block set** in the quotient law: if the
physical law is carried by the Borel active set A and the block map is a
measurable embedding, then the quotient law is carried by the active block
set b '' A. -/
theorem quotientLaw_conull_active {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {b : X → Y} (hb : MeasurableEmbedding b)
    (law : Measure X) [IsFiniteMeasure law] {A : Set X}
    (hAmeas : MeasurableSet A) (hA : law Aᶜ = 0) :
    (law.map b) (b '' A)ᶜ = 0 := by
  have himg : MeasurableSet (b '' A) := hb.measurableSet_image' hAmeas
  rw [Measure.map_apply hb.measurable himg.compl]
  have hpre : b ⁻¹' (b '' A)ᶜ = Aᶜ := by
    ext x
    constructor
    · intro hx
      by_contra hxA
      have hxA' : x ∈ A := by simpa using hxA
      exact hx (mem_image_of_mem b hxA')
    · intro hx hmem
      rcases hmem with ⟨a, haA, hba⟩
      have hax : a = x := hb.injective hba
      rw [hax] at haA
      exact hx haA
  rw [hpre]
  exact hA

/-- The block (quotient) law of a probability law is a probability measure. -/
theorem quotientLaw_isProbability {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (b : X → Y) (hb : Measurable b) (law : Measure X)
    [IsProbabilityMeasure law] : IsProbabilityMeasure (law.map b) :=
  Measure.isProbabilityMeasure_map hb.aemeasurable

/-- **Bundled conclusion** (Borel block matching, matching identity, quotient-law
balance propagation, and conullness of the active block set in both quotient
laws), closing gaps (ii)/(iii)/(iv) of the active-block invariance theorem. -/
theorem exists_borelBlockMatching_with_balance {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Y]
    (bφ bψ : X → Y) (hbφ : MeasurableEmbedding bφ) (hbψ : Measurable bψ)
    {A : Set X} (hAmeas : MeasurableSet A)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμA : μ Aᶜ = 0) (hνA : ν Aᶜ = 0) (hbal : μ.map bφ = ν.map bφ) :
    ∃ T : Y → Y, Measurable T ∧ (∀ x : X, T (bφ x) = bψ x) ∧
      μ.map bψ = ν.map bψ ∧ (μ.map bφ) (bφ '' A)ᶜ = 0 ∧
        (ν.map bφ) (bφ '' A)ᶜ = 0 := by
  obtain ⟨T, hTmeas, hT⟩ := exists_measurable_matching bφ bψ hbφ hbψ
  exact ⟨T, hTmeas, hT,
    quotientLaw_balance_of_matching bφ bψ T hbφ hTmeas hT μ ν hbal,
    quotientLaw_conull_active hbφ μ hAmeas hμA,
    quotientLaw_conull_active hbφ ν hAmeas hνA⟩

end OTSelector.Reconstruction
end
end
