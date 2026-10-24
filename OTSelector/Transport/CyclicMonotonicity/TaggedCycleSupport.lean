import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Topology.Algebra.Module.Cardinality
import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity
import OTSelector.Transport.CyclicMonotonicity.CountableRectangleSupport
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedTaggedCycleSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedTaggedCycleSupport`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerPhysicalSceneRootedTaggedCycleSupport

**Conditions:** Countable macro and endpoint bases and locally vanishing strict-cycle witnesses for each actual tag in the specified parameter set.

**Objects:** One probability-one support certificate valid for the tag-dependent original legal cost.

**Proof detail:** Replace each local violating neighborhood by one of countably many macro basis sets and rectangular cycle indices; intersect their full events once, then use positive support masses to exclude every actual tagged violation.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6), Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products); [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# One probability-one support certificate for a cost depending on the actual tag

Local physical certificates can use different actual macro neighborhoods and
Taylor references. Countable macro and endpoint bases place all such locally
vanishing witnesses on one common probability-one event for the unchanged law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {V X Y Ω : Type*} [TopologicalSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Countable macro and endpoint bases turn local zero physical witnesses into
one common almost-sure legal no-cycle statement for the original tag-dependent
cost. No single coefficient is imposed on the whole source seed piece. -/
theorem ae_tagged_legal_twoCycle_support_of_local_zero_witnesses
    (P : Measure Ω) (tag : Ω → V) (π : Ω → Measure (X × Y))
    (K : Set V) (c : V → X → Y → ℝ) (D : V → Set (X × Y))
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (hBXcount : BX.Countable) (hBYcount : BY.Countable)
    (hlocal : ∀ w ∈ K, ∀ x y x' y',
      (x, y) ∈ D w → (x', y') ∈ D w → (x, y') ∈ D w → (x', y) ∈ D w →
      c w x y' + c w x' y < c w x y + c w x' y' →
      ∃ U : Set V, IsOpen U ∧ w ∈ U ∧
      ∃ i : CavityBasisCycleIndex BX BY,
        (x, y) ∈ i.1.1.1.val ×ˢ i.1.1.2.val ∧
        (x', y') ∈ i.1.2.1.val ×ˢ i.1.2.2.val ∧
        ∀ᵐ ω ∂P, tag ω ∈ U → cavityBasisCycleWitness (π ω) i = 0) :
    ∀ᵐ ω ∂P, tag ω ∈ K →
      IsTwoCycleMonotoneOn (c (tag ω)) (D (tag ω))
        ((π ω).support ∩ D (tag ω)) := by
  classical
  let B := countableBasis V
  let _instB : Countable B := (countable_countableBasis V).to_subtype
  let _instBX : Countable BX := hBXcount.to_subtype
  let _instBY : Countable BY := hBYcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ b : B, ∀ i : CavityBasisCycleIndex BX BY,
      (∀ᵐ ω' ∂P, tag ω' ∈ b.val → cavityBasisCycleWitness (π ω') i = 0) →
        tag ω ∈ b.val → cavityBasisCycleWitness (π ω) i = 0 := by
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro i
    by_cases hz : ∀ᵐ ω ∂P, tag ω ∈ b.val → cavityBasisCycleWitness (π ω) i = 0
    · exact hz.mono fun _ h _ ↦ h
    · exact ae_of_all _ fun _ h ↦ False.elim (hz h)
  filter_upwards [hall] with ω hω hwK
  intro x y x' y' hxy hxy' hcross hcross'
  by_contra hle
  obtain ⟨U, hU, hwU, i, hleft, hright, hzero⟩ := hlocal (tag ω) hwK x y x' y'
    hxy.2 hxy'.2 hcross hcross' (lt_of_not_ge hle)
  obtain ⟨b, hb, hwb, hbU⟩ := (isBasis_countableBasis V).mem_nhds_iff.mp (hU.mem_nhds hwU)
  have hzeroB : ∀ᵐ ω' ∂P, tag ω' ∈ b → cavityBasisCycleWitness (π ω') i = 0 :=
    hzero.mono fun _ hz hb ↦ hz (hbU hb)
  have hz : cavityBasisCycleWitness (π ω) i = 0 := hω ⟨b, hb⟩ i hzeroB hwb
  have hp := (Measure.mem_support_iff_forall _).mp hxy.1 _
    (((hBX.isOpen i.1.1.1.property).prod (hBY.isOpen i.1.1.2.property)).mem_nhds hleft)
  have hp' := (Measure.mem_support_iff_forall _).mp hxy'.1 _
    (((hBX.isOpen i.1.2.1.property).prod (hBY.isOpen i.1.2.2.property)).mem_nhds hright)
  have hpos : 0 < cavityBasisCycleWitness (π ω) i := lt_min zero_lt_one (lt_min hp hp')
  exact (ne_of_gt hpos) hz

end OTSelector.Reconstruction

end
end
