import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.MeasureTheory.LusinCompactProperty
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.MeasurableContinuousSections.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.MeasurableContinuousSections`; the selected original proof blocks follow. -/
section

/-!
Conditions: A measurable parameter family with continuous sections on the good set, compact metric section domain and the stated finite inner-regular measure.

Objects: A measurable continuous-function-valued representative and large compact sets with joint continuity and the requested property.

Proof detail: Embed continuous sections by evaluations on a countable dense set, invert the measurable embedding, and apply Lusin after removing the exceptional null set.

Sources: D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30); D. H. Fremlin, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416 (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110); D. H. Fremlin, Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11 (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3).
Relation: A locally implemented measurable continuous-section construction; the dense evaluation code is not claimed as the book’s exact encoding.
-/

/-!
# Measurable continuous sections and uniform compact cores

Countably many dense evaluations embed a continuous function on a compact metric
space into a countable product. The measurable inverse gives a measurable section
representative agreeing at every continuous section, even when the good set has
not separately been shown measurable.
-/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {Ω Y V : Type*} [MeasurableSpace Ω]
  [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [NormedAddCommGroup V] [CompleteSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]

local instance : MeasurableSpace C(Y, V) := borel _
local instance : BorelSpace C(Y, V) := ⟨rfl⟩

/-- Measurable evaluations admit a Borel continuous-function representative which
agrees with every genuinely continuous section, without a measurable good-set assumption. -/
theorem exists_measurable_continuous_sections (f : Ω → Y → V)
    (hf : ∀ y, Measurable (fun x ↦ f x y)) :
    ∃ g : Ω → C(Y, V), Measurable g ∧
      ∀ x, Continuous (f x) → ∀ y, g x y = f x y := by
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense Y
  let : Countable s := hs.to_subtype
  let ev : C(Y, V) → s → V := fun g y ↦ g y
  have hevc : Continuous ev := continuous_pi (fun y ↦ continuous_eval_const (y : Y))
  have hevi : Injective ev := by
    intro g h heq
    apply DFunLike.ext'
    apply g.continuous.ext_on hd h.continuous
    intro y hy
    exact congrFun heq ⟨y, hy⟩
  have he : MeasurableEmbedding ev := hevc.measurable.measurableEmbedding hevi
  let read : (s → V) → C(Y, V) := extend ev id (fun _ ↦ 0)
  have hr : Measurable read := he.measurable_extend measurable_id measurable_const
  refine ⟨fun x ↦ read (fun y ↦ f x y),
    hr.comp (measurable_pi_lambda _ (fun y ↦ hf y)), ?_⟩
  intro x hx y
  have heq := hevi.extend_apply id (fun _ ↦ (0 : C(Y, V))) (⟨f x, hx⟩ : C(Y, V))
  exact congrArg (fun g : C(Y, V) ↦ g y) heq

/-- Lusin compactness holds for the entire compact parameter section and retains
any almost-everywhere property. The conclusion is joint continuity on the compact product. -/
theorem exists_lusin_compact_continuous_sections
    [TopologicalSpace Ω] [PolishSpace Ω] [BorelSpace Ω]
    {ν : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hνs : ν s ≠ ∞)
    (f : Ω → Y → V) (hf : ∀ y, Measurable (fun x ↦ f x y))
    {P : Ω → Prop} (hP : ∀ᵐ x ∂ν.restrict s, Continuous (f x) ∧ P x)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      ContinuousOn (fun q : Ω × Y ↦ f q.1 q.2) (K ×ˢ univ) ∧ ∀ x ∈ K, P x := by
  obtain ⟨g, hg, heq⟩ := exists_measurable_continuous_sections f hf
  obtain ⟨K, hKs, hK, hsmall, hgK, hgood⟩ :=
    exists_lusin_compact_core_with_ae_property hs hνs hg hP hε
  refine ⟨K, hKs, hK, hsmall, ?_, fun x hx ↦ (hgood x hx).2⟩
  have hc : ContinuousOn (fun q : Ω × Y ↦ g q.1 q.2) (K ×ˢ univ) :=
    continuous_eval.comp_continuousOn
      ((hgK.comp continuousOn_fst (fun _ hq ↦ hq.1)).prodMk continuousOn_snd)
  apply hc.congr
  intro q hq
  exact (heq q.1 (hgood q.1 hq.1).1 q.2).symm

omit [CompactSpace Y] in
/-- The compact-section result expressed on a compact subset of the original parameter space. -/
theorem exists_lusin_compact_continuous_sections_on
    [TopologicalSpace Ω] [PolishSpace Ω] [BorelSpace Ω]
    {ν : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hνs : ν s ≠ ∞)
    {T : Set Y} (hT : IsCompact T) (f : Ω → Y → V)
    (hf : ∀ y, Measurable (fun x ↦ f x y))
    {P : Ω → Prop} (hP : ∀ᵐ x ∂ν.restrict s, ContinuousOn (f x) T ∧ P x)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      ContinuousOn (fun q : Ω × Y ↦ f q.1 q.2) (K ×ˢ T) ∧ ∀ x ∈ K, P x := by
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have hPc : ∀ᵐ x ∂ν.restrict s, Continuous (fun y : T ↦ f x y) ∧ P x := by
    filter_upwards [hP] with x hx
    exact ⟨hx.1.domRestrict, hx.2⟩
  obtain ⟨K, hKs, hK, hsmall, hc, hgood⟩ :=
    exists_lusin_compact_continuous_sections hs hνs (fun x (y : T) ↦ f x y)
      (fun y ↦ hf y) hPc hε
  refine ⟨K, hKs, hK, hsmall, ?_, hgood⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hr : Continuous (fun q : K ×ˢ T ↦
      (q.val.1, (⟨q.val.2, q.property.2⟩ : T))) :=
    continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  exact hc.comp_continuous hr (fun q ↦ ⟨q.property.1, mem_univ _⟩)

end OTSelector.Geometry

end
end
