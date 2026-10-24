import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureMoments
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.MeasureTheory.LocalFiniteMeasureProbability
import OTSelector.MeasureTheory.LocalFiniteMeasureTightness
import OTSelector.Probability.JointLawTightness
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.LocalFiniteMeasureMarginalTightness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.LocalFiniteMeasureMarginalTightness`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.LocalFiniteMeasureMarginalTightness

## Lemma skeleton

* **Conditions:** Measurable locally finite plan laws dominated after continuous projection by actual target measures with uniform finite local first or second moments.
* **Objects:** Plan/joint-law tightness and a weakly convergent subsequence of the actual two-plan-plus-target laws.
* **Proof detail:** A compact source-plan window maps into a compact target window. Transfer target local moment bounds, convert second moments by 2f<=f²+1 and apply local-mass tightness and forward Prokhorov, preserving the joint sample law.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=68): Section 437P and Theorem 437R(f), (g), (h), tightness, compact measure sets and metrizability.
- [Olav Kallenberg, Random Measures, Theory and Applications (Springer 2017)](https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4): Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=211): Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).

Source relation (composition): Marginal-dominated compactness assembly; no independent replacement of the two plans or completeness assumption beyond the actual carrier setup.
-/

/-!
# Joint plan-law tightness from the actual common target marginal

Every compact plan window projects into a compact target window. Original target
local moments therefore control both plans and their actual joint law, without
additional plan-moment assumptions or independent replacement couplings.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability.LocalFiniteMeasure

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [BorelSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [BorelSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]

omit [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y] in
/-- A continuous observation dominated by the actual target measure controls
all compact plan windows, even when the observation itself is not proper. -/
theorem isTightMeasureSet_map_of_dominated_pushforward
    {I : Type*} {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i))
    (plan : ∀ i, Ω i → LocalFiniteMeasure X) (hplan : ∀ i, Measurable (plan i))
    (target : ∀ i, Ω i → LocalFiniteMeasure Y)
    (f : X → Y) (hf : Continuous f)
    (hdom : ∀ i, ∀ᵐ ω ∂P i, (plan i ω : Measure X).map f ≤ (target i ω : Measure Y))
    (KX : CompactExhaustion X) (KY : CompactExhaustion Y)
    (b : ℕ → ℝ≥0∞) (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ i n, ∫⁻ ω, (target i ω : Measure Y) (interior (KY n)) ∂P i ≤ b n) :
    IsTightMeasureSet (range (fun i ↦ (P i).map (plan i))) := by
  have hc : ∀ n, ∃ k, f '' KX n ⊆ interior (KY k) := by
    intro n
    obtain ⟨k, hk⟩ := KY.exists_superset_of_isCompact ((KX.isCompact n).image hf)
    exact ⟨k + 1, hk.trans (KY.subset_interior_succ k)⟩
  choose k hk using hc
  refine isTightMeasureSet_map_of_lintegral_localMass_le P plan hplan
    (fun n ↦ interior (KX n)) (fun _ ↦ isOpen_interior) ?_
    (fun n ↦ b (k n)) (fun n ↦ hb (k n)) ?_
  · intro A hA
    obtain ⟨n, hn⟩ := KX.exists_superset_of_isCompact hA
    exact ⟨n + 1, hn.trans (KX.subset_interior_succ n)⟩
  · intro i n
    apply le_trans _ (hbound i (k n))
    apply lintegral_mono_ae
    filter_upwards [hdom i] with ω hω
    calc
      (plan i ω : Measure X) (interior (KX n)) ≤
          (plan i ω : Measure X) (f ⁻¹' interior (KY (k n))) :=
        measure_mono (fun x hx ↦ hk n ⟨x, interior_subset hx, rfl⟩)
      _ = ((plan i ω : Measure X).map f) (interior (KY (k n))) :=
        (Measure.map_apply hf.measurable isOpen_interior.measurableSet).symm
      _ ≤ (target i ω : Measure Y) (interior (KY (k n))) := hω _

omit [T2Space Y] in
/-- A local second-moment estimate directly bounds the corresponding actual
nonnegative mass integral used by all three laws. -/
theorem lintegral_exhaustionMass_le_of_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (target : Ω → LocalFiniteMeasure Y) (htarget : Measurable target)
    (K : CompactExhaustion Y) (n : ℕ) {C : ℝ}
    (hsq : Integrable (fun ω ↦ ((target ω : Measure Y).real (interior (K n))) ^ 2) P)
    (hbound : (∫ ω, ((target ω : Measure Y).real (interior (K n))) ^ 2 ∂P) ≤ C) :
    (∫⁻ ω, (target ω : Measure Y) (interior (K n)) ∂P) ≤
      ENNReal.ofReal ((C + 1) / 2) := by
  have hm : Measurable (fun ω ↦ (target ω : Measure Y).real (interior (K n))) :=
    ((measurable_measure_open isOpen_interior).comp htarget).ennreal_toReal
  have hb := lintegral_ofReal_le_of_second_moment hm hsq
    (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) hbound
  convert hb using 1
  apply lintegral_congr
  intro ω
  exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top (K.isCompact n).measure_ne_top
    (measure_mono interior_subset))).symm

variable [SecondCountableTopology X] [SecondCountableTopology Y]

omit [SecondCountableTopology X] in
/-- Two original plans sharing the actual target cloud have one tight joint law
as soon as that target cloud has uniform local second moments. -/
theorem isTightMeasureSet_original_twoPlans_target
    {I : Type*} {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (plan₀ plan₁ : ∀ i, Ω i → LocalFiniteMeasure (X × Y))
    (target : ∀ i, Ω i → LocalFiniteMeasure Y)
    (hplan₀ : ∀ i, Measurable (plan₀ i)) (hplan₁ : ∀ i, Measurable (plan₁ i))
    (htarget : ∀ i, Measurable (target i))
    (hdom₀ : ∀ i, ∀ᵐ ω ∂P i, (plan₀ i ω : Measure (X × Y)).snd ≤ (target i ω : Measure Y))
    (hdom₁ : ∀ i, ∀ᵐ ω ∂P i, (plan₁ i ω : Measure (X × Y)).snd ≤ (target i ω : Measure Y))
    (K : CompactExhaustion Y) (C : ℕ → ℝ)
    (hsq : ∀ i n, Integrable (fun ω ↦
      ((target i ω : Measure Y).real (interior (K n))) ^ 2) (P i))
    (hbound : ∀ i n, (∫ ω,
      ((target i ω : Measure Y).real (interior (K n))) ^ 2 ∂P i) ≤ C n) :
    IsTightMeasureSet (range (fun i ↦
      (P i).map (fun ω ↦ (plan₀ i ω, plan₁ i ω, target i ω)))) := by
  have hb : ∀ i n, (∫⁻ ω, (target i ω : Measure Y) (interior (K n)) ∂P i) ≤
      ENNReal.ofReal ((C n + 1) / 2) := fun i n ↦
    lintegral_exhaustionMass_le_of_second_moment (P i) (target i) (htarget i)
      K n (hsq i n) (hbound i n)
  apply isTightMeasureSet_original_triple_of_marginals P plan₀ plan₁ target hplan₀ hplan₁ htarget
  · exact isTightMeasureSet_map_of_dominated_pushforward P plan₀ hplan₀ target
      Prod.snd continuous_snd hdom₀ (CompactExhaustion.choice (X × Y)) K
      _ (fun _ ↦ ENNReal.ofReal_ne_top) hb
  · exact isTightMeasureSet_map_of_dominated_pushforward P plan₁ hplan₁ target
      Prod.snd continuous_snd hdom₁ (CompactExhaustion.choice (X × Y)) K
      _ (fun _ ↦ ENNReal.ofReal_ne_top) hb
  · exact isTightMeasureSet_map_of_integral_exhaustionMass_sq_le P target htarget K C hsq hbound

/-- The two original plans and original target cloud converge along one common
law subsequence, with no separate assumptions on plan local moments. -/
theorem exists_tendsto_subseq_original_twoPlans_target
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (plan₀ plan₁ : ∀ i, Ω i → LocalFiniteMeasure (X × Y))
    (target : ∀ i, Ω i → LocalFiniteMeasure Y)
    (hplan₀ : ∀ i, Measurable (plan₀ i)) (hplan₁ : ∀ i, Measurable (plan₁ i))
    (htarget : ∀ i, Measurable (target i))
    (hdom₀ : ∀ i, ∀ᵐ ω ∂P i, (plan₀ i ω : Measure (X × Y)).snd ≤ (target i ω : Measure Y))
    (hdom₁ : ∀ i, ∀ᵐ ω ∂P i, (plan₁ i ω : Measure (X × Y)).snd ≤ (target i ω : Measure Y))
    (K : CompactExhaustion Y) (C : ℕ → ℝ)
    (hsq : ∀ i n, Integrable (fun ω ↦
      ((target i ω : Measure Y).real (interior (K n))) ^ 2) (P i))
    (hbound : ∀ i n, (∫ ω,
      ((target i ω : Measure Y).real (interior (K n))) ^ 2 ∂P i) ≤ C n) :
    let laws : ℕ → ProbabilityMeasure
        (LocalFiniteMeasure (X × Y) × LocalFiniteMeasure (X × Y) × LocalFiniteMeasure Y) :=
      fun i ↦ ProbabilityMeasure.map (⟨P i, inferInstance⟩ : ProbabilityMeasure (Ω i))
        (f := fun ω ↦ (plan₀ i ω, plan₁ i ω, target i ω))
        ((hplan₀ i).prodMk ((hplan₁ i).prodMk (htarget i))).aemeasurable
    ∃ Q, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (laws ∘ φ) atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_probabilityMeasure_of_isTight
  exact isTightMeasureSet_original_twoPlans_target P plan₀ plan₁ target hplan₀ hplan₁ htarget
    hdom₀ hdom₁ K C hsq hbound

end OTSelector.Probability.LocalFiniteMeasure

end
end
