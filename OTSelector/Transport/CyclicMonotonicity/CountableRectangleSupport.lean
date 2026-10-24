import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import OTSelector.Probability.WeakClosedConstraint
import OTSelector.Transport.CyclicMonotonicity.CountableTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteCycleSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteCycleSupport`; the selected original proof blocks follow. -/
section

/-!
# Probability.CavitySemidiscreteCycleSupport

**Conditions:** Continuous real cost and countable source/target topological bases; weak-limit versions use lower-semicontinuous open evaluations and vanishing witness expectations.

**Objects:** Rational-gap rectangular strict-cycle certificates and the plan’s two-cycle-monotone support.

**Proof detail:** Continuity enlarges each strict violation to four basis neighborhoods with a positive rational gap; support gives positive mass to both rectangles, contradicting their zero witness, and countability places all certificates on one full event.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6), Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products); [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61), Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144), Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (composition): This countable certificate and weak-limit combination is local. Portmanteau/open evaluation and nonnegative-integral zero principles are the classical foundations; the result is two-cycle monotonicity, not a claim that every such support solves arbitrary OT.
-/

/-!
# Countable rectangular certificates for two-cycle violations

Every strict violation of a continuous cost is detected by two rectangles from
fixed topological bases and a positive rational gap. Vanishing actual rectangle
mass witnesses therefore forces two-cycle monotonicity on the plan's support.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Two basis rectangles together with a rational cost gap. -/
abbrev CavityBasisCycleIndex (BX : Set (Set X)) (BY : Set (Set Y)) :=
  ((BX × BY) × (BX × BY)) × ℚ

/-- The two rectangles have the indicated strictly positive cost improvement. -/
def CavityBasisCycleValid (c : X → Y → ℝ) {BX : Set (Set X)} {BY : Set (Set Y)}
    (i : CavityBasisCycleIndex BX BY) : Prop :=
  0 < i.2 ∧ ∀ x ∈ i.1.1.1.val, ∀ y ∈ i.1.1.2.val,
    ∀ x' ∈ i.1.2.1.val, ∀ y' ∈ i.1.2.2.val,
    (i.2 : ℝ) ≤ c x y + c x' y' - c x y' - c x' y

/-- Continuity produces a basis-rectangle certificate for every strict cycle violation. -/
theorem exists_cavityBasisCycleIndex_of_strict_cycle
    (c : X → Y → ℝ) (hc : Continuous (Function.uncurry c))
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (x x' : X) (y y' : Y) (hbad : c x y' + c x' y < c x y + c x' y') :
    ∃ i : CavityBasisCycleIndex BX BY, CavityBasisCycleValid c i ∧
      (x, y) ∈ i.1.1.1.val ×ˢ i.1.1.2.val ∧
      (x', y') ∈ i.1.2.1.val ×ˢ i.1.2.2.val := by
  obtain ⟨q, hq, hqgap⟩ := exists_pos_rat_lt (show 0 < c x y + c x' y' - c x y' - c x' y by
    linarith)
  have hcont : Continuous (fun z : (X × Y) × (X × Y) ↦
      c z.1.1 z.1.2 + c z.2.1 z.2.2 - c z.1.1 z.2.2 - c z.2.1 z.1.2) :=
    (((hc.comp continuous_fst).add (hc.comp continuous_snd)).sub
      (hc.comp (continuous_fst.fst.prodMk continuous_snd.snd))).sub
      (hc.comp (continuous_snd.fst.prodMk continuous_fst.snd))
  have hn : {z : (X × Y) × (X × Y) |
      (q : ℝ) < c z.1.1 z.1.2 + c z.2.1 z.2.2 - c z.1.1 z.2.2 - c z.2.1 z.1.2} ∈
      𝓝 ((x, y), (x', y')) := (isOpen_lt continuous_const hcont).mem_nhds hqgap
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨C, hC, D, hD, hCD⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨A₀, hA₀, hx, hAA⟩ := hBX.mem_nhds_iff.mp hA
  obtain ⟨B₀, hB₀, hy, hBB⟩ := hBY.mem_nhds_iff.mp hB
  obtain ⟨C₀, hC₀, hx', hCC⟩ := hBX.mem_nhds_iff.mp hC
  obtain ⟨D₀, hD₀, hy', hDD⟩ := hBY.mem_nhds_iff.mp hD
  refine ⟨(((⟨A₀, hA₀⟩, ⟨B₀, hB₀⟩), (⟨C₀, hC₀⟩, ⟨D₀, hD₀⟩)), q),
    ⟨hq, ?_⟩, ⟨hx, hy⟩, ⟨hx', hy'⟩⟩
  intro a ha b hb a' ha' b' hb'
  have hu : (a, b) ∈ U := hAB ⟨hAA ha, hBB hb⟩
  have hv : (a', b') ∈ V := hCD ⟨hCC ha', hDD hb'⟩
  exact le_of_lt (hUV (show ((a, b), (a', b')) ∈ U ×ˢ V from ⟨hu, hv⟩))

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- A nonempty positive-gap certificate automatically has disjoint source and target
sets; no separation assumption is needed to extract the certificates. -/
theorem CavityBasisCycleValid.disjoint
    {c : X → Y → ℝ} {BX : Set (Set X)} {BY : Set (Set Y)}
    {i : CavityBasisCycleIndex BX BY} (hi : CavityBasisCycleValid c i)
    (hleft : (i.1.1.1.val ×ˢ i.1.1.2.val).Nonempty)
    (hright : (i.1.2.1.val ×ˢ i.1.2.2.val).Nonempty) :
    Disjoint i.1.1.1.val i.1.2.1.val ∧ Disjoint i.1.1.2.val i.1.2.2.val := by
  obtain ⟨⟨x, y⟩, hx, hy⟩ := hleft
  obtain ⟨⟨x', y'⟩, hx', hy'⟩ := hright
  have hq : (0 : ℝ) < i.2 := by exact_mod_cast hi.1
  constructor
  · apply Set.disjoint_left.mpr
    intro a ha ha'
    have h := hi.2 a ha y hy a ha' y' hy'
    linarith
  · apply Set.disjoint_left.mpr
    intro b hb hb'
    have h := hi.2 x hx b hb x' hx' b hb'
    linarith

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- The actual bounded plan-mass witness associated with a basis certificate. -/
def cavityBasisCycleWitness {BX : Set (Set X)} {BY : Set (Set Y)}
    (π : Measure (X × Y)) (i : CavityBasisCycleIndex BX BY) : ℝ≥0∞ :=
  min 1 (min (π (i.1.1.1.val ×ˢ i.1.1.2.val)) (π (i.1.2.1.val ×ˢ i.1.2.2.val)))

/-- Vanishing valid basis witnesses implies monotonicity on the entire actual support. -/
theorem isTwoCycleMonotone_support_of_basis_witness_zero
    (c : X → Y → ℝ) (hc : Continuous (Function.uncurry c))
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (π : Measure (X × Y))
    (hzero : ∀ i : CavityBasisCycleIndex BX BY,
      CavityBasisCycleValid c i → cavityBasisCycleWitness π i = 0) :
    OTSelector.Reconstruction.IsTwoCycleMonotone c π.support := by
  intro x y x' y' hxy hxy'
  by_contra hle
  obtain ⟨i, hi, hleft, hright⟩ := exists_cavityBasisCycleIndex_of_strict_cycle
    c hc hBX hBY x x' y y' (lt_of_not_ge hle)
  have hp := (Measure.mem_support_iff_forall _).mp hxy _
    (((hBX.isOpen i.1.1.1.property).prod (hBY.isOpen i.1.1.2.property)).mem_nhds hleft)
  have hp' := (Measure.mem_support_iff_forall _).mp hxy' _
    (((hBX.isOpen i.1.2.1.property).prod (hBY.isOpen i.1.2.2.property)).mem_nhds hright)
  have hw : 0 < cavityBasisCycleWitness π i := lt_min zero_lt_one (lt_min hp hp')
  exact (ne_of_gt hw) (hzero i hi)

/-- Countability moves every individual zero-witness event onto one probability-one
set, so all strict support violations are excluded simultaneously. -/
theorem ae_isTwoCycleMonotone_support_of_basis_witness_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (π : Ω → Measure (X × Y))
    (c : X → Y → ℝ) (hc : Continuous (Function.uncurry c))
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (hBXcount : BX.Countable) (hBYcount : BY.Countable)
    (hzero : ∀ i : CavityBasisCycleIndex BX BY, CavityBasisCycleValid c i →
      ∀ᵐ ω ∂P, cavityBasisCycleWitness (π ω) i = 0) :
    ∀ᵐ ω ∂P, OTSelector.Reconstruction.IsTwoCycleMonotone c (π ω).support := by
  let := hBXcount.to_subtype
  let := hBYcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ i : CavityBasisCycleIndex BX BY,
      CavityBasisCycleValid c i → cavityBasisCycleWitness (π ω) i = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : CavityBasisCycleValid c i
    · exact (hzero i hi).mono fun _ h _ ↦ h
    · exact Filter.Eventually.of_forall fun _ h ↦ False.elim (hi h)
  exact hall.mono fun ω h ↦ isTwoCycleMonotone_support_of_basis_witness_zero
    c hc hBX hBY (π ω) h

section SceneLimit

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- A nonnegative lower-semicontinuous witness with vanishing expectations is zero
almost surely under every actual weak limit of the probability laws. -/
theorem ae_eq_zero_of_lowerSemicontinuous_lintegral_tendsto_zero
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P)) (W : Ω → ℝ≥0∞)
    (hW : LowerSemicontinuous W)
    (hmean : Tendsto (fun n ↦ ∫⁻ ω, W ω ∂(Pn n : Measure Ω)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂(P : Measure Ω), W ω = 0 := by
  have hopen (r : ℝ≥0∞) (hr : 0 < r) (hrt : r ≠ ⊤) :
      (P : Measure Ω) {ω | r < W ω} = 0 := by
    have hb (n : ℕ) : (Pn n : Measure Ω) {ω | r < W ω} ≤
        (∫⁻ ω, W ω ∂(Pn n : Measure Ω)) / r :=
      (measure_mono (show {ω | r < W ω} ⊆ {ω | r ≤ W ω} from fun ω h ↦ le_of_lt (show r < W ω from h))).trans
        (meas_ge_le_lintegral_div hW.measurable.aemeasurable (ne_of_gt hr) hrt)
    have hdiv : Tendsto (fun n ↦ (∫⁻ ω, W ω ∂(Pn n : Measure Ω)) / r)
        atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [ENNReal.zero_div] using
        ENNReal.Tendsto.div_const hmean (Or.inr (ne_of_gt hr))
    exact le_antisymm
      (OTSelector.Probability.measure_open_le_of_tendsto_bounds P Pn hweak _
        (hW.isOpen_preimage r) _ 0 hdiv hb) bot_le
  have hzero : ∀ᵐ ω ∂(P : Measure Ω), W ω ≤ 0 := by
    apply (ae_le_const_iff_forall_gt_measure_zero W 0).mpr
    intro b hb
    obtain ⟨q, _, hq0, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hb
    have hs : {ω | b ≤ W ω} ⊆ {ω | ((q : ℝ).toNNReal : ℝ≥0∞) < W ω} :=
      fun _ h ↦ hqb.trans_le h
    exact measure_mono_null hs (hopen _ hq0 ENNReal.coe_ne_top)
  exact hzero.mono fun _ h ↦ le_antisymm h bot_le

omit [MeasurableSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] in
/-- Open-set evaluation makes the actual bounded mass witness lower semicontinuous. -/
theorem lowerSemicontinuous_cavityBasisCycleWitness
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (π : Ω → Measure (X × Y))
    (heval : ∀ U : Set (X × Y), IsOpen U → LowerSemicontinuous (fun ω ↦ π ω U))
    (i : CavityBasisCycleIndex BX BY) :
    LowerSemicontinuous (fun ω ↦ cavityBasisCycleWitness (π ω) i) := by
  exact lowerSemicontinuous_const.inf
    ((heval _ ((hBX.isOpen i.1.1.1.property).prod (hBY.isOpen i.1.1.2.property))).inf
      (heval _ ((hBX.isOpen i.1.2.1.property).prod (hBY.isOpen i.1.2.2.property))))

/-- Countably many vanishing finite-environment witnesses pass through weak convergence
and force the limiting actual plan's support to be two-cycle monotone. -/
theorem ae_isTwoCycleMonotone_support_of_weak_witness_tendsto_zero
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P)) (π : Ω → Measure (X × Y))
    (c : X → Y → ℝ) (hc : Continuous (Function.uncurry c))
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (hBXcount : BX.Countable) (hBYcount : BY.Countable)
    (heval : ∀ U : Set (X × Y), IsOpen U → LowerSemicontinuous (fun ω ↦ π ω U))
    (hmean : ∀ i : CavityBasisCycleIndex BX BY, CavityBasisCycleValid c i →
      Tendsto (fun n ↦ ∫⁻ ω, cavityBasisCycleWitness (π ω) i ∂(Pn n : Measure Ω))
        atTop (𝓝 0)) :
    ∀ᵐ ω ∂(P : Measure Ω),
      OTSelector.Reconstruction.IsTwoCycleMonotone c (π ω).support := by
  apply ae_isTwoCycleMonotone_support_of_basis_witness_zero
    (P : Measure Ω) π c hc hBX hBY hBXcount hBYcount
  intro i hi
  exact ae_eq_zero_of_lowerSemicontinuous_lintegral_tendsto_zero P Pn hweak _
    (lowerSemicontinuous_cavityBasisCycleWitness hBX hBY π heval i) (hmean i hi)

end SceneLimit
end OTSelector.Probability


end
end
