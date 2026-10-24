import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity
import OTSelector.Transport.CyclicMonotonicity.CountableRectangleSupport
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteLegalCycleSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteLegalCycleSupport`; the selected original proof blocks follow. -/
section

/-!
# Probability.CavitySemidiscreteLegalCycleSupport

**Conditions:** The real cost is continuous on an open legal edge domain and source/target bases are countable; every tested exchange keeps all four edges legal.

**Objects:** Countable strict-cycle rectangles inside the legal domain and legal two-cycle monotonicity on support.

**Proof detail:** Shrink all four pair neighborhoods inside the open legal set while preserving a rational strict gap; zero rectangular witnesses contradict positive support masses, and countability combines the almost-sure statements.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6), Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products); [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61), Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (generalization): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Cycle certificates inside the actual legal edge domain

Interleaving marks only require continuity on the open set of legal forward
edges. A strict admissible exchange is detected by countably many rectangles
whose four possible source-target pairings all remain legal.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A strict basis certificate for which every original and exchanged edge is legal. -/
def CavityLegalBasisCycleValid (c : X → Y → ℝ) (D : Set (X × Y))
    {BX : Set (Set X)} {BY : Set (Set Y)} (i : CavityBasisCycleIndex BX BY) : Prop :=
  CavityBasisCycleValid c i ∧ ∀ x ∈ i.1.1.1.val, ∀ y ∈ i.1.1.2.val,
    ∀ x' ∈ i.1.2.1.val, ∀ y' ∈ i.1.2.2.val,
      (x, y) ∈ D ∧ (x', y') ∈ D ∧ (x, y') ∈ D ∧ (x', y) ∈ D

/-- Local continuity on the legal domain suffices to detect each strict legal exchange. -/
theorem exists_cavityLegalBasisCycleIndex_of_strict_cycle
    (c : X → Y → ℝ) (D : Set (X × Y)) (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry c) D)
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (x x' : X) (y y' : Y) (hxy : (x, y) ∈ D) (hxy' : (x', y') ∈ D)
    (hcross : (x, y') ∈ D) (hcross' : (x', y) ∈ D)
    (hbad : c x y' + c x' y < c x y + c x' y') :
    ∃ i : CavityBasisCycleIndex BX BY, CavityLegalBasisCycleValid c D i ∧
      (x, y) ∈ i.1.1.1.val ×ˢ i.1.1.2.val ∧
      (x', y') ∈ i.1.2.1.val ×ˢ i.1.2.2.val := by
  obtain ⟨q, hq, hqgap⟩ := exists_pos_rat_lt
    (show 0 < c x y + c x' y' - c x y' - c x' y by linarith)
  let a := ((x, y), (x', y'))
  let legal : Set ((X × Y) × (X × Y)) :=
    {z | z.1 ∈ D ∧ z.2 ∈ D ∧ (z.1.1, z.2.2) ∈ D ∧ (z.2.1, z.1.2) ∈ D}
  have hlegal : IsOpen legal :=
    (hD.preimage continuous_fst).inter ((hD.preimage continuous_snd).inter
      ((hD.preimage (continuous_fst.fst.prodMk continuous_snd.snd)).inter
        (hD.preimage (continuous_snd.fst.prodMk continuous_fst.snd))))
  have h₀ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.1.1 z.1.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ z.1)
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hxy)) continuous_fst.continuousAt
  have h₁ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.2.1 z.2.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ z.2)
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hxy')) continuous_snd.continuousAt
  have h₂ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.1.1 z.2.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ (z.1.1, z.2.2))
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hcross))
      (continuous_fst.fst.prodMk continuous_snd.snd).continuousAt
  have h₃ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.2.1 z.1.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ (z.2.1, z.1.2))
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hcross'))
      (continuous_snd.fst.prodMk continuous_fst.snd).continuousAt
  have hcont : ContinuousAt (fun z : (X × Y) × (X × Y) ↦
      c z.1.1 z.1.2 + c z.2.1 z.2.2 - c z.1.1 z.2.2 - c z.2.1 z.1.2) a :=
    ((h₀.add h₁).sub h₂).sub h₃
  have hn : {z : (X × Y) × (X × Y) |
      (q : ℝ) < c z.1.1 z.1.2 + c z.2.1 z.2.2 - c z.1.1 z.2.2 - c z.2.1 z.1.2} ∩
        legal ∈ 𝓝 a :=
    inter_mem (hcont.preimage_mem_nhds (Ioi_mem_nhds hqgap))
      (hlegal.mem_nhds ⟨hxy, hxy', hcross, hcross'⟩)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨C, hC, E, hE, hCE⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨A₀, hA₀, hx, hAA⟩ := hBX.mem_nhds_iff.mp hA
  obtain ⟨B₀, hB₀, hy, hBB⟩ := hBY.mem_nhds_iff.mp hB
  obtain ⟨C₀, hC₀, hx', hCC⟩ := hBX.mem_nhds_iff.mp hC
  obtain ⟨E₀, hE₀, hy', hEE⟩ := hBY.mem_nhds_iff.mp hE
  have hall : ∀ a ∈ A₀, ∀ b ∈ B₀, ∀ a' ∈ C₀, ∀ b' ∈ E₀,
      (q : ℝ) < c a b + c a' b' - c a b' - c a' b ∧
      (a, b) ∈ D ∧ (a', b') ∈ D ∧ (a, b') ∈ D ∧ (a', b) ∈ D := by
    intro a ha b hb a' ha' b' hb'
    exact @hUV ((a, b), (a', b'))
      ⟨hAB ⟨hAA ha, hBB hb⟩, hCE ⟨hCC ha', hEE hb'⟩⟩
  refine ⟨(((⟨A₀, hA₀⟩, ⟨B₀, hB₀⟩), (⟨C₀, hC₀⟩, ⟨E₀, hE₀⟩)), q),
    ⟨⟨hq, ?_⟩, ?_⟩, ⟨hx, hy⟩, ⟨hx', hy'⟩⟩
  · intro a ha b hb a' ha' b' hb'
    exact (hall a ha b hb a' ha' b' hb').1.le
  · intro a ha b hb a' ha' b' hb'
    exact (hall a ha b hb a' ha' b' hb').2

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- Zero legal witnesses exclude every strict admissible exchange on the actual
support. Costs outside the legal domain are irrelevant. -/
theorem support_legal_twoCycle_of_basis_witness_zero
    (c : X → Y → ℝ) (D : Set (X × Y)) (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry c) D)
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (π : Measure (X × Y))
    (hzero : ∀ i : CavityBasisCycleIndex BX BY,
      CavityLegalBasisCycleValid c D i → cavityBasisCycleWitness π i = 0) :
    ∀ x y x' y', (x, y) ∈ π.support ∩ D → (x', y') ∈ π.support ∩ D →
      (x, y') ∈ D → (x', y) ∈ D → c x y + c x' y' ≤ c x y' + c x' y := by
  intro x y x' y' hxy hxy' hcross hcross'
  by_contra hle
  obtain ⟨i, hi, hleft, hright⟩ := exists_cavityLegalBasisCycleIndex_of_strict_cycle
    c D hD hc hBX hBY x x' y y' hxy.2 hxy'.2 hcross hcross' (lt_of_not_ge hle)
  have hp := (Measure.mem_support_iff_forall _).mp hxy.1 _
    (((hBX.isOpen i.1.1.1.property).prod (hBY.isOpen i.1.1.2.property)).mem_nhds hleft)
  have hp' := (Measure.mem_support_iff_forall _).mp hxy'.1 _
    (((hBX.isOpen i.1.2.1.property).prod (hBY.isOpen i.1.2.2.property)).mem_nhds hright)
  have hw : 0 < cavityBasisCycleWitness π i := lt_min zero_lt_one (lt_min hp hp')
  exact (ne_of_gt hw) (hzero i hi)

/-- Countably many legal certificates hold on one common probability-one event. -/
theorem ae_legal_twoCycle_support_of_basis_witness_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (π : Ω → Measure (X × Y))
    (c : X → Y → ℝ) (D : Set (X × Y)) (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry c) D)
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (hBXcount : BX.Countable) (hBYcount : BY.Countable)
    (hzero : ∀ i : CavityBasisCycleIndex BX BY, CavityLegalBasisCycleValid c D i →
      ∀ᵐ ω ∂P, cavityBasisCycleWitness (π ω) i = 0) :
    ∀ᵐ ω ∂P, OTSelector.Reconstruction.IsTwoCycleMonotoneOn c D ((π ω).support ∩ D) := by
  let := hBXcount.to_subtype
  let := hBYcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ i : CavityBasisCycleIndex BX BY,
      CavityLegalBasisCycleValid c D i → cavityBasisCycleWitness (π ω) i = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : CavityLegalBasisCycleValid c D i
    · exact (hzero i hi).mono fun _ h _ ↦ h
    · exact Filter.Eventually.of_forall fun _ h ↦ False.elim (hi h)
  exact hall.mono fun ω h ↦ support_legal_twoCycle_of_basis_witness_zero
    c D hD hc hBX hBY (π ω) h

/-- Actual weak convergence transfers vanishing legal rectangle witnesses to legal
monotonicity of the limiting support. No continuity outside the legal domain is used. -/
theorem ae_legal_twoCycle_support_of_weak_witness_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P)) (π : Ω → Measure (X × Y))
    (c : X → Y → ℝ) (D : Set (X × Y)) (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry c) D)
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (hBXcount : BX.Countable) (hBYcount : BY.Countable)
    (heval : ∀ U : Set (X × Y), IsOpen U → LowerSemicontinuous (fun ω ↦ π ω U))
    (hmean : ∀ i : CavityBasisCycleIndex BX BY, CavityLegalBasisCycleValid c D i →
      Tendsto (fun n ↦ ∫⁻ ω, cavityBasisCycleWitness (π ω) i ∂(Pn n : Measure Ω))
        atTop (𝓝 0)) :
    ∀ᵐ ω ∂(P : Measure Ω),
      OTSelector.Reconstruction.IsTwoCycleMonotoneOn c D ((π ω).support ∩ D) := by
  apply ae_legal_twoCycle_support_of_basis_witness_zero
    (P : Measure Ω) π c D hD hc hBX hBY hBXcount hBYcount
  intro i hi
  exact ae_eq_zero_of_lowerSemicontinuous_lintegral_tendsto_zero P Pn hweak _
    (lowerSemicontinuous_cavityBasisCycleWitness hBX hBY π heval i) (hmean i hi)

end OTSelector.Probability

end
end
