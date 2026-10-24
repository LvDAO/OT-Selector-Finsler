import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.Transport.Coupling.FiniteClockMixture
import OTSelector.Transport.Coupling.LabelClockCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawCalibratedPopulation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawCalibratedPopulation`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawCalibratedPopulation

**Conditions:** An injective original label-clock chart with measurable inverse, exact original marginal data and a forward same-label class coupling.

**Objects:** A rebuilt calibrated coupling of the unchanged original populations and every residual subplan below it.

**Proof detail:** Lift the class coupling through the same measured inverse on both endpoints; exact marginals recover the original populations, forward same-label geometry gives calibration, and pushforward preserves submeasure order and total mass.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30), Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20; [OTSelector project, Measurable forward weighted Hall construction](main.tex#measurable-forward-hall), main.tex label measurable-forward-hall, line 6889.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Rebuilt deterministic class couplings preserve the original calibrated population

A measurable inverse of the original injective label-clock coordinates transports
any forward common-label coupling of the unchanged marginals back to original
physical points. Every deterministic residual submeasure stays below this new
whole calibrated coupling, without any sampled orphan independence premise.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Every forward same-label coupling of the exact original label-clock laws
lifts to a calibrated coupling of the unchanged original physical marginals.
The same measurable map transports every residual submeasure and preserves raw mass. -/
theorem exists_original_calibrated_coupling_of_labelClock
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]
    [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)))
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure M) (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (Λ : Measure ((Z × ℝ) × (Z × ℝ)))
    (hΛ : Vlasov.IsCoupling Λ (μ.map (fun x ↦ (a x, u x)))
      (ν.map (fun y ↦ (a y, u y))))
    (hforward : ∀ᵐ p ∂Λ, p.1.1 = p.2.1 ∧ p.1.2 ≤ p.2.2) :
    ∃ b : Z × ℝ → M, Measurable b ∧
      Vlasov.IsCoupling (Λ.map (Prod.map b b)) μ ν ∧
      (∀ᵐ p ∂Λ.map (Prod.map b b), u p.2 - u p.1 = dist p.1 p.2) ∧
      ∀ ξ : Measure ((Z × ℝ) × (Z × ℝ)), ξ ≤ Λ →
        ξ.map (Prod.map b b) ≤ Λ.map (Prod.map b b) ∧
        ξ.map (Prod.map b b) Set.univ = ξ Set.univ := by
  obtain ⟨b, hb, hi, _⟩ := exists_measurable_labelClock_inverse hN ha hu hinj
  let c : M → Z × ℝ := fun x ↦ (a x, u x)
  have hc : Measurable c := ha.prodMk hu
  have hμback : (μ.map c).map b = μ := by
    rw [Measure.map_map hb hc]
    calc
      μ.map (b ∘ c) = μ.map id := Measure.map_congr (hμN.mono fun x hx ↦ hi x hx)
      _ = μ := Measure.map_id
  have hνback : (ν.map c).map b = ν := by
    rw [Measure.map_map hb hc]
    calc
      ν.map (b ∘ c) = ν.map id := Measure.map_congr (hνN.mono fun x hx ↦ hi x hx)
      _ = ν := Measure.map_id
  have hphysical : Vlasov.IsCoupling (Λ.map (Prod.map b b)) μ ν := by
    have h := hΛ.map b b hb hb
    change Vlasov.IsCoupling (Λ.map (Prod.map b b)) ((μ.map c).map b) ((ν.map c).map b) at h
    rwa [hμback, hνback] at h
  have hMeas : MeasurableSet {z : Z × ℝ | b z ∈ N ∧ c (b z) = z} := by
    convert (hb hN).inter ((measurableSet_eq_fun (ha.comp hb) measurable_fst).inter
      (measurableSet_eq_fun (hu.comp hb) measurable_snd)) using 1
    ext z
    rcases z with ⟨z, t⟩
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Function.comp_apply, c, Prod.mk.injEq]
  have hclockμ : ∀ᵐ z ∂μ.map c, b z ∈ N ∧ c (b z) = z := by
    apply (ae_map_iff hc.aemeasurable hMeas).mpr
    filter_upwards [hμN] with x hx
    change b (a x, u x) ∈ N ∧ c (b (a x, u x)) = c x
    rw [hi x hx]
    exact ⟨hx, rfl⟩
  have hclockν : ∀ᵐ z ∂ν.map c, b z ∈ N ∧ c (b z) = z := by
    apply (ae_map_iff hc.aemeasurable hMeas).mpr
    filter_upwards [hνN] with x hx
    change b (a x, u x) ∈ N ∧ c (b (a x, u x)) = c x
    rw [hi x hx]
    exact ⟨hx, rfl⟩
  have hleft : ∀ᵐ p ∂Λ, b p.1 ∈ N ∧ c (b p.1) = p.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (hΛ.1.symm ▸ hclockμ)
  have hright : ∀ᵐ p ∂Λ, b p.2 ∈ N ∧ c (b p.2) = p.2 :=
    ae_of_ae_map measurable_snd.aemeasurable (hΛ.2.symm ▸ hclockν)
  refine ⟨b, hb, hphysical, ?_, ?_⟩
  · apply (ae_map_iff (hb.prodMap hb).aemeasurable
      (measurableSet_eq_fun ((hu.comp measurable_snd).sub (hu.comp measurable_fst))
        (continuous_fst.dist continuous_snd).measurable)).mpr
    filter_upwards [hleft, hright, hforward] with p hx hy hf
    apply (horder (b p.1) hx.1 (b p.2) hy.1).mp
    have hax : a (b p.1) = p.1.1 := congrArg Prod.fst hx.2
    have hay : a (b p.2) = p.2.1 := congrArg Prod.fst hy.2
    have hux : u (b p.1) = p.1.2 := congrArg Prod.snd hx.2
    have huy : u (b p.2) = p.2.2 := congrArg Prod.snd hy.2
    exact ⟨hax.trans (hf.1.trans hay.symm), by simpa only [hux, huy] using hf.2⟩
  · intro ξ hξ
    exact ⟨Measure.map_mono hξ (hb.prodMap hb),
      by rw [Measure.map_apply (hb.prodMap hb) MeasurableSet.univ, Set.preimage_univ]⟩

/-- A measurable finite legal class flow and the actual within-bin laws give a
new whole original calibrated coupling. All original sampled marginals remain
unchanged, and every deterministic residual remains an actual submeasure. -/
theorem exists_original_calibrated_coupling_of_classFlow
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    {I J : Type*} [Fintype I] [Fintype J]
    {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)))
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure M) (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (r : Measure Z) [SFinite r]
    (P : Z → I → J → ℝ) (asrc : Z → I → ℝ) (btgt : Z → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hma : ∀ i, Measurable (fun z ↦ asrc z i))
    (hmb : ∀ j, Measurable (fun z ↦ btgt z j))
    (α : I → Kernel Z ℝ) (β : J → Kernel Z ℝ)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂r, ∀ i j, 0 ≤ P z i j)
    (hrow : ∀ᵐ z ∂r, ∀ i, ∑ j, P z i j = asrc z i)
    (hcol : ∀ᵐ z ∂r, ∀ j, ∑ i, P z i j = btgt z j)
    (hsource : r ⊗ₘ finiteClassMarginalKernel asrc α = μ.map (fun x ↦ (a x, u x)))
    (htarget : r ⊗ₘ finiteClassMarginalKernel btgt β = ν.map (fun y ↦ (a y, u y)))
    (allowed : I → J → Prop)
    (hzero : ∀ᵐ z ∂r, ∀ i j, ¬ allowed i j → P z i j = 0)
    (hbinlegal : ∀ᵐ z ∂r, ∀ i j, allowed i j →
      ∀ᵐ p ∂(α i z).prod (β j z), p.1 ≤ p.2) :
    ∃ b : Z × ℝ → M, Measurable b ∧
      Vlasov.IsCoupling ((sameLabelPopulationCoupling r P α β).map (Prod.map b b)) μ ν ∧
      (∀ᵐ p ∂(sameLabelPopulationCoupling r P α β).map (Prod.map b b),
        u p.2 - u p.1 = dist p.1 p.2) ∧
      ∀ ξ : Measure ((Z × ℝ) × (Z × ℝ)), ξ ≤ sameLabelPopulationCoupling r P α β →
        ξ.map (Prod.map b b) ≤ (sameLabelPopulationCoupling r P α β).map (Prod.map b b) ∧
        ξ.map (Prod.map b b) Set.univ = ξ Set.univ := by
  have hcoupling : Vlasov.IsCoupling (sameLabelPopulationCoupling r P α β)
      (μ.map (fun x ↦ (a x, u x))) (ν.map (fun y ↦ (a y, u y))) := by
    constructor
    · rw [sameLabelPopulationCoupling_fst r P asrc hmP hma α β hP hrow, hsource]
    · rw [sameLabelPopulationCoupling_snd r P btgt hmP hmb α β hP hcol, htarget]
  have hforward : ∀ᵐ p ∂sameLabelPopulationCoupling r P α β,
      p.1.1 = p.2.1 ∧ p.1.2 ≤ p.2.2 := by
    have hlegal := sameLabelPopulationCoupling_ae_legal r P hmP α β allowed
      (fun _ p ↦ p.1 ≤ p.2)
      (measurableSet_le (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd)) hzero hbinlegal
    filter_upwards [sameLabelPopulationCoupling_ae_commonLabel r P α β, hlegal] with p hc hl
    exact ⟨hc, hl⟩
  exact exists_original_calibrated_coupling_of_labelClock hN ha hu hinj horder
    μ ν hμN hνN _ hcoupling hforward

/-- The explicit continuous residual class kernel gives an actual deterministic
original physical subplan with its quantitative raw-mass bound. This discharges
the subplan premise used by original-sample small-mass energy recovery. -/
theorem original_classFlow_residual_subplan
    {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
    {I J : Type*} [Fintype I] [Fintype J]
    (r : Measure Z) [SFinite r] (P Q : Z → I → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (α : I → Kernel Z ℝ) (β : J → Kernel Z ℝ)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂r, ∀ i j, 0 ≤ P z i j)
    (hQ : ∀ᵐ z ∂r, ∀ i j, 0 ≤ Q z i j)
    (B : ℝ) (hB : ∀ᵐ z ∂r, (∑ i, ∑ j, Q z i j) ≤ B)
    (b : Z × ℝ → M) (hb : Measurable b) :
    ((sameLabelPopulationCoupling r Q α β).map (Prod.map b b) ≤
      (sameLabelPopulationCoupling r (fun z i j ↦ P z i j + Q z i j) α β).map (Prod.map b b)) ∧
    ((sameLabelPopulationCoupling r Q α β).map (Prod.map b b) univ ≤
      ENNReal.ofReal B * r univ) := by
  refine ⟨Measure.map_mono
    (sameLabelPopulationCoupling_residual_le_ae r P Q hmP hmQ α β hP hQ)
    (hb.prodMap hb), ?_⟩
  rw [Measure.map_apply (hb.prodMap hb) MeasurableSet.univ, Set.preimage_univ]
  exact sameLabelPopulationCoupling_mass_le r Q hmQ α β hQ B hB

/-- The original calibrated coupling construction only needs within-bin legality
on positive class-flow entries. Arbitrary zero-bin Markov fallbacks are allowed. -/
theorem exists_original_calibrated_coupling_of_positive_classFlow
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    {I J : Type*} [Fintype I] [Fintype J]
    {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)))
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure M) (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (r : Measure Z) [SFinite r]
    (P : Z → I → J → ℝ) (asrc : Z → I → ℝ) (btgt : Z → J → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hma : ∀ i, Measurable (fun z ↦ asrc z i))
    (hmb : ∀ j, Measurable (fun z ↦ btgt z j))
    (α : I → Kernel Z ℝ) (β : J → Kernel Z ℝ)
    [∀ i, IsMarkovKernel (α i)] [∀ j, IsMarkovKernel (β j)]
    (hP : ∀ᵐ z ∂r, ∀ i j, 0 ≤ P z i j)
    (hrow : ∀ᵐ z ∂r, ∀ i, ∑ j, P z i j = asrc z i)
    (hcol : ∀ᵐ z ∂r, ∀ j, ∑ i, P z i j = btgt z j)
    (hsource : r ⊗ₘ finiteClassMarginalKernel asrc α = μ.map (fun x ↦ (a x, u x)))
    (htarget : r ⊗ₘ finiteClassMarginalKernel btgt β = ν.map (fun y ↦ (a y, u y)))
    (hbinlegal : ∀ᵐ z ∂r, ∀ i j, 0 < P z i j →
      ∀ᵐ p ∂(α i z).prod (β j z), p.1 ≤ p.2) :
    ∃ b : Z × ℝ → M, Measurable b ∧
      Vlasov.IsCoupling ((sameLabelPopulationCoupling r P α β).map (Prod.map b b)) μ ν ∧
      (∀ᵐ p ∂(sameLabelPopulationCoupling r P α β).map (Prod.map b b),
        u p.2 - u p.1 = dist p.1 p.2) ∧
      ∀ ξ : Measure ((Z × ℝ) × (Z × ℝ)), ξ ≤ sameLabelPopulationCoupling r P α β →
        ξ.map (Prod.map b b) ≤ (sameLabelPopulationCoupling r P α β).map (Prod.map b b) ∧
        ξ.map (Prod.map b b) Set.univ = ξ Set.univ := by
  have hcoupling : Vlasov.IsCoupling (sameLabelPopulationCoupling r P α β)
      (μ.map (fun x ↦ (a x, u x))) (ν.map (fun y ↦ (a y, u y))) := by
    constructor
    · rw [sameLabelPopulationCoupling_fst r P asrc hmP hma α β hP hrow, hsource]
    · rw [sameLabelPopulationCoupling_snd r P btgt hmP hmb α β hP hcol, htarget]
  have hforward : ∀ᵐ p ∂sameLabelPopulationCoupling r P α β,
      p.1.1 = p.2.1 ∧ p.1.2 ≤ p.2.2 := by
    have hlegal := sameLabelPopulationCoupling_ae_legal_of_pos r P hmP α β
      (fun _ p ↦ p.1 ≤ p.2)
      (measurableSet_le (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd)) hbinlegal
    filter_upwards [sameLabelPopulationCoupling_ae_commonLabel r P α β, hlegal] with p hc hl
    exact ⟨hc, hl⟩
  exact exists_original_calibrated_coupling_of_labelClock hN ha hu hinj horder
    μ ν hμN hνN _ hcoupling hforward

end OTSelector.Reconstruction

end
end
