import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OTSelector.Analysis.Calculus.Whitney.Basic
import OTSelector.Analysis.Calculus.Whitney.Proofs.Cover

/-!
# Smooth Whitney partition from the locally finite cover

Main declarations: exists_whitney_partition.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.Partition`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional real normed domain and nonempty closed K; helper statements expose the actual ball-cover and local-finiteness data they use.
* **Objects:** Actual scaled-bump sum, normalized nonnegative weights, locally finite support, local sum one and reciprocal-radius first derivative mass.
* **Proof detail:** Reduce each locally finite sum to a genuine finite germ. The inner-ball cover gives denominator at least one; quotient differentiation and bounded overlap yield the total derivative estimate.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
  https://www.jirka.org/ra/realanal2.pdf#page=37

**Relationship to the sources:** The ball version of Whitney’s normalized partition (9.2) and scale-controlled derivatives (10.1), with finite-support formalization and explicit denominator bounds.
-/

/-!
# A constructed normalized Whitney partition

The weights are actual scaled bumps divided by their locally finite sum. The inner
ball cover ensures the denominator is at least one; actual differentiation and the
constructed overlap bound control the derivative mass by the reciprocal Whitney scale.
-/

open Set Metric Filter Function
open scoped Topology BigOperators ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Localize the actual doubled support balls to the finite family active at a point.
The resulting neighborhood is an ordinary ambient neighborhood. -/
theorem exists_whitney_support_finset {K C : Set E} (hK : IsClosed K)
    (hLF : LocallyFinite (fun c : C ↦
      {y : ↥(Kᶜ) | (y : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}))
    {x : E} (hx : x ∉ K) :
    ∃ s : Finset C, (∀ c ∈ s, x ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)) ∧
      ∀ᶠ y in 𝓝 x, ∀ c ∉ s, y ∉ closedBall (c : E) (2 * whitneyCoverRadius K c) := by
  classical
  let z : ↥(Kᶜ) := ⟨x, hx⟩
  have hfin := hLF.point_finite z
  refine ⟨hfin.toFinset, fun c hc ↦ hfin.mem_toFinset.mp hc, ?_⟩
  have hev := hLF.eventually_subset (fun c ↦
    isClosed_closedBall.preimage continuous_subtype_val) z
  obtain ⟨U, hU, hsub⟩ := (mem_nhds_subtype Kᶜ z _).mp hev
  filter_upwards [hU, hK.isOpen_compl.mem_nhds hx] with y hy hyK
  intro c hc hball
  apply hc
  apply hfin.mem_toFinset.mpr
  exact hsub (show (⟨y, hyK⟩ : ↥(Kᶜ)) ∈ Subtype.val ⁻¹' U from hy) hball

/-- Sum of the actual radius-scaled bumps selected by a center set. -/
def whitneyBumpSum (K C : Set E) (x : E) : ℝ :=
  ∑ᶠ c : C, whitneyScaledBump (c : E) (whitneyCoverRadius K c) x

/-- Actual normalized bump weights, with zero denominator convention inherited from
real division. The constructed cover makes the denominator positive off the closed set. -/
def whitneyPartitionWeight (K C : Set E) (c : C) (x : E) : ℝ :=
  whitneyScaledBump (c : E) (whitneyCoverRadius K c) x / whitneyBumpSum K C x

private theorem bump_tsupport_subset {K C : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hC : C ⊆ Kᶜ) (c : C) :
    tsupport (whitneyScaledBump (c : E) (whitneyCoverRadius K c)) ⊆
      closedBall (c : E) (2 * whitneyCoverRadius K c) := by
  rw [tsupport, support_whitneyScaledBump (whitneyCoverRadius_pos hK hne (hC c.property))]
  exact closure_minimal ball_subset_closedBall isClosed_closedBall

private theorem weight_tsupport_subset {K C : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hC : C ⊆ Kᶜ) (c : C) :
    tsupport (whitneyPartitionWeight K C c) ⊆
      closedBall (c : E) (2 * whitneyCoverRadius K c) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  apply bump_tsupport_subset hK hne hC c
  apply subset_tsupport
  contrapose! hx
  apply notMem_support.mpr
  have hz := notMem_support.mp hx
  simp only [whitneyPartitionWeight, hz, zero_div]

private theorem bumpSum_local {K C : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hC : C ⊆ Kᶜ)
    (hLF : LocallyFinite (fun c : C ↦
      {y : ↥(Kᶜ) | (y : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}))
    {x : E} (hx : x ∉ K) :
    ∃ s : Finset C,
      (∀ c ∈ s, x ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)) ∧
      (whitneyBumpSum K C =ᶠ[𝓝 x] fun y ↦
        ∑ c ∈ s, whitneyScaledBump (c : E) (whitneyCoverRadius K c) y) ∧
      ∀ᶠ y in 𝓝 x, ∀ c ∉ s,
        whitneyScaledBump (c : E) (whitneyCoverRadius K c) y = 0 := by
  obtain ⟨s, hs, he⟩ := exists_whitney_support_finset hK hLF hx
  have hz : ∀ᶠ y in 𝓝 x, ∀ c ∉ s,
      whitneyScaledBump (c : E) (whitneyCoverRadius K c) y = 0 := by
    filter_upwards [he] with y hy c hc
    apply notMem_support.mp
    exact fun h ↦ hy c hc (bump_tsupport_subset hK hne hC c (subset_tsupport _ h))
  refine ⟨s, hs, ?_, hz⟩
  filter_upwards [hz] with y hy
  apply finsum_eq_sum_of_support_subset
  intro c hc
  by_contra hnot
  exact hc (hy c hnot)

private theorem bumpSum_smooth {K C : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hC : C ⊆ Kᶜ)
    (hLF : LocallyFinite (fun c : C ↦
      {y : ↥(Kᶜ) | (y : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}))
    {x : E} (hx : x ∉ K) : ContDiffAt ℝ ∞ (whitneyBumpSum K C) x := by
  obtain ⟨s, _, he, _⟩ := bumpSum_local hK hne hC hLF hx
  have hh : ContDiffAt ℝ ∞ (fun y ↦
      ∑ c ∈ s, whitneyScaledBump (c : E) (whitneyCoverRadius K c) y) x :=
    ContDiffAt.sum (fun c _ ↦ (contDiff_whitneyScaledBump (c : E) _).contDiffAt)
  exact hh.congr_of_eventuallyEq he

private theorem bumpSum_one_le {K C : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hC : C ⊆ Kᶜ)
    (hcover : Kᶜ ⊆ ⋃ c ∈ C, ball c (whitneyCoverRadius K c))
    (hLF : LocallyFinite (fun c : C ↦
      {y : ↥(Kᶜ) | (y : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}))
    {x : E} (hx : x ∉ K) : 1 ≤ whitneyBumpSum K C x := by
  classical
  obtain ⟨s, _, he, hz⟩ := bumpSum_local hK hne hC hLF hx
  obtain ⟨c, hc, hball⟩ := by simpa only [mem_iUnion] using hcover hx
  let j : C := ⟨c, hc⟩
  have hj : whitneyScaledBump (j : E) (whitneyCoverRadius K j) x = 1 :=
    whitneyScaledBump_eq_one (whitneyCoverRadius_pos hK hne (hC hc))
      (ball_subset_closedBall hball)
  have hjs : j ∈ s := by
    by_contra hn
    have hh := hz.self_of_nhds j hn
    rw [hj] at hh
    exact one_ne_zero hh
  have hsum : whitneyBumpSum K C x =
      ∑ c ∈ s, whitneyScaledBump (c : E) (whitneyCoverRadius K c) x := he.self_of_nhds
  rw [hsum]
  calc
    1 = whitneyScaledBump (j : E) (whitneyCoverRadius K j) x := hj.symm
    _ ≤ _ := Finset.single_le_sum (s := s)
      (f := fun i : C ↦ whitneyScaledBump (i : E) (whitneyCoverRadius K i) x)
      (fun i _ ↦ (whitneyScaledBump_mem_Icc (i : E) _ x).1) hjs

omit [FiniteDimensional ℝ E] in
private theorem norm_fderiv_div_le {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf0 : 0 ≤ f x) (hg0 : 0 < g x) :
    ‖fderiv ℝ (fun y ↦ f y / g y) x‖ ≤
      (f x / (g x) ^ 2) * ‖fderiv ℝ g x‖ + (g x)⁻¹ * ‖fderiv ℝ f x‖ := by
  have hi := (hasDerivAt_inv hg0.ne').comp_hasFDerivAt x hg.hasFDerivAt
  have hd := hf.hasFDerivAt.mul hi
  have heq : fderiv ℝ (fun y ↦ f y / g y) x =
      f x • (-(g x ^ 2)⁻¹ • fderiv ℝ g x) + (g x)⁻¹ • fderiv ℝ f x := by
    have hfun : (fun y ↦ f y / g y) = f * ((fun y ↦ y⁻¹) ∘ g) := by
      funext y
      simp only [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
    rw [hfun]
    exact hd.fderiv
  rw [heq]
  calc
    _ ≤ ‖f x • (-(g x ^ 2)⁻¹ • fderiv ℝ g x)‖ +
        ‖(g x)⁻¹ • fderiv ℝ f x‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf0, abs_neg,
        abs_inv, abs_pow, abs_of_pos hg0, div_eq_mul_inv, mul_assoc]

omit [FiniteDimensional ℝ E] in
private theorem normalized_finite_derivative_mass {ι : Type*} (s : Finset ι)
    (b : ι → E → ℝ) (S : E → ℝ) {x : E}
    (hb : ∀ i ∈ s, DifferentiableAt ℝ (b i) x)
    (hb0 : ∀ i ∈ s, 0 ≤ b i x) (hS : 1 ≤ S x)
    (he : S =ᶠ[𝓝 x] fun y ↦ ∑ i ∈ s, b i y) :
    ∑ i ∈ s, ‖fderiv ℝ (fun y ↦ b i y / S y) x‖ ≤
      2 * ∑ i ∈ s, ‖fderiv ℝ (b i) x‖ := by
  have hS0 : 0 < S x := lt_of_lt_of_le zero_lt_one hS
  have hd0 := HasFDerivAt.fun_sum (fun i hi ↦ (hb i hi).hasFDerivAt)
  have hd := hd0.congr_of_eventuallyEq he
  have hnorm : ‖fderiv ℝ S x‖ ≤ ∑ i ∈ s, ‖fderiv ℝ (b i) x‖ := by
    rw [hd.fderiv]
    exact norm_sum_le _ _
  have hsum : S x = ∑ i ∈ s, b i x := he.self_of_nhds
  calc
    _ ≤ ∑ i ∈ s, (b i x / S x ^ 2 * ‖fderiv ℝ S x‖ +
        (S x)⁻¹ * ‖fderiv ℝ (b i) x‖) :=
      Finset.sum_le_sum fun i hi ↦ norm_fderiv_div_le (hb i hi) hd.differentiableAt
        (hb0 i hi) hS0
    _ = (2 * (S x)⁻¹) * (∑ i ∈ s, ‖fderiv ℝ (b i) x‖) +
        (S x)⁻¹ * (‖fderiv ℝ S x‖ - ∑ i ∈ s, ‖fderiv ℝ (b i) x‖) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        ← Finset.sum_div, ← hsum]
      field_simp
      ring
    _ ≤ (2 * (S x)⁻¹) * (∑ i ∈ s, ‖fderiv ℝ (b i) x‖) := by
      have hn : (S x)⁻¹ *
          (‖fderiv ℝ S x‖ - ∑ i ∈ s, ‖fderiv ℝ (b i) x‖) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hS0.le) (sub_nonpos.mpr hnorm)
      linarith
    _ ≤ _ := by
      have hi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS
      exact mul_le_mul_of_nonneg_right (by linarith)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- A genuine smooth partition off a nonempty closed set, constructed from the Whitney
cover and scaled bumps. Its support geometry and actual derivative mass are conclusions. -/
theorem exists_whitney_partition {K : Set E} (hK : IsClosed K) (hne : K.Nonempty) :
    ∃ (C : Set E) (ψ : C → E → ℝ) (A : ℝ), 0 ≤ A ∧ C ⊆ Kᶜ ∧
      (∀ c, tsupport (ψ c) ⊆ closedBall (c : E) (2 * whitneyCoverRadius K c)) ∧
      LocallyFinite (fun c : C ↦
        {x : ↥(Kᶜ) | (x : E) ∈ closedBall (c : E) (2 * whitneyCoverRadius K c)}) ∧
      ∀ (x : E), x ∉ K →
        (∀ c, 0 ≤ ψ c x) ∧ HasFiniteSupport (fun c ↦ ψ c x) ∧
        (∑ᶠ c, ψ c x) = 1 ∧ (∀ c, ContDiffAt ℝ ∞ (ψ c) x) ∧
        HasFiniteSupport (fun c ↦ fderiv ℝ (ψ c) x) ∧
        (∑ᶠ c, ‖fderiv ℝ (ψ c) x‖) ≤ A / whitneyCoverRadius K x := by
  classical
  obtain ⟨M, C, hC, hcover, _, hLF, hM⟩ := exists_locallyFinite_whitney_cover hK hne
  obtain ⟨C₀, hC₀, hbound⟩ := exists_fderiv_whitneyScaledBump_bound (E := E)
  refine ⟨C, whitneyPartitionWeight K C, 4 * M * C₀, by positivity, hC,
    weight_tsupport_subset hK hne hC, hLF, ?_⟩
  intro x hx
  let b : C → E → ℝ := fun c ↦ whitneyScaledBump (c : E) (whitneyCoverRadius K c)
  let S : E → ℝ := whitneyBumpSum K C
  let ψ : C → E → ℝ := whitneyPartitionWeight K C
  have hS : 1 ≤ S x := bumpSum_one_le hK hne hC hcover hLF hx
  have hS0 : 0 < S x := zero_lt_one.trans_le hS
  have hSsmooth : ContDiffAt ℝ ∞ S x := bumpSum_smooth hK hne hC hLF hx
  have hb (c : C) : ContDiff ℝ ∞ (b c) := contDiff_whitneyScaledBump (c : E) _
  have hb0 (c : C) : 0 ≤ b c x := (whitneyScaledBump_mem_Icc (c : E) _ x).1
  obtain ⟨s, hs, he, hz⟩ := bumpSum_local hK hne hC hLF hx
  have hzero (c : C) (hc : c ∉ s) : ψ c =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [hz] with y hy
    change b c y / S y = 0
    rw [show b c y = 0 from hy c hc, zero_div]
  have hval : support (fun c ↦ ψ c x) ⊆ (s : Set C) := by
    intro c hc
    by_contra hn
    exact hc ((hzero c hn).self_of_nhds)
  have hder : support (fun c ↦ fderiv ℝ (ψ c) x) ⊆ (s : Set C) := by
    intro c hc
    by_contra hn
    have hd := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).congr_of_eventuallyEq (hzero c hn)
    exact hc hd.fderiv
  have hnorm : support (fun c ↦ ‖fderiv ℝ (ψ c) x‖) ⊆ (s : Set C) := by
    intro c hc
    apply hder
    intro hh
    apply hc
    change ‖fderiv ℝ (ψ c) x‖ = 0
    change fderiv ℝ (ψ c) x = 0 at hh
    rw [hh, norm_zero]
  refine ⟨fun c ↦ div_nonneg (hb0 c) hS0.le, s.finite_toSet.subset hval, ?_, ?_,
    s.finite_toSet.subset hder, ?_⟩
  · change (∑ᶠ c, ψ c x) = 1
    rw [finsum_eq_sum_of_support_subset _ hval]
    change (∑ c ∈ s, b c x / S x) = 1
    have hsum : S x = ∑ c ∈ s, b c x := he.self_of_nhds
    rw [← Finset.sum_div, ← hsum, div_self hS0.ne']
  · intro c
    change ContDiffAt ℝ ∞ (fun y ↦ b c y / S y) x
    exact (hb c).contDiffAt.div hSsmooth hS0.ne'
  · change (∑ᶠ c, ‖fderiv ℝ (ψ c) x‖) ≤ (4 * M * C₀) / whitneyCoverRadius K x
    rw [finsum_eq_sum_of_support_subset _ hnorm]
    have hr := whitneyCoverRadius_pos hK hne hx
    have hinc (c : C) (hc : c ∈ s) :
        x ∈ closedBall (c : E) ((5 / 2 : ℝ) * whitneyCoverRadius K c) := by
      have hrc := whitneyCoverRadius_pos hK hne (hC c.property)
      exact (closedBall_subset_closedBall (by linarith)) (hs c hc)
    have hactive := hM x hx
    have hsub : s.image (fun c : C ↦ (c : E)) ⊆ hactive.1.toFinset := by
      intro c hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
      exact hactive.1.mem_toFinset.mpr ⟨z.property, hinc z hz⟩
    have hcard : s.card ≤ M := by
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Subtype.val_injective,
        ← Set.ncard_eq_toFinset_card _ hactive.1] at hh
      exact hh.trans hactive.2
    have hgrad (c : C) (hc : c ∈ s) :
        ‖fderiv ℝ (b c) x‖ ≤ 2 * C₀ / whitneyCoverRadius K x := by
      have hrc := whitneyCoverRadius_pos hK hne (hC c.property)
      have hcomp := (whitneyCoverRadius_comparable (hinc c hc)).1
      calc
        _ ≤ C₀ / whitneyCoverRadius K c := hbound (c : E) _ hrc x
        _ ≤ _ := (div_le_div_iff₀ hrc hr).mpr (by nlinarith)
    have hmass := normalized_finite_derivative_mass s b S
      (fun c _ ↦ (hb c).differentiable (by simp) x) (fun c _ ↦ hb0 c) hS he
    calc
      _ ≤ 2 * ∑ c ∈ s, ‖fderiv ℝ (b c) x‖ := hmass
      _ ≤ 2 * ((s.card : ℝ) * (2 * C₀ / whitneyCoverRadius K x)) := by
        gcongr
        exact (Finset.sum_le_sum hgrad).trans_eq (by simp)
      _ ≤ 2 * ((M : ℝ) * (2 * C₀ / whitneyCoverRadius K x)) := by
        gcongr
      _ = (4 * M * C₀) / whitneyCoverRadius K x := by ring

end OTSelector.Geometry

end
end
