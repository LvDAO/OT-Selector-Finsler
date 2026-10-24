import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.Linarith

/-!
# Transport.CyclicMonotonicity.CountableTargetRigidity

## Lemma skeleton

* **Conditions:** A countable target, measurable pairwise cost differences with atomless pushforward laws, and a common measurable two-cycle monotone relation. Plan equality also assumes the same source marginal and carrying by that relation.

* **Objects:** Almost-sure single-valuedness and equality of two carried plans, without finite-mass assumptions.

* **Proof detail:** For each target pair, monotonicity forces any shared source fiber onto at most one cost-difference level; atomlessness makes that level null. Remove countably many exceptional sets. Determine every source-set×target-singleton mass from the common source marginal and sum over the countable target.

## Mathematical sources

- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.
- [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254): Appendix A.1, Theorem A.5, p. 242.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106): Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.

Source relation (composition): A locally proved countable-target rigidity criterion, not an assertion that arbitrary transport optimal faces are singletons. The countable-target determination avoids unjustified probability normalization.
-/

/-!
# Rigidity of countable-target two-cycle monotone plans

Atomless pairwise cost differences make a two-cycle monotone relation
single-valued outside a source-null set. Two plans carried by that relation
and having the same source marginal are therefore equal. Neither the source
measure nor the plans need have finite mass, so the result also applies to
stationary local limits with Lebesgue source marginal.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {S J : Type*} [MeasurableSpace S] [Countable J]

/-- The two-cycle inequality on a common source-target relation. -/
def IsTwoCycleMonotone (c : S → J → ℝ) (Γ : Set (S × J)) : Prop :=
  ∀ x i y j, (x, i) ∈ Γ → (y, j) ∈ Γ →
    c x i + c y j ≤ c x j + c y i

/-- Pairwise atomless cost differences rule out two target labels over almost
every source point of a two-cycle monotone relation. -/
theorem IsTwoCycleMonotone.ae_single_valued
    {c : S → J → ℝ} {Γ : Set (S × J)} {μ : Measure S}
    (hΓ : IsTwoCycleMonotone c Γ)
    (hc : ∀ j, Measurable (fun x ↦ c x j))
    (hatom : ∀ i j, i ≠ j →
      NullSingletonClass (μ.map (fun x ↦ c x i - c x j))) :
    ∀ᵐ x ∂μ, ∀ i j, (x, i) ∈ Γ → (x, j) ∈ Γ → i = j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ _ _ ↦ hij)
  by_cases hex : ∃ x, (x, i) ∈ Γ ∧ (x, j) ∈ Γ
  · obtain ⟨x₀, hi₀, hj₀⟩ := hex
    let _ := hatom i j hij
    have hnull : μ {x | c x i - c x j = c x₀ i - c x₀ j} = 0 := by
      have hm : Measurable (fun x ↦ c x i - c x j) := (hc i).sub (hc j)
      have h := measure_singleton (μ := μ.map (fun x ↦ c x i - c x j))
        (c x₀ i - c x₀ j)
      rw [Measure.map_apply hm (measurableSet_singleton _)] at h
      exact h
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxi hxj
    have h₁ := hΓ x i x₀ j hxi hj₀
    have h₂ := hΓ x₀ i x j hi₀ hxj
    exact False.elim (hx (by linarith))
  · exact Filter.Eventually.of_forall (fun x hxi hxj ↦
      False.elim (hex ⟨x, hxi, hxj⟩))

section MeasurableTargets

variable [MeasurableSpace J] [MeasurableSingletonClass J]

omit [Countable J] [MeasurableSingletonClass J] in
/-- Each target slice of a plan carried by an almost-everywhere single-valued
relation is determined by its source marginal, including for infinite measures. -/
theorem measure_prod_singleton_of_ae_single_valued
    {Γ : Set (S × J)} (hΓ : MeasurableSet Γ) {μ : Measure S}
    (hsingle : ∀ᵐ x ∂μ, ∀ i j, (x, i) ∈ Γ → (x, j) ∈ Γ → i = j)
    {π : Measure (S × J)} (hsource : π.map Prod.fst = μ)
    (hcarried : ∀ᵐ z ∂π, z ∈ Γ) {B : Set S} (hB : MeasurableSet B) (j : J) :
    π (B ×ˢ {j}) = μ (B ∩ {x | (x, j) ∈ Γ}) := by
  have hslice : MeasurableSet {x | (x, j) ∈ Γ} :=
    (measurable_id.prodMk measurable_const) hΓ
  have hsingleπ : ∀ᵐ z ∂π, ∀ i j, (z.1, i) ∈ Γ → (z.1, j) ∈ Γ → i = j :=
    ae_of_ae_map measurable_fst.aemeasurable (hsource.symm ▸ hsingle)
  rw [← hsource, Measure.map_apply measurable_fst (hB.inter hslice)]
  apply measure_congr
  filter_upwards [hcarried, hsingleπ] with z hz hs
  change (z.1 ∈ B ∧ z.2 ∈ ({j} : Set J)) =
    (z.1 ∈ B ∧ (z.1, j) ∈ Γ)
  apply propext
  constructor
  · rintro ⟨hb, hj⟩
    exact ⟨hb, (mem_singleton_iff.mp hj) ▸ hz⟩
  · rintro ⟨hb, hj⟩
    exact ⟨hb, hs z.2 j hz hj⟩

/-- Countably many target slices determine the whole plan. No finite-mass
assumption or selected Monge map is required. -/
theorem measure_eq_of_common_ae_single_valued_relation
    {Γ : Set (S × J)} (hΓ : MeasurableSet Γ) {μ : Measure S}
    (hsingle : ∀ᵐ x ∂μ, ∀ i j, (x, i) ∈ Γ → (x, j) ∈ Γ → i = j)
    {π₀ π₁ : Measure (S × J)}
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (hcarried₀ : ∀ᵐ z ∂π₀, z ∈ Γ) (hcarried₁ : ∀ᵐ z ∂π₁, z ∈ Γ) :
    π₀ = π₁ := by
  apply Measure.ext
  intro U hU
  let slice : J → Set S := fun j ↦ {x | (x, j) ∈ U}
  have hm : ∀ j, MeasurableSet (slice j) := fun j ↦
    (measurable_id.prodMk measurable_const) hU
  have hdecomp : U = ⋃ j, slice j ×ˢ {j} := by
    ext z
    simp only [mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨z.2, hz, rfl⟩
    · rintro ⟨j, hj, hzj⟩
      change (z.1, j) ∈ U at hj
      simpa only [← hzj, Prod.eta] using hj
  have hdis : Pairwise (fun i j ↦ Disjoint (slice i ×ˢ {i}) (slice j ×ˢ {j})) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact hij ((mem_singleton_iff.mp hi.2).symm.trans (mem_singleton_iff.mp hj.2))
  rw [hdecomp, measure_iUnion hdis (fun j ↦ (hm j).prod (measurableSet_singleton j)),
    measure_iUnion hdis (fun j ↦ (hm j).prod (measurableSet_singleton j))]
  apply tsum_congr
  intro j
  rw [measure_prod_singleton_of_ae_single_valued hΓ hsingle hsource₀ hcarried₀ (hm j),
    measure_prod_singleton_of_ae_single_valued hΓ hsingle hsource₁ hcarried₁ (hm j)]

/-- Two plans on the same two-cycle monotone relation agree when pairwise
cost-difference laws are atomless and their source marginals agree. -/
theorem IsTwoCycleMonotone.measure_eq
    {c : S → J → ℝ} {Γ : Set (S × J)} {μ : Measure S}
    (hcycle : IsTwoCycleMonotone c Γ) (hΓ : MeasurableSet Γ)
    (hc : ∀ j, Measurable (fun x ↦ c x j))
    (hatom : ∀ i j, i ≠ j → NullSingletonClass (μ.map (fun x ↦ c x i - c x j)))
    {π₀ π₁ : Measure (S × J)}
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (hcarried₀ : ∀ᵐ z ∂π₀, z ∈ Γ) (hcarried₁ : ∀ᵐ z ∂π₁, z ∈ Γ) :
    π₀ = π₁ :=
  measure_eq_of_common_ae_single_valued_relation hΓ (hcycle.ae_single_valued hc hatom)
    hsource₀ hsource₁ hcarried₀ hcarried₁

/-- A two-cycle monotone relation carrying a nonzero multiple of the sum of
two same-source plans forces both plans to agree. This includes their average. -/
theorem IsTwoCycleMonotone.measure_eq_of_smul_add
    {c : S → J → ℝ} {Γ : Set (S × J)} {μ : Measure S}
    (hcycle : IsTwoCycleMonotone c Γ) (hΓ : MeasurableSet Γ)
    (hc : ∀ j, Measurable (fun x ↦ c x j))
    (hatom : ∀ i j, i ≠ j → NullSingletonClass (μ.map (fun x ↦ c x i - c x j)))
    {π₀ π₁ : Measure (S × J)}
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    {a : ℝ≥0∞} (ha : a ≠ 0) (hcarried : ∀ᵐ z ∂a • (π₀ + π₁), z ∈ Γ) :
    π₀ = π₁ := by
  rw [Measure.ae_ennreal_smul_measure_iff ha, ae_add_measure_iff] at hcarried
  exact hcycle.measure_eq hΓ hc hatom hsource₀ hsource₁ hcarried.1 hcarried.2

end MeasurableTargets
end OTSelector.Reconstruction
