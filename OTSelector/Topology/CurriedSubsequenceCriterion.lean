import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Curry
import Mathlib.Topology.Defs.Filter

/-!
# Topology.CurriedSubsequenceCriterion

Conditions: An array on two natural indices with the explicit strict row and within-row reindexings; the target may be any filter.

Objects: Preservation and a strict-subsequence refinement characterization of curried convergence.

Proof detail: Failure of eventual target membership leaves infinitely many bad rows, each with infinitely many bad inner indices. Extract strictly at both levels; every refinement remains bad, contradicting the supplied convergent refinement.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=86): Section 1.6.2, Definition 1.6.15 and Exercise 1.6.8, pp. 77–78.

Source relation: A proved two-level/filter generalization of Urysohn’s single-sequence principle; no first-countability premise on the target.
-/

/-!
# Strict subsequence refinement criterion for the curried filter

Failure of curried convergence leaves infinitely many bad outer indices,
each with infinitely many bad inner indices. Strict extraction on both
levels makes every further refinement stay outside one fixed target set.
This contradicts convergence of a supplied refinement to the target filter.
-/

open Set Function Filter
open scoped Topology

noncomputable section
namespace OTSelector.Probability

/-- Strict outer extraction and a strictly increasing inner extraction in
each selected original row preserve the existing curried filter. -/
theorem tendsto_curry_reindex_of_strictMono
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, StrictMono (φ ℓ)) :
    Tendsto (fun p : ℕ × ℕ ↦ (ψ p.1, φ (ψ p.1) p.2))
      ((atTop : Filter ℕ).curry atTop) ((atTop : Filter ℕ).curry atTop) := by
  apply tendsto_iff_forall_eventually_mem.mpr
  intro s hs
  have hrows := eventually_curry_iff.mp hs
  apply eventually_curry_iff.mpr
  filter_upwards [hψ.tendsto_atTop.eventually hrows] with ℓ hℓ
  exact (hφ (ψ ℓ)).tendsto_atTop.eventually hℓ

/-- If every strict two-level subsequence has a further strict refinement
converging to a target filter, the original array converges on the curried
filter. The target can be any filter, without a countability assumption. -/
theorem tendsto_curry_of_forall_strictMono_subsequence_has_refinement
    {X : Type*} (a : ℕ → ℕ → X) (l : Filter X)
    (hrefine : ∀ (ψ₀ : ℕ → ℕ), StrictMono ψ₀ →
      ∀ (φ₀ : ℕ → ℕ → ℕ), (∀ ℓ, StrictMono (φ₀ ℓ)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
          Tendsto (fun p : ℕ × ℕ ↦
            a (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ p.1 p.2)))
            ((atTop : Filter ℕ).curry atTop) l) :
    Tendsto (fun p : ℕ × ℕ ↦ a p.1 p.2) ((atTop : Filter ℕ).curry atTop) l := by
  classical
  by_contra hnot
  obtain ⟨s, hs, hbad⟩ := not_tendsto_iff_exists_frequently_notMem.mp hnot
  have hbadrows : ∃ᶠ ℓ in atTop, ∃ᶠ n in atTop, a ℓ n ∉ s :=
    (frequently_curry_iff (fun p : ℕ × ℕ ↦ a p.1 p.2 ∉ s)).mp hbad
  obtain ⟨ψ₀, hψ₀, hψ₀bad⟩ := extraction_of_frequently_atTop hbadrows
  have hinner (ℓ : ℕ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ᶠ n in atTop, a ℓ n ∉ s) → ∀ n, a ℓ (φ n) ∉ s) := by
    by_cases hℓ : ∃ᶠ n in atTop, a ℓ n ∉ s
    · obtain ⟨φ, hφ, hbadφ⟩ := extraction_of_frequently_atTop hℓ
      exact ⟨φ, hφ, fun _ ↦ hbadφ⟩
    · exact ⟨id, strictMono_id, fun h ↦ (hℓ h).elim⟩
  choose φ₀ hφ₀ hφ₀bad using hinner
  obtain ⟨ψ, _hψ, φ, _hφ, hconv⟩ := hrefine ψ₀ hψ₀ φ₀ hφ₀
  have hgood := eventually_curry_iff.mp (hconv.eventually_mem hs)
  obtain ⟨ℓ, hℓ⟩ := hgood.exists
  obtain ⟨n, hn⟩ := hℓ.exists
  exact hφ₀bad (ψ₀ (ψ ℓ)) (hψ₀bad (ψ ℓ)) (φ ℓ n) hn

/-- Exact strict-refinement characterization of curried convergence. -/
theorem tendsto_curry_iff_forall_strictMono_subsequence_has_refinement
    {X : Type*} (a : ℕ → ℕ → X) (l : Filter X) :
    Tendsto (fun p : ℕ × ℕ ↦ a p.1 p.2) ((atTop : Filter ℕ).curry atTop) l ↔
      ∀ (ψ₀ : ℕ → ℕ), StrictMono ψ₀ →
        ∀ (φ₀ : ℕ → ℕ → ℕ), (∀ ℓ, StrictMono (φ₀ ℓ)) →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
            Tendsto (fun p : ℕ × ℕ ↦
              a (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ p.1 p.2)))
              ((atTop : Filter ℕ).curry atTop) l := by
  constructor
  · intro h ψ₀ hψ₀ φ₀ hφ₀
    refine ⟨id, strictMono_id, fun _ ↦ id, fun _ ↦ strictMono_id, ?_⟩
    exact h.comp (tendsto_curry_reindex_of_strictMono ψ₀ hψ₀ φ₀ hφ₀)
  · exact tendsto_curry_of_forall_strictMono_subsequence_has_refinement a l

/-- Zero-convergence version for real, nonnegative extended-real, or any
other topological zero-valued readout, using the unchanged curried filter. -/
theorem tendsto_curry_zero_of_forall_strictMono_subsequence_has_refinement
    {X : Type*} [TopologicalSpace X] [Zero X] (a : ℕ → ℕ → X)
    (hrefine : ∀ (ψ₀ : ℕ → ℕ), StrictMono ψ₀ →
      ∀ (φ₀ : ℕ → ℕ → ℕ), (∀ ℓ, StrictMono (φ₀ ℓ)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
          Tendsto (fun p : ℕ × ℕ ↦
            a (ψ₀ (ψ p.1)) (φ₀ (ψ₀ (ψ p.1)) (φ p.1 p.2)))
            ((atTop : Filter ℕ).curry atTop) (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ ↦ a p.1 p.2) ((atTop : Filter ℕ).curry atTop) (𝓝 0) :=
  tendsto_curry_of_forall_strictMono_subsequence_has_refinement a (𝓝 0) hrefine

end OTSelector.Probability
