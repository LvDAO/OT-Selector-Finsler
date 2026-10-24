import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

/-!
# Topology.CompactCutoffExhaustion

Conditions: A second-countable locally compact Hausdorff space and an open set U.

Objects: Compactly supported continuous cutoffs in [0,1], supported in U, eventually exactly one at each point of U.

Proof detail: Exhaust the open subspace by increasing compact sets, apply the LCH compact cutoff lemma to each, and use eventual membership in the exhaustion.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=143): Section 1.10.1, Lemma 1.10.1, pp. 134–135, and Exercise 1.10.6, p. 136.
- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation: Derived exhaustion construction from the stated compact-cutoff result.
-/

/-!
# Compact continuous cutoffs inside the original open clock domain

An exhaustion of the open domain supplies compactly supported cutoffs that
stay between zero and one and eventually equal one at every interior point.
-/
open Set Function Filter Topology
open scoped Topology CompactlySupported
noncomputable section
namespace OTSelector.Probability
variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [SecondCountableTopology X]

/-- Every open domain has compactly supported continuous cutoffs with support
inside the domain and eventual exact value one at each original interior point. -/
theorem exists_compact_cutoffs_eventually_one_of_isOpen (U : Set X) (hU : IsOpen U) :
    ∃ χ : ℕ → C_c(X, ℝ),
      (∀ n x, χ n x ∈ Icc 0 1) ∧ (∀ n, tsupport (χ n) ⊆ U) ∧
      ∀ x ∈ U, ∀ᶠ n in atTop, χ n x = 1 := by
  let _inst : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  have hc (n : ℕ) : IsCompact (Subtype.val '' K n : Set X) :=
    (K.isCompact n).image continuous_subtype_val
  have hsub (n : ℕ) : (Subtype.val '' K n : Set X) ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  choose f hfOne hfCompact hfSupport hfBounds using
    (fun n ↦ exists_continuousMap_one_of_isCompact_subset_isOpen (hc n) hU (hsub n))
  let χ : ℕ → C_c(X, ℝ) := fun n ↦ ⟨f n, hfCompact n⟩
  refine ⟨χ, hfBounds, hfSupport, ?_⟩
  intro x hx
  obtain ⟨N, hN⟩ := K.exists_mem ⟨x,hx⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hfOne n ⟨⟨x,hx⟩, K.subset hn hN, rfl⟩

/-- The same original open-domain cutoffs converge pointwise to one without
assuming any coercivity or regularity at the boundary of that domain. -/
theorem exists_compact_cutoffs_tendsto_one_of_isOpen (U : Set X) (hU : IsOpen U) :
    ∃ χ : ℕ → C_c(X, ℝ),
      (∀ n x, χ n x ∈ Icc 0 1) ∧ (∀ n, tsupport (χ n) ⊆ U) ∧
      ∀ x ∈ U, Tendsto (fun n ↦ χ n x) atTop (𝓝 1) := by
  obtain ⟨χ, hb, hs, he⟩ := exists_compact_cutoffs_eventually_one_of_isOpen U hU
  refine ⟨χ, hb, hs, ?_⟩
  intro x hx
  exact tendsto_const_nhds.congr' ((he x hx).mono fun _ hn ↦ hn.symm)

end OTSelector.Probability
