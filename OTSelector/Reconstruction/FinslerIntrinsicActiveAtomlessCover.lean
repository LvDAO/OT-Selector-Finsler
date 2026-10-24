import OTSelector.Transport.Calibration.ScalarRayCoupling
import OTSelector.Reconstruction.FinslerIntrinsicActiveInvariance
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Connected.Basic

/-!
# Conditional atomlessness and geometric two-cover instantiation

This module closes the two remaining gaps of
FinslerIntrinsicActiveMatching.lean for the structural invariance theorem
(main.tex:958).

## Atomlessness of the conditional scalar laws

The window/input laws of the Finsler chain have densities with respect to the
volume, which is atomless on singletons; we prove that absolute continuity
transfers atomlessness, that a density w.r.t. an atomless reference measure is
atomless, that a family of conditional laws (the conditional scalar laws of the
whole-ray labels) is atomless on singletons when each conditional is absolutely
continuous w.r.t. an atomless window law, and that atomlessness of the scalar
first marginal of a physical plan implies the vertical atomlessness hypothesis
hatom of the flux construction (rayCut flux identity).

## Geometric instantiation of the two-cover containment

The active blocks of the paper are the connected components of the common
active ray set U_z = {r | 0 < H_z r} of a fixed whole-ray label z.  We prove
the abstract component-cover lemma: a connected block contained in a cover by
connected components of U lies in a single component; hence two block families
which are both component covers of the same active set U_z satisfy the
two-cover cross-containment hypothesis hAB/hBA of
block_matching_of_cross_cover (FinslerIntrinsicActiveInvariance.lean), giving
the injective block matching T.

Remaining sub-gap: the geometric identification of the two potentials' active
sets U_z^phi = U_z^psi via transported minimal calibrated arcs (the
constant-difference-on-arcs core is in
potentialDifference_const_of_double_calibration); the Borel/measure-theoretic
layer is supplied by FinslerIntrinsicActiveMatching.lean.
-/

open Set Function MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {X : Type*} [MeasurableSpace X]

/-- **Atomlessness transfers across absolute continuity.** -/
theorem measure_singleton_eq_zero_of_absolutelyContinuous {γ ref : Measure X}
    (hac : γ ≪ ref) (href : ∀ x : X, ref {x} = 0) (x : X) : γ {x} = 0 :=
  hac (href x)

/-- **Densities of atomless laws are atomless.**  The window/input laws of the
paper have densities w.r.t. the volume, which is atomless on singletons. -/
theorem withDensity_singleton_eq_zero (ref : Measure X) (f : X → ℝ≥0∞)
    (href : ∀ x : X, ref {x} = 0) (x : X) : (ref.withDensity f) {x} = 0 :=
  measure_singleton_eq_zero_of_absolutelyContinuous
    (withDensity_absolutelyContinuous ref f) href x

/-- **Conditional atomlessness.**  If every conditional scalar law is
absolutely continuous w.r.t. an atomless window law, every conditional scalar
law is atomless on singletons. -/
theorem conditional_laws_singleton_eq_zero_of_absoluteContinuity {Z : Type*}
    [MeasurableSpace Z] (κ : Z → Measure X) (ref : Z → Measure X)
    (hac : ∀ z : Z, κ z ≪ ref z) (href : ∀ (z : Z) (x : X), ref z {x} = 0)
    (z : Z) (x : X) : κ z {x} = 0 :=
  hac z (href z x)

/-- **Scalar-law atomlessness gives the flux hypothesis.**  If the first scalar
marginal (the conditional scalar law of a whole-ray label) is atomless, then
the potential-clock ray coupling is atomless on verticals, i.e. the hatom
hypothesis of the ray-cut flux identity. -/
theorem rayCoupling_singleton_eq_zero_of_scalarLaw_atomless {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (γ : Measure (M × M)) [IsFiniteMeasure γ] {u : M → ℝ} (hu : Measurable u)
    (hscal : ∀ r : ℝ, ((γ.map Prod.fst).map u) {r} = 0) (r : ℝ) :
    rayCoupling γ u {q : ℝ × ℝ | q.1 = r} = 0 := by
  have hset : MeasurableSet {q : ℝ × ℝ | q.1 = r} :=
    (measurableSet_singleton r).preimage measurable_fst
  rw [rayCoupling, Measure.map_apply (measurable_rayCouplingMap hu) hset]
  have hpre : rayCouplingMap u ⁻¹' {q : ℝ × ℝ | q.1 = r} =
      {p : M × M | u p.1 = r} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, rayCouplingMap]
  rw [hpre]
  have h1 : (γ.map Prod.fst) (u ⁻¹' {r}) = γ {p : M × M | u p.1 = r} := by
    rw [Measure.map_apply measurable_fst ((measurableSet_singleton r).preimage hu)]
    congr 1
  have h2 : ((γ.map Prod.fst).map u) {r} = (γ.map Prod.fst) (u ⁻¹' {r}) := by
    rw [Measure.map_apply hu (measurableSet_singleton r)]
  rw [← h1, ← h2]
  exact hscal r

variable {α : Type*} [TopologicalSpace α]

/-- **Component-cover lemma.**  A connected block lying in a cover by connected
components of an active set U lies inside one block of the cover. -/
theorem connected_subset_of_component_cover {U A : Set α}
    (hA : IsPreconnected A) (hAU : A ⊆ U) (hne : A.Nonempty)
    {ι : Type*} {B : ι → Set α} (hcover : U ⊆ ⋃ i, B i)
    (hBcomp : ∀ i, ∃ y ∈ U, B i = connectedComponentIn U y) :
    ∃ i, A ⊆ B i := by
  obtain ⟨a, haA⟩ := hne
  have haU : a ∈ U := hAU haA
  obtain ⟨i, hai⟩ := Set.mem_iUnion.mp (hcover haU)
  obtain ⟨y, _hyU, hB⟩ := hBcomp i
  refine ⟨i, ?_⟩
  have hai' : a ∈ connectedComponentIn U y := by
    rw [hB] at hai
    exact hai
  rw [hB, connectedComponentIn_eq hai']
  exact hA.subset_connectedComponentIn haA hAU

/-- **Two-cover cross-containment.**  Two covers by connected components of the
same active set U satisfy both containment directions. -/
theorem component_cover_cross_containment {U : Set α} {ι κ : Type*}
    (A : ι → Set α) (B : κ → Set α)
    (hAcover : U ⊆ ⋃ i, A i)
    (hAcomp : ∀ i, ∃ x ∈ U, A i = connectedComponentIn U x)
    (hBcover : U ⊆ ⋃ j, B j)
    (hBcomp : ∀ j, ∃ y ∈ U, B j = connectedComponentIn U y) :
    (∀ i, (A i).Nonempty → ∃ j, A i ⊆ B j) ∧
      (∀ j, (B j).Nonempty → ∃ i, B j ⊆ A i) := by
  constructor
  · intro i hne
    obtain ⟨x, _hxU, hAeq⟩ := hAcomp i
    exact connected_subset_of_component_cover (hAeq ▸ isPreconnected_connectedComponentIn)
      (hAeq ▸ connectedComponentIn_subset U x) hne hBcover hBcomp
  · intro j hne
    obtain ⟨y, _hyU, hBeq⟩ := hBcomp j
    exact connected_subset_of_component_cover (hBeq ▸ isPreconnected_connectedComponentIn)
      (hBeq ▸ connectedComponentIn_subset U y) hne hAcover hAcomp

/-- **Geometric two-cover instantiation for the ray data.**  If the active
blocks of two ray data are connected components of a common active ray set
U_z, then they satisfy the two-cover cross-containment hypotheses. -/
theorem intrinsicActiveRayData_cross_containment {Z : Type*}
    (A B : IntrinsicActiveRayData Z) (U : Z → Set ℝ)
    (hAflux : ∀ z : Z, {r : ℝ | 0 < A.flux z r} = U z)
    (hBflux : ∀ z : Z, {r : ℝ | 0 < B.flux z r} = U z)
    (hAcomp : ∀ (z : Z) (j : ℕ), ∃ x ∈ U z,
      A.block z j = connectedComponentIn (U z) x)
    (hBcomp : ∀ (z : Z) (j : ℕ), ∃ x ∈ U z,
      B.block z j = connectedComponentIn (U z) x) :
    (∀ z j, ∃ k, A.block z j ⊆ B.block z k) ∧
      (∀ z k, ∃ j, B.block z k ⊆ A.block z j) := by
  constructor
  · intro z j
    have hcover : U z ⊆ ⋃ k, B.block z k := by
      intro r hr
      have hpos : 0 < B.flux z r := by
        have hmem : r ∈ {q : ℝ | 0 < B.flux z q} := by
          rw [hBflux z]
          exact hr
        simpa using hmem
      obtain ⟨k, hk⟩ := B.cover_pos z r hpos
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
    obtain ⟨x, _hxU, hAeq⟩ := hAcomp z j
    exact connected_subset_of_component_cover
      (hAeq ▸ isPreconnected_connectedComponentIn)
      (hAeq ▸ connectedComponentIn_subset (U z) x) (A.nonempty z j) hcover (hBcomp z)
  · intro z k
    have hcover : U z ⊆ ⋃ j, A.block z j := by
      intro r hr
      have hpos : 0 < A.flux z r := by
        have hmem : r ∈ {q : ℝ | 0 < A.flux z q} := by
          rw [hAflux z]
          exact hr
        simpa using hmem
      obtain ⟨j, hj⟩ := A.cover_pos z r hpos
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    obtain ⟨x, _hxU, hBeq⟩ := hBcomp z k
    exact connected_subset_of_component_cover
      (hBeq ▸ isPreconnected_connectedComponentIn)
      (hBeq ▸ connectedComponentIn_subset (U z) x) (B.nonempty z k) hcover (hAcomp z)

/-- **Block matching from the geometric component covers.**  The cross-containment
supplies the injective block matching T of block_matching_of_cross_cover. -/
theorem exists_block_matching_of_component_cover {Z : Type*}
    (A B : IntrinsicActiveRayData Z) (U : Z → Set ℝ)
    (hAflux : ∀ z : Z, {r : ℝ | 0 < A.flux z r} = U z)
    (hBflux : ∀ z : Z, {r : ℝ | 0 < B.flux z r} = U z)
    (hAcomp : ∀ (z : Z) (j : ℕ), ∃ x ∈ U z,
      A.block z j = connectedComponentIn (U z) x)
    (hBcomp : ∀ (z : Z) (j : ℕ), ∃ x ∈ U z,
      B.block z j = connectedComponentIn (U z) x) :
    ∃ T : Z → ℕ → ℕ, (∀ z j, A.block z j = B.block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) := by
  obtain ⟨hAB, hBA⟩ :=
    intrinsicActiveRayData_cross_containment A B U hAflux hBflux hAcomp hBcomp
  exact block_matching_of_cross_cover A B hAB hBA

end OTSelector.Reconstruction