import OTSelector.Reconstruction.FinslerIntrinsicActiveAtomlessCover
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Conditional-density instantiation and the common active set

This module closes the two remaining gaps of
FinslerIntrinsicActiveAtomlessCover.lean for the structural invariance theorem
(main.tex:958).

## Conditional-density instantiation

The conditional scalar laws of the physical window law are given by densities
w.r.t. an atomless reference law (the volume/window measure); we construct
them and discharge the absolute-continuity hypothesis `hac` of
conditional_laws_singleton_eq_zero_of_absoluteContinuity and the scalar
atomlessness hypothesis `hscal` of
rayCoupling_singleton_eq_zero_of_scalarLaw_atomless: if the scalar first
marginal of a physical plan is `ref.withDensity dens` with `ref` atomless on
singletons, then the potential-clock ray coupling is atomless on all verticals.

## Common active set

The two optimal potentials phi, psi of the invariance theorem act on the same
ray parameter; their active sets are the positivity sets of the two surpluses
H^phi_z, H^psi_z.  We prove that pointwise agreement of the positivity sets
gives a common active set U_z, that blocks which are connected components of
their own positivity set are then component covers of U_z, and consequently
(via the component-cover cross-containment of
FinslerIntrinsicActiveAtomlessCover) that the two block families satisfy the
two-cover hypotheses of block_matching_of_cross_cover and admit the injective
block matching T.  The final theorem bundles the atomlessness and the block
matching conclusion.

Remaining sub-gap: the derivation of the positivity agreement `hpos` from the
physical data (that the active components are plan-independent, i.e. depend
only on the marginals and the canonical ray parametrization; the
constant-difference-on-arcs core is
potentialDifference_const_of_double_calibration) is not formalized here; it is
consumed as the explicit hypothesis hpos.
-/

open Set Function MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {Z : Type*}

/-- **Conditional-density instantiation.**  If the conditional scalar laws are
given by densities w.r.t. an atomless reference law, then every conditional
scalar law is atomless on singletons (discharges the absolute-continuity
hypothesis of conditional_laws_singleton_eq_zero_of_absoluteContinuity). -/
theorem conditional_law_withDensity_singleton_eq_zero (ref : Z → Measure ℝ)
    (dens : Z → ℝ → ℝ≥0∞) (href : ∀ (z : Z) (r : ℝ), ref z {r} = 0) :
    ∀ (z : Z) (r : ℝ), ((ref z).withDensity (dens z)) {r} = 0 :=
  fun z r ↦ withDensity_singleton_eq_zero (ref z) (dens z) (href z) r

/-- **Scalar atomlessness from a window density.**  If the first scalar marginal
of a physical plan is a density w.r.t. an atomless reference law, then the
potential-clock ray coupling is atomless on all verticals, i.e. the `hatom`
hypothesis of the ray-cut flux identity is discharged. -/
theorem rayCoupling_vertical_atomless_of_window_density {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (γ : Measure (M × M)) [IsFiniteMeasure γ] {u : M → ℝ} (hu : Measurable u)
    {ref : Measure ℝ} (href : ∀ r : ℝ, ref {r} = 0) (dens : ℝ → ℝ≥0∞)
    (hmarg : (γ.map Prod.fst).map u = ref.withDensity dens) :
    ∀ r : ℝ, rayCoupling γ u {q : ℝ × ℝ | q.1 = r} = 0 := by
  intro r
  refine rayCoupling_singleton_eq_zero_of_scalarLaw_atomless γ hu ?_ r
  intro r'
  rw [hmarg]
  exact withDensity_singleton_eq_zero ref dens href r'

section CommonActiveSet

/-- Pointwise agreement of the positivity sets of two surpluses gives equality of
the active sets. -/
theorem activeSet_eq_of_positivity_agree {H₁ H₂ : ℝ → ℝ}
    (h : ∀ r : ℝ, 0 < H₁ r ↔ 0 < H₂ r) :
    {r : ℝ | 0 < H₁ r} = {r : ℝ | 0 < H₂ r} := by
  ext r
  exact h r

/-- **Common active set.**  If the positivity sets of the two ray surpluses agree
pointwise, there is a common active ray set U_z carrying both. -/
theorem exists_common_active_set (A B : IntrinsicActiveRayData Z)
    (hpos : ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r) :
    ∃ U : Z → Set ℝ, (∀ z : Z, {r : ℝ | 0 < A.flux z r} = U z) ∧
      (∀ z : Z, {r : ℝ | 0 < B.flux z r} = U z) :=
  ⟨fun z ↦ {r : ℝ | 0 < A.flux z r}, fun _ ↦ rfl,
    fun z ↦ activeSet_eq_of_positivity_agree (fun r ↦ (hpos z r).symm)⟩

/-- **Cross-containment from the common active set.**  If each block is a
connected component of its own positivity set, pointwise positivity agreement
makes both block families component covers of the common active set, so the
two-cover cross-containment holds. -/
theorem cross_containment_of_positivity_agree (A B : IntrinsicActiveRayData Z)
    (hpos : ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r)
    (hAcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < A.flux z x ∧
      A.block z j = connectedComponentIn {r : ℝ | 0 < A.flux z r} x)
    (hBcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < B.flux z x ∧
      B.block z j = connectedComponentIn {r : ℝ | 0 < B.flux z r} x) :
    (∀ z j, ∃ k, A.block z j ⊆ B.block z k) ∧
      (∀ z k, ∃ j, B.block z k ⊆ A.block z j) := by
  let U : Z → Set ℝ := fun z ↦ {r : ℝ | 0 < A.flux z r}
  have hAflux : ∀ z : Z, {r : ℝ | 0 < A.flux z r} = U z :=
    fun _ ↦ rfl
  have hBflux : ∀ z : Z, {r : ℝ | 0 < B.flux z r} = U z :=
    fun z ↦ activeSet_eq_of_positivity_agree (fun r ↦ (hpos z r).symm)
  have hAcomp' : ∀ (z : Z) (j : ℕ), ∃ x ∈ U z,
      A.block z j = connectedComponentIn (U z) x := by
    intro z j
    obtain ⟨x, hx, hEq⟩ := hAcomp z j
    exact ⟨x, hx, hEq⟩
  have hBcomp' : ∀ (z : Z) (j : ℕ), ∃ x ∈ U z,
      B.block z j = connectedComponentIn (U z) x := by
    intro z j
    obtain ⟨x, hxB, hEq⟩ := hBcomp z j
    refine ⟨x, (hpos z x).mpr hxB, ?_⟩
    rw [hEq, hBflux z]
  exact intrinsicActiveRayData_cross_containment A B U hAflux hBflux hAcomp' hBcomp'

/-- **Block matching from the common active set.**  The cross-containment
supplies the injective block matching T of block_matching_of_cross_cover. -/
theorem exists_block_matching_of_positivity_agree (A B : IntrinsicActiveRayData Z)
    (hpos : ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r)
    (hAcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < A.flux z x ∧
      A.block z j = connectedComponentIn {r : ℝ | 0 < A.flux z r} x)
    (hBcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < B.flux z x ∧
      B.block z j = connectedComponentIn {r : ℝ | 0 < B.flux z r} x) :
    ∃ T : Z → ℕ → ℕ, (∀ z j, A.block z j = B.block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) := by
  obtain ⟨hAB, hBA⟩ := cross_containment_of_positivity_agree A B hpos hAcomp hBcomp
  exact block_matching_of_cross_cover A B hAB hBA

end CommonActiveSet

/-- **Bundled conclusion.**  The conditional-density instantiation discharges the
vertical atomlessness of the potential-clock ray coupling, and the common
active set supplies the injective block matching between the two potentials'
block families. -/
theorem atomless_and_matching_of_window_density_and_positivity {M : Type*}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (γ : Measure (M × M)) [IsFiniteMeasure γ] {u : M → ℝ} (hu : Measurable u)
    {ref : Measure ℝ} (href : ∀ r : ℝ, ref {r} = 0) (dens : ℝ → ℝ≥0∞)
    (hmarg : (γ.map Prod.fst).map u = ref.withDensity dens)
    (A B : IntrinsicActiveRayData Z)
    (hpos : ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r)
    (hAcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < A.flux z x ∧
      A.block z j = connectedComponentIn {r : ℝ | 0 < A.flux z r} x)
    (hBcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < B.flux z x ∧
      B.block z j = connectedComponentIn {r : ℝ | 0 < B.flux z r} x) :
    (∀ r : ℝ, rayCoupling γ u {q : ℝ × ℝ | q.1 = r} = 0) ∧
      ∃ T : Z → ℕ → ℕ, (∀ z j, A.block z j = B.block z (T z j)) ∧
        (∀ z j k, T z j = T z k → j = k) :=
  ⟨rayCoupling_vertical_atomless_of_window_density γ hu href dens hmarg,
    exists_block_matching_of_positivity_agree A B hpos hAcomp hBcomp⟩

end OTSelector.Reconstruction