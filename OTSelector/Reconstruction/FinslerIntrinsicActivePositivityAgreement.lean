import OTSelector.Reconstruction.FinslerIntrinsicActiveCommonSet
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.MetricSpace.Basic

/-!
# Positivity agreement from the scalar ray marginals

This module closes gap (a) of FinslerIntrinsicActiveCommonSet.lean for the
structural invariance theorem (main.tex:958).

The surplus (flux) of a whole-ray label of an optimal plan is
rayFlux κ r = κ {p | p.1 <= r} - κ {p | p.2 <= r}, where κ is the scalar ray
coupling of the conditional plan in the potential clock.  We prove:

* rayCoupling_fst_eq / rayCoupling_snd_eq: the scalar marginals of the
  potential-clock ray coupling of a plan γ are the pushforwards of the plan's
  marginals by the potential clock, (γ.map fst).map u and (γ.map snd).map u;
* rayFlux_eq_of_marginals_eq: the surplus is determined by the two scalar
  marginals only — equal scalar marginals give equal surpluses;
* positivity agreement: hence equal scalar ray marginals give pointwise
  agreement of the positivity sets, i.e. the hypothesis hpos of the common
  active set, which supplies the block matching between the two potentials;
* gapMap / rayCoupling_gapLaw_eq / gapLaw_eq_of_double_calibration: the
  potential increment (gapMap u p = u p.2 - u p.1) of the ray coupling is the
  increment law of the plan, and double calibration (both potentials satisfy
  u p.2 - u p.1 = dist p.1 p.2) makes the increment laws of the two potentials
  coincide.

The final theorem discharges hpos for two IntrinsicActiveRayData whose fluxes
are rayFluxes of per-label scalar couplings with equal scalar marginals, and
applies the injective block matching of the common active set.

Remaining sub-gap: the physical input that the two optimal plans' conditional
scalar laws have equal scalar marginals (plan-independence of the conditional
scalar law per ray label).  Double calibration alone only gives equality of the
increment laws, not of the clock marginals; the plan-independence follows
physically from the transported minimal calibrated arcs, whose formalization
remains outside this module.
-/

open Set Function MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The first scalar marginal of the potential-clock ray coupling is the plan's
first marginal pushed forward by the potential clock. -/
theorem rayCoupling_fst_eq (γ : Measure (M × M)) {u : M → ℝ} (hu : Measurable u) :
    (rayCoupling γ u).map Prod.fst = (γ.map Prod.fst).map u := by
  rw [rayCoupling, Measure.map_map measurable_fst (measurable_rayCouplingMap hu),
    Measure.map_map hu measurable_fst]
  congr 1

/-- The second scalar marginal of the potential-clock ray coupling is the plan's
second marginal pushed forward by the potential clock. -/
theorem rayCoupling_snd_eq (γ : Measure (M × M)) {u : M → ℝ} (hu : Measurable u) :
    (rayCoupling γ u).map Prod.snd = (γ.map Prod.snd).map u := by
  rw [rayCoupling, Measure.map_map measurable_snd (measurable_rayCouplingMap hu),
    Measure.map_map hu measurable_snd]
  congr 1

/-- **The surplus depends only on the two scalar marginals.** -/
theorem rayFlux_eq_of_marginals_eq {κ₁ κ₂ : Measure (ℝ × ℝ)}
    (h₁ : κ₁.map Prod.fst = κ₂.map Prod.fst)
    (h₂ : κ₁.map Prod.snd = κ₂.map Prod.snd) (r : ℝ) :
    rayFlux κ₁ r = rayFlux κ₂ r := by
  have hfst : κ₁ {p : ℝ × ℝ | p.1 ≤ r} = κ₂ {p : ℝ × ℝ | p.1 ≤ r} := by
    have hmap : (κ₁.map Prod.fst) (Iic r) = (κ₂.map Prod.fst) (Iic r) := by
      rw [h₁]
    rw [Measure.map_apply measurable_fst measurableSet_Iic] at hmap
    rw [Measure.map_apply measurable_fst measurableSet_Iic] at hmap
    exact hmap
  have hsnd : κ₁ {p : ℝ × ℝ | p.2 ≤ r} = κ₂ {p : ℝ × ℝ | p.2 ≤ r} := by
    have hmap : (κ₁.map Prod.snd) (Iic r) = (κ₂.map Prod.snd) (Iic r) := by
      rw [h₂]
    rw [Measure.map_apply measurable_snd measurableSet_Iic] at hmap
    rw [Measure.map_apply measurable_snd measurableSet_Iic] at hmap
    exact hmap
  unfold rayFlux
  rw [hfst, hsnd]

/-- **Positivity agreement from equal scalar marginals.** -/
theorem positivity_agree_of_rayFlux_marginals_eq {κ₁ κ₂ : Measure (ℝ × ℝ)}
    (h₁ : κ₁.map Prod.fst = κ₂.map Prod.fst)
    (h₂ : κ₁.map Prod.snd = κ₂.map Prod.snd) (r : ℝ) :
    0 < rayFlux κ₁ r ↔ 0 < rayFlux κ₂ r := by
  rw [rayFlux_eq_of_marginals_eq h₁ h₂ r]

/-- The increment (gap) map of a potential clock. -/
def gapMap (u : M → ℝ) : M × M → ℝ := fun p ↦ u p.2 - u p.1

theorem measurable_gapMap {u : M → ℝ} (hu : Measurable u) :
    Measurable (gapMap u) :=
  (hu.comp measurable_snd).sub (hu.comp measurable_fst)

/-- The increment law of the potential-clock ray coupling is the increment law of
the plan: both are γ.map (gapMap u). -/
theorem rayCoupling_gapLaw_eq (γ : Measure (M × M)) {u : M → ℝ} (hu : Measurable u) :
    (rayCoupling γ u).map (fun q : ℝ × ℝ ↦ q.2 - q.1) = γ.map (gapMap u) := by
  have hg : Measurable (fun q : ℝ × ℝ ↦ q.2 - q.1) :=
    measurable_snd.sub measurable_fst
  rw [rayCoupling, Measure.map_map hg (measurable_rayCouplingMap hu)]
  congr 1

/-- **Double calibration gives equal increment laws.** -/
theorem gapLaw_eq_of_double_calibration (γ : Measure (M × M)) {u₁ u₂ : M → ℝ}
    (h₁ : ∀ᵐ p ∂γ, u₁ p.2 - u₁ p.1 = dist p.1 p.2)
    (h₂ : ∀ᵐ p ∂γ, u₂ p.2 - u₂ p.1 = dist p.1 p.2) :
    γ.map (gapMap u₁) = γ.map (gapMap u₂) := by
  refine Measure.map_congr ?_
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  show u₁ p.2 - u₁ p.1 = u₂ p.2 - u₂ p.1
  rw [hp₁, hp₂]

/-- **Positivity agreement for ray data with equal scalar marginals.** -/
theorem rayData_positivity_agree_of_equal_marginals {Z : Type*}
    (A B : IntrinsicActiveRayData Z) (κ₁ κ₂ : Z → Measure (ℝ × ℝ))
    (hAflux : ∀ z : Z, A.flux z = rayFlux (κ₁ z))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (κ₂ z))
    (hm₁ : ∀ z : Z, (κ₁ z).map Prod.fst = (κ₂ z).map Prod.fst)
    (hm₂ : ∀ z : Z, (κ₁ z).map Prod.snd = (κ₂ z).map Prod.snd) :
    ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r := by
  intro z r
  rw [hAflux z, hBflux z]
  exact positivity_agree_of_rayFlux_marginals_eq (hm₁ z) (hm₂ z) r

/-- **Block matching from equal scalar ray marginals.** -/
theorem exists_block_matching_of_equal_rayMarginals {Z : Type*}
    (A B : IntrinsicActiveRayData Z) (κ₁ κ₂ : Z → Measure (ℝ × ℝ))
    (hAflux : ∀ z : Z, A.flux z = rayFlux (κ₁ z))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (κ₂ z))
    (hm₁ : ∀ z : Z, (κ₁ z).map Prod.fst = (κ₂ z).map Prod.fst)
    (hm₂ : ∀ z : Z, (κ₁ z).map Prod.snd = (κ₂ z).map Prod.snd)
    (hAcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < A.flux z x ∧
      A.block z j = connectedComponentIn {r : ℝ | 0 < A.flux z r} x)
    (hBcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < B.flux z x ∧
      B.block z j = connectedComponentIn {r : ℝ | 0 < B.flux z r} x) :
    ∃ T : Z → ℕ → ℕ, (∀ z j, A.block z j = B.block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) := by
  have hpos : ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r :=
    rayData_positivity_agree_of_equal_marginals A B κ₁ κ₂ hAflux hBflux hm₁ hm₂
  exact exists_block_matching_of_positivity_agree A B hpos hAcomp hBcomp

end OTSelector.Reconstruction