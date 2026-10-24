import OTSelector.Reconstruction.FinslerIntrinsicActivePositivityAgreement
import OTSelector.Transport.Coupling.LabelDisintegration

/-!
# Plan-independence of the conditional scalar marginals

This module closes the last gap of
FinslerIntrinsicActivePositivityAgreement.lean for the structural invariance
theorem (main.tex:958).

The distance-optimal face disintegration of the original populations
(OptimalFaceDisintegration.lean) says: one constructed optimal potential
describes the whole optimal face; every optimal plan π with labels a, b is
π = κ ∘ₘ (μ.map a) where, for the shared label law a.e., the conditional plan
κ z is a coupling of the fixed conditional marginals
condDistrib id a μ z and condDistrib id b ν z.  Hence the conditional marginals
of κ z are plan-independent: they are the conditional marginals of the fixed
populations μ, ν under the labels a, b.

We prove:

* conditionalCoupling_marginals_eq_ae (and the pointwise version
  conditionalCoupling_marginals_eq): two conditional plans coupling the same
  pair of conditional laws have equal conditional marginals;
* scalarRayMarginal_eq_of_conditional_marginals: equal conditional marginals
  give equal scalar marginals of the potential-clock ray couplings;
* scalarRayMarginal_plan_independent_ae (and the pointwise version
  scalarRayMarginal_plan_independent): consequently the scalar ray marginals
  of the two optimal plans coincide a.e. (pointwise) on the shared label law —
  the plan-independence of the conditional scalar marginals;
* positivity_agree_of_plan_independence: this discharges the hypothesis
  (equal scalar marginals) of rayData_positivity_agree_of_equal_marginals, so
  the positivity sets of the two potentials agree;
* exists_block_matching_of_plan_independence: consequently the injective block
  matching T between the two potentials' active block families exists;
* positivity_agree_ae_of_plan_independence: the a.e. form supplied directly by
  the face disintegration.

Remaining sub-gap: the face disintegration supplies the conditional-coupling
property only for a.e. label z, while the pointwise block matching of
FinslerIntrinsicActiveCommonSet is stated for all labels.  The null-label
kernels can be redefined arbitrarily (their conditional laws are irrelevant to
the label law), which is a routine modification not formalized here.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M]
variable {Z : Type*} [MeasurableSpace Z]

/-- **Plan-independence at the coupling level (a.e. form).**  Two conditional
plans which couple the same pair of conditional laws have equal conditional
marginals, a.e. w.r.t. the shared label law. -/
theorem conditionalCoupling_marginals_eq_ae {μ ν : Measure M} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a b : M → Z} (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z)) :
    (∀ᵐ z ∂μ.map a, (κ₁ z).map Prod.fst = (κ₂ z).map Prod.fst) ∧
      (∀ᵐ z ∂μ.map a, (κ₁ z).map Prod.snd = (κ₂ z).map Prod.snd) := by
  constructor
  · filter_upwards [h₁, h₂] with z hz₁ hz₂
    rw [hz₁.1, hz₂.1]
  · filter_upwards [h₁, h₂] with z hz₁ hz₂
    rw [hz₁.2, hz₂.2]

/-- **Plan-independence at the coupling level (pointwise form).** -/
theorem conditionalCoupling_marginals_eq {μ ν : Measure M} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a b : M → Z} (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ z : Z, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ z : Z, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z)) :
    (∀ z : Z, (κ₁ z).map Prod.fst = (κ₂ z).map Prod.fst) ∧
      (∀ z : Z, (κ₁ z).map Prod.snd = (κ₂ z).map Prod.snd) :=
  ⟨fun z ↦ by rw [(h₁ z).1, (h₂ z).1],
    fun z ↦ by rw [(h₁ z).2, (h₂ z).2]⟩

/-- Equal conditional marginals give equal scalar marginals of the
potential-clock ray couplings. -/
theorem scalarRayMarginal_eq_of_conditional_marginals {κ₁ κ₂ : Measure (M × M)}
    {u : M → ℝ} (hu : Measurable u)
    (h₁ : κ₁.map Prod.fst = κ₂.map Prod.fst)
    (h₂ : κ₁.map Prod.snd = κ₂.map Prod.snd) :
    (rayCoupling κ₁ u).map Prod.fst = (rayCoupling κ₂ u).map Prod.fst ∧
      (rayCoupling κ₁ u).map Prod.snd = (rayCoupling κ₂ u).map Prod.snd := by
  constructor
  · rw [rayCoupling_fst_eq κ₁ hu, rayCoupling_fst_eq κ₂ hu, h₁]
  · rw [rayCoupling_snd_eq κ₁ hu, rayCoupling_snd_eq κ₂ hu, h₂]

/-- **Plan-independence of the conditional scalar marginals (a.e. form).**  The two
optimal plans' potential-clock ray couplings have equal scalar marginals a.e.
w.r.t. the shared label law; their conditional scalar marginals are the
conditional marginals of the fixed populations μ, ν, pushed forward by the
potential clock. -/
theorem scalarRayMarginal_plan_independent_ae {μ ν : Measure M}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {a b : M → Z}
    {u : M → ℝ} (hu : Measurable u) (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z)) :
    (∀ᵐ z ∂μ.map a,
        (rayCoupling (κ₁ z) u).map Prod.fst = (rayCoupling (κ₂ z) u).map Prod.fst) ∧
      (∀ᵐ z ∂μ.map a,
        (rayCoupling (κ₁ z) u).map Prod.snd = (rayCoupling (κ₂ z) u).map Prod.snd) := by
  obtain ⟨hfirst, hsecond⟩ := conditionalCoupling_marginals_eq_ae κ₁ κ₂ h₁ h₂
  constructor
  · filter_upwards [hfirst] with z hz
    rw [rayCoupling_fst_eq _ hu, rayCoupling_fst_eq _ hu, hz]
  · filter_upwards [hsecond] with z hz
    rw [rayCoupling_snd_eq _ hu, rayCoupling_snd_eq _ hu, hz]

/-- **Plan-independence of the conditional scalar marginals (pointwise form).** -/
theorem scalarRayMarginal_plan_independent {μ ν : Measure M}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {a b : M → Z}
    {u : M → ℝ} (hu : Measurable u) (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ z : Z, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ z : Z, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z)) :
    (∀ z : Z,
        (rayCoupling (κ₁ z) u).map Prod.fst = (rayCoupling (κ₂ z) u).map Prod.fst) ∧
      (∀ z : Z,
        (rayCoupling (κ₁ z) u).map Prod.snd = (rayCoupling (κ₂ z) u).map Prod.snd) := by
  obtain ⟨hfirst, hsecond⟩ := conditionalCoupling_marginals_eq κ₁ κ₂ h₁ h₂
  constructor
  · intro z
    rw [rayCoupling_fst_eq _ hu, rayCoupling_fst_eq _ hu, hfirst z]
  · intro z
    rw [rayCoupling_snd_eq _ hu, rayCoupling_snd_eq _ hu, hsecond z]

/-- **Positivity agreement from plan-independence (pointwise form).**  The equal
scalar ray marginals discharge the hypothesis of
rayData_positivity_agree_of_equal_marginals, so the positivity sets of the two
potentials agree. -/
theorem positivity_agree_of_plan_independence {μ ν : Measure M}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {a b : M → Z}
    {u : M → ℝ} (hu : Measurable u) (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ z : Z, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ z : Z, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (A B : IntrinsicActiveRayData Z)
    (hAflux : ∀ z : Z, A.flux z = rayFlux (rayCoupling (κ₁ z) u))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (rayCoupling (κ₂ z) u)) :
    ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r := by
  obtain ⟨hm₁, hm₂⟩ := scalarRayMarginal_plan_independent hu κ₁ κ₂ h₁ h₂
  intro z r
  rw [hAflux z, hBflux z]
  exact positivity_agree_of_rayFlux_marginals_eq (hm₁ z) (hm₂ z) r

/-- **Block matching from plan-independence.**  The plan-independent positivity
agreement supplies the injective block matching between the two potentials'
active block families. -/
theorem exists_block_matching_of_plan_independence {μ ν : Measure M}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {a b : M → Z}
    {u : M → ℝ} (hu : Measurable u) (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ z : Z, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ z : Z, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (A B : IntrinsicActiveRayData Z)
    (hAflux : ∀ z : Z, A.flux z = rayFlux (rayCoupling (κ₁ z) u))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (rayCoupling (κ₂ z) u))
    (hAcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < A.flux z x ∧
      A.block z j = connectedComponentIn {r : ℝ | 0 < A.flux z r} x)
    (hBcomp : ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < B.flux z x ∧
      B.block z j = connectedComponentIn {r : ℝ | 0 < B.flux z r} x) :
    ∃ T : Z → ℕ → ℕ, (∀ z j, A.block z j = B.block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) := by
  have hpos : ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < B.flux z r :=
    positivity_agree_of_plan_independence hu κ₁ κ₂ h₁ h₂ A B hAflux hBflux
  exact exists_block_matching_of_positivity_agree A B hpos hAcomp hBcomp

/-- **Positivity agreement from plan-independence (a.e. form).**  The a.e. form
supplied directly by the face disintegration gives positivity agreement a.e.
on the shared label law. -/
theorem positivity_agree_ae_of_plan_independence {μ ν : Measure M}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {a b : M → Z}
    {u : M → ℝ} (hu : Measurable u) (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (A B : IntrinsicActiveRayData Z)
    (hAflux : ∀ z : Z, A.flux z = rayFlux (rayCoupling (κ₁ z) u))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (rayCoupling (κ₂ z) u)) :
    ∀ᵐ z ∂μ.map a, ∀ r : ℝ, 0 < A.flux z r ↔ 0 < B.flux z r := by
  obtain ⟨hm₁, hm₂⟩ := scalarRayMarginal_plan_independent_ae hu κ₁ κ₂ h₁ h₂
  filter_upwards [hm₁, hm₂] with z hz₁ hz₂
  intro r
  rw [hAflux z, hBflux z]
  exact positivity_agree_of_rayFlux_marginals_eq hz₁ hz₂ r

end OTSelector.Reconstruction