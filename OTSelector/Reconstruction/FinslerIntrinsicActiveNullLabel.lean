import OTSelector.Reconstruction.FinslerIntrinsicActivePlanIndependence

/-!
# Null-label modification and ray-data wiring

This module closes the remaining items of
FinslerIntrinsicActivePlanIndependence.lean for the structural invariance
theorem (main.tex:958).

## Null-label modification

The face disintegration supplies the conditional-coupling property (and hence,
by plan-independence, the agreement of the two potentials' surpluses and
positivity sets) only for a.e. label w.r.t. the shared label law `μ.map a`.
Here we:

* produce the conull agreement set `S`: on `S` the two surplus functions agree
  and their positivity sets agree, and the complement of `S` is `μ.map a`-null;
* construct the null-label modification `nullLabelModification A B S` of the
  second ray data: it agrees with `B` on `S` and with `A` off `S`, so it is a
  valid `IntrinsicActiveRayData` that differs from `B` only on a null set of
  labels;
* show that `A` and the modified data have pointwise agreeing positivity sets,
  so the injective block matching of the common active set applies for all
  labels, not merely a.e.

## Ray-data wiring

We record the minimal geometric interface consumed from the Finsler geometry
lane as `IntrinsicActiveRayGeometry`: a constructed optimal potential (the ray
clock), measurable label maps constant on its calibrated pairs.  The final
theorem wires this interface together with the face-disintegration hypotheses
(the two optimal plans as conditional mixtures over the labels) and concludes
the conull-set null-label modification and the global injective block matching.

Remaining sub-gaps (exact inputs still required from other lanes):

* the transport construction of the label maps along minimal calibrated arcs
  (the geometric construction of `labelFirst`, `labelSecond` from the
  potential's calibrated arcs) is an input of `IntrinsicActiveRayGeometry`, not
  constructed here;
* the balance identity `μ.map labelFirst = ν.map labelSecond` and the
  conditional-mixture representation of the two optimal plans (with the a.e.
  conditional-coupling property) are supplied by the face disintegration
  theorem of OptimalFaceDisintegration.lean, consumed as hypotheses;
* the component-cover hypothesis `IsComponentCover` (blocks are connected
  components of their positive-flux sets) is the paper's cover identity
  `eq:intrinsic-active-cover` plus minimal-arc transport, kept as an explicit
  hypothesis.
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

/-! ## The conull agreement set -/

/-- **A.e. equality of the surplus functions.**  The two potentials' ray
surpluses coincide a.e. on the shared label law. -/
theorem rayFlux_eq_ae_of_plan_independence {μ ν : Measure M} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a b : M → Z} {u : M → ℝ} (hu : Measurable u)
    (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z)) :
    ∀ᵐ z ∂μ.map a, rayFlux (rayCoupling (κ₁ z) u) = rayFlux (rayCoupling (κ₂ z) u) := by
  obtain ⟨hm₁, hm₂⟩ := scalarRayMarginal_plan_independent_ae hu κ₁ κ₂ h₁ h₂
  filter_upwards [hm₁, hm₂] with z hz₁ hz₂
  funext r
  exact rayFlux_eq_of_marginals_eq hz₁ hz₂ r

/-- **Conull flux-agreement set.**  For the two optimal plans there is a set `S`
of labels, conull for the shared label law, on which the two surplus functions
and their positivity sets agree pointwise. -/
theorem exists_conull_flux_agree_set {μ ν : Measure M} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a b : M → Z} {u : M → ℝ} (hu : Measurable u)
    (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₁ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (h₂ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ₂ z) (condDistrib id a μ z)
      (condDistrib id b ν z))
    (A B : IntrinsicActiveRayData Z)
    (hAflux : ∀ z : Z, A.flux z = rayFlux (rayCoupling (κ₁ z) u))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (rayCoupling (κ₂ z) u)) :
    ∃ S : Set Z, (μ.map a) Sᶜ = 0 ∧
      (∀ z ∈ S, A.flux z = B.flux z) ∧
      (∀ z ∈ S, ∀ r : ℝ, 0 < A.flux z r ↔ 0 < B.flux z r) := by
  have hflux_ae : ∀ᵐ z ∂μ.map a, A.flux z = B.flux z := by
    have hfl := rayFlux_eq_ae_of_plan_independence hu κ₁ κ₂ h₁ h₂
    filter_upwards [hfl] with z hz
    rw [hAflux z, hBflux z]
    exact hz
  have hpos_ae := positivity_agree_ae_of_plan_independence hu κ₁ κ₂ h₁ h₂ A B hAflux hBflux
  let S : Set Z := {z | A.flux z = B.flux z ∧
    ∀ r : ℝ, 0 < A.flux z r ↔ 0 < B.flux z r}
  have hae : ∀ᵐ z ∂μ.map a, z ∈ S := by
    filter_upwards [hflux_ae, hpos_ae] with z hz₁ hz₂
    exact ⟨hz₁, hz₂⟩
  have hnull : (μ.map a) {z : Z | ¬ z ∈ S} = 0 := MeasureTheory.ae_iff.mp hae
  have hset : Sᶜ = {z : Z | ¬ z ∈ S} := by
    ext z
    simp
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hset]
    exact hnull
  · intro z hz
    exact hz.1
  · intro z hz
    exact hz.2

/-! ## Null-label modification of the ray data -/

/-- **Null-label modification.**  The ray data that agrees with `B` on the label
set `S` and with `A` off `S`.  It is a valid `IntrinsicActiveRayData` and differs
from `B` only on the complement of `S`. -/
def nullLabelModification (A B : IntrinsicActiveRayData Z) (S : Set Z) :
    IntrinsicActiveRayData Z := by
  classical
  exact
    { flux := fun z => if z ∈ S then B.flux z else A.flux z
      block := fun z j => if z ∈ S then B.block z j else A.block z j
      nonempty := by
        intro z j
        by_cases h : z ∈ S
        · rw [if_pos h]
          exact B.nonempty z j
        · rw [if_neg h]
          exact A.nonempty z j
      disjoint := by
        intro z j k hjk
        by_cases h : z ∈ S
        · rw [if_pos h, if_pos h]
          exact B.disjoint z j k hjk
        · rw [if_neg h, if_neg h]
          exact A.disjoint z j k hjk
      block_pos := by
        intro z j r hr
        by_cases h : z ∈ S
        · rw [if_pos h] at hr ⊢
          exact B.block_pos z j hr
        · rw [if_neg h] at hr ⊢
          exact A.block_pos z j hr
      cover_pos := by
        intro z r hr
        by_cases h : z ∈ S
        · rw [if_pos h] at hr
          obtain ⟨j, hj⟩ := B.cover_pos z r hr
          exact ⟨j, by rw [if_pos h]; exact hj⟩
        · rw [if_neg h] at hr
          obtain ⟨j, hj⟩ := A.cover_pos z r hr
          exact ⟨j, by rw [if_neg h]; exact hj⟩ }

theorem nullLabelModification_flux_of_mem {A B : IntrinsicActiveRayData Z} {S : Set Z}
    {z : Z} (hz : z ∈ S) : (nullLabelModification A B S).flux z = B.flux z := by
  dsimp [nullLabelModification]
  classical
  rw [if_pos hz]

theorem nullLabelModification_flux_of_notMem {A B : IntrinsicActiveRayData Z}
    {S : Set Z} {z : Z} (hz : z ∉ S) :
    (nullLabelModification A B S).flux z = A.flux z := by
  dsimp [nullLabelModification]
  classical
  rw [if_neg hz]

theorem nullLabelModification_block_of_mem {A B : IntrinsicActiveRayData Z}
    {S : Set Z} {z : Z} (hz : z ∈ S) (j : ℕ) :
    (nullLabelModification A B S).block z j = B.block z j := by
  dsimp [nullLabelModification]
  classical
  rw [if_pos hz]

theorem nullLabelModification_block_of_notMem {A B : IntrinsicActiveRayData Z}
    {S : Set Z} {z : Z} (hz : z ∉ S) (j : ℕ) :
    (nullLabelModification A B S).block z j = A.block z j := by
  dsimp [nullLabelModification]
  classical
  rw [if_neg hz]

/-- **Positivity agreement with the null-label modification.** -/
theorem positivity_agree_nullLabelModification {A B : IntrinsicActiveRayData Z}
    {S : Set Z} (hpos : ∀ z ∈ S, ∀ r : ℝ, 0 < A.flux z r ↔ 0 < B.flux z r) :
    ∀ (z : Z) (r : ℝ), 0 < A.flux z r ↔ 0 < (nullLabelModification A B S).flux z r := by
  intro z r
  by_cases h : z ∈ S
  · rw [nullLabelModification_flux_of_mem h]
    exact hpos z h r
  · rw [nullLabelModification_flux_of_notMem h]

/-- An active block family is a component cover when every block is a connected
component of its own positive-flux set (paper's cover identity
`eq:intrinsic-active-cover` together with the minimal calibrated arc transport). -/
def IsComponentCover (A : IntrinsicActiveRayData Z) : Prop :=
  ∀ (z : Z) (j : ℕ), ∃ x : ℝ, 0 < A.flux z x ∧
    A.block z j = connectedComponentIn {r : ℝ | 0 < A.flux z r} x

/-- **Block matching after the null-label modification.**  If the two ray data
agree in positivity on the set `S` and both are component covers, then the first
ray data and the null-label modification of the second admit the injective block
matching for all labels. -/
theorem exists_block_matching_nullLabel (A B : IntrinsicActiveRayData Z) (S : Set Z)
    (hpos : ∀ z ∈ S, ∀ r : ℝ, 0 < A.flux z r ↔ 0 < B.flux z r)
    (hA : IsComponentCover A) (hB : IsComponentCover B) :
    ∃ T : Z → ℕ → ℕ,
      (∀ z j, A.block z j = (nullLabelModification A B S).block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) := by
  have hpos' : ∀ (z : Z) (r : ℝ),
      0 < A.flux z r ↔ 0 < (nullLabelModification A B S).flux z r :=
    positivity_agree_nullLabelModification hpos
  have hB' : IsComponentCover (nullLabelModification A B S) := by
    intro z j
    by_cases h : z ∈ S
    · obtain ⟨x, hx, hEq⟩ := hB z j
      refine ⟨x, ?_, ?_⟩
      · rw [nullLabelModification_flux_of_mem h]
        exact hx
      · rw [nullLabelModification_block_of_mem h, nullLabelModification_flux_of_mem h]
        exact hEq
    · obtain ⟨x, hx, hEq⟩ := hA z j
      refine ⟨x, ?_, ?_⟩
      · rw [nullLabelModification_flux_of_notMem h]
        exact hx
      · rw [nullLabelModification_block_of_notMem h, nullLabelModification_flux_of_notMem h]
        exact hEq
  exact exists_block_matching_of_positivity_agree A (nullLabelModification A B S)
    hpos' hA hB'

/-! ## Ray-data wiring: the geometric interface -/

/-- **Minimal geometric interface from the Finsler geometry lane.**  A constructed
optimal potential (used as the ray clock) and measurable label maps constant on
its calibrated pairs.  The transport construction of the labels along minimal
calibrated arcs is precisely what has to be supplied here. -/
structure IntrinsicActiveRayGeometry (M Z : Type*) [MetricSpace M] [MeasurableSpace M]
    [MeasurableSpace Z] where
  /-- The constructed optimal potential, used as the ray clock. -/
  potential : M → ℝ
  /-- First-label map (whole-ray label of the first marginal). -/
  labelFirst : M → Z
  /-- Second-label map (whole-ray label of the second marginal). -/
  labelSecond : M → Z
  measurable_labelFirst : Measurable labelFirst
  measurable_labelSecond : Measurable labelSecond
  measurable_potential : Measurable potential
  /-- The labels are constant on calibrated pairs (locality of the whole-ray
  label along the constructed minimal calibrated arcs). -/
  label_constant_on_calibrated : ∀ ⦃x y : M⦄, potential y - potential x = dist x y →
    labelFirst x = labelSecond y

/-- **Wiring theorem.**  Consuming the geometric interface and the
face-disintegration hypotheses (two optimal plans as conditional mixtures over
the labels, with the a.e. conditional-coupling property), there is a conull label
set `S` such that: the two surpluses agree on `S`; the second ray data modified
only on the null label set `Sᶜ` admits the injective block matching with the
first; and the modification leaves the surplus unchanged off `S`. -/
theorem exists_block_matching_of_geometry {μ ν : Measure M} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (G : IntrinsicActiveRayGeometry M Z)
    (κ₁ κ₂ : Kernel Z (M × M))
    (h₁ : ∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ₁ z)
      (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z))
    (h₂ : ∀ᵐ z ∂μ.map G.labelFirst, Vlasov.IsCoupling (κ₂ z)
      (condDistrib id G.labelFirst μ z) (condDistrib id G.labelSecond ν z))
    (A B : IntrinsicActiveRayData Z)
    (hAflux : ∀ z : Z, A.flux z = rayFlux (rayCoupling (κ₁ z) G.potential))
    (hBflux : ∀ z : Z, B.flux z = rayFlux (rayCoupling (κ₂ z) G.potential))
    (hA : IsComponentCover A) (hB : IsComponentCover B) :
    ∃ (S : Set Z) (T : Z → ℕ → ℕ),
      (μ.map G.labelFirst) Sᶜ = 0 ∧
      (∀ z ∈ S, A.flux z = B.flux z) ∧
      (∀ z ∈ S, ∀ r : ℝ, 0 < A.flux z r ↔ 0 < B.flux z r) ∧
      (∀ z j, A.block z j = (nullLabelModification A B S).block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) ∧
      (∀ z ∉ S, (nullLabelModification A B S).flux z = A.flux z) := by
  obtain ⟨S, hS, hfluxS, hposS⟩ := exists_conull_flux_agree_set (u := G.potential)
    G.measurable_potential κ₁ κ₂ h₁ h₂ A B hAflux hBflux
  obtain ⟨T, hT, hinj⟩ := exists_block_matching_nullLabel A B S hposS hA hB
  refine ⟨S, T, hS, hfluxS, hposS, hT, hinj, ?_⟩
  intro z hz
  exact nullLabelModification_flux_of_notMem hz

end OTSelector.Reconstruction