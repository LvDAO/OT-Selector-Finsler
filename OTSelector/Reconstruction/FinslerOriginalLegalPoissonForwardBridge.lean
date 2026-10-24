import OTSelector.Reconstruction.FinslerOriginalAbstractCarrierConstruction
import OTSelector.Reconstruction.MarkedStationaryValueLegalFiniteMomentReserve

/-!
# Window-supported forward classes and the legal-to-forward Palm bridge

Two gaps of `FinslerOriginalForwardDataConvergence` are addressed here.

## 1.  Restriction to window-supported stationary matchings

Regularity only gives uniform closeness of the calibrated coefficient on a
compact window `S ⊆ ℝ × ℝ` and of the probe on a compact marked-pair sample
`T`, while the stationary-class continuity needs global uniformity.  Restricting
attention to the stationary matchings whose Palm law is supported in `T` (and
whose unweighted second moment is bounded by `B`) removes the gap: on this class
`forwardWindowClass T B` the a.e. coefficient/probe bounds produce uniform
Kinetic/probe Palm-energy convergence (`stationaryForward_kineticProbe_uniform_convergence_on_window`),
hence both refinement hypotheses (`stationaryForward_hclass_hconv_on_window`)
and the local pressure continuity capstone
`continuousOn_stationaryForwardPressureFamily_on_window`.

## 2.  The legal Poisson Palm as finite-second-moment bridge data

The abstract `StationaryForwardMatching` carrier and the legal
`LegalWeightedStationaryPoissonMatching` carrier live on different label spaces:
the abstract Palm is a probability law on marked pairs with `UnitMark` labels,
while the legal Palm `legalMarkedJointPalm q Q.law` is a probability law on
`PhysicalPairPalmMark (Fin q) = (ℝ × ℝ) × (Fin q → ℝ)`.  We record the canonical
recoding `legalPairToMarkedPair` of a legal Palm pair to an abstract marked pair,
package the existing finite-second-moment reserve as a probability Palm object
with finite second moment, and state the exact bridge: any abstract carrier
whose Palm law is the recoded legal Palm of the reserve inherits membership in
the bounded second-moment class.  Supplying the carrier itself (the marked-cloud
scene and its Campbell data) remains the open Poisson construction.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
  Matrix Module Manifold OTSelector.PointProcess OTSelector.Geometry
  ContinuousFinslerNorm OTSelector.Probability
open scoped Topology ContDiff BigOperators Matrix.Norms.Operator

noncomputable section

namespace OTSelector.PointProcess

open StationaryForwardMatching

variable {α β : Measure UnitMark}

/-! ## Per-matching Palm-energy bounds from almost-everywhere closeness -/

/-- Difference of two weighted kinetic Palm means under an almost-everywhere
coefficient bound on the Palm law. -/
theorem abs_palmKinetic_sub_le_of_ae_coefficient_bound
    {A A' : ℝ → ℝ → ℝ} {M : StationaryForwardMatching α β} {C ε : ℝ}
    (hM : FiniteSecondMoment M)
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A p.1.1 p.2.1))
    (hA_meas' : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A' p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hA_nonneg' : ∀ a b, 0 ≤ A' a b) (hA_bound' : ∀ a b, A' a b ≤ C)
    (hae : ∀ᵐ p ∂M.palm, |A p.1.1 p.2.1 - A' p.1.1 p.2.1| ≤ ε) :
    |palmKinetic A M - palmKinetic A' M| ≤
      ε / 2 * ∫ p, edgeDisplacement p ^ 2 ∂M.palm := by
  have hInt : Integrable (kineticIntegrand A) M.palm :=
    finiteSecondMoment_subset_finiteWeightedKinetic (C := C) hA_meas hA_nonneg
      hA_bound hM
  have hInt' : Integrable (kineticIntegrand A') M.palm :=
    finiteSecondMoment_subset_finiteWeightedKinetic (C := C) hA_meas' hA_nonneg'
      hA_bound' hM
  have hsub : palmKinetic A M - palmKinetic A' M =
      ∫ p, (kineticIntegrand A p - kineticIntegrand A' p) ∂M.palm := by
    unfold palmKinetic
    rw [integral_sub hInt hInt']
  have hnorm : |∫ p, (kineticIntegrand A p - kineticIntegrand A' p) ∂M.palm| ≤
      ∫ p, |kineticIntegrand A p - kineticIntegrand A' p| ∂M.palm := by
    have h := norm_integral_le_integral_norm
      (μ := M.palm) (f := fun p ↦ kineticIntegrand A p - kineticIntegrand A' p)
    simpa only [Real.norm_eq_abs] using h
  have hmono : (∫ p, |kineticIntegrand A p - kineticIntegrand A' p| ∂M.palm) ≤
      ∫ p, ε / 2 * edgeDisplacement p ^ 2 ∂M.palm := by
    apply integral_mono_ae (hInt.sub hInt').norm (hM.const_mul (ε / 2))
    filter_upwards [hae] with p hp
    have hp' : |kineticIntegrand A p - kineticIntegrand A' p| ≤
        ε / 2 * edgeDisplacement p ^ 2 := by
      have hD : 0 ≤ edgeDisplacement p ^ 2 := sq_nonneg _
      have hrew : kineticIntegrand A p - kineticIntegrand A' p =
          (1 / 2) * (A p.1.1 p.2.1 - A' p.1.1 p.2.1) * edgeDisplacement p ^ 2 := by
        unfold kineticIntegrand
        ring
      rw [hrew, abs_mul, abs_mul, abs_of_nonneg hD,
        show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
      calc (1 / 2) * |A p.1.1 p.2.1 - A' p.1.1 p.2.1| * edgeDisplacement p ^ 2
          ≤ (1 / 2) * ε * edgeDisplacement p ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hD
            exact mul_le_mul_of_nonneg_left hp (by norm_num)
        _ = ε / 2 * edgeDisplacement p ^ 2 := by ring
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hp'
  have hconst : (∫ p, ε / 2 * edgeDisplacement p ^ 2 ∂M.palm) =
      ε / 2 * ∫ p, edgeDisplacement p ^ 2 ∂M.palm :=
    integral_const_mul _ _
  rw [hsub]
  calc |∫ p, (kineticIntegrand A p - kineticIntegrand A' p) ∂M.palm|
      ≤ ∫ p, |kineticIntegrand A p - kineticIntegrand A' p| ∂M.palm := hnorm
    _ ≤ ∫ p, ε / 2 * edgeDisplacement p ^ 2 ∂M.palm := hmono
    _ = ε / 2 * ∫ p, edgeDisplacement p ^ 2 ∂M.palm := hconst

/-- Difference of two bounded measurable probe Palm means under an
almost-everywhere probe bound on the Palm law. -/
theorem abs_palmProbe_sub_le_of_ae_bound
    {f f' : MarkedCloudPoint → MarkedCloudPoint → ℝ}
    {M : StationaryForwardMatching α β} {G ε : ℝ}
    (hf_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2))
    (hf_meas' : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f' p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G) (hfG' : ∀ x y, |f' x y| ≤ G)
    (hae : ∀ᵐ p ∂M.palm, |f p.1 p.2 - f' p.1 p.2| ≤ ε) :
    |palmProbe f M - palmProbe f' M| ≤ ε := by
  let _ : IsProbabilityMeasure M.palm := M.palm_isProbability
  have hInt : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2)
      M.palm :=
    Integrable.of_bound hf_meas.aestronglyMeasurable G (Eventually.of_forall
      (fun p ↦ by rw [Real.norm_eq_abs]; exact hfG p.1 p.2))
  have hInt' : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f' p.1 p.2)
      M.palm :=
    Integrable.of_bound hf_meas'.aestronglyMeasurable G (Eventually.of_forall
      (fun p ↦ by rw [Real.norm_eq_abs]; exact hfG' p.1 p.2))
  have hsub : palmProbe f M - palmProbe f' M =
      ∫ p, (f p.1 p.2 - f' p.1 p.2) ∂M.palm := by
    unfold palmProbe
    rw [integral_sub hInt hInt']
  have hpalm : (∫ _ : MarkedCloudPoint × MarkedCloudPoint, ε ∂M.palm) = ε := by
    rw [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one,
      one_mul]
  have hnorm : |∫ p, (f p.1 p.2 - f' p.1 p.2) ∂M.palm| ≤
      ∫ p, |f p.1 p.2 - f' p.1 p.2| ∂M.palm := by
    have h := norm_integral_le_integral_norm
      (μ := M.palm) (f := fun p ↦ f p.1 p.2 - f' p.1 p.2)
    simpa only [Real.norm_eq_abs] using h
  have hmono : (∫ p, |f p.1 p.2 - f' p.1 p.2| ∂M.palm) ≤
      ∫ _ : MarkedCloudPoint × MarkedCloudPoint, ε ∂M.palm := by
    apply integral_mono_ae (hInt.sub hInt').norm (integrable_const ε)
    filter_upwards [hae] with p hp
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hp
  rw [hsub]
  calc |∫ p, (f p.1 p.2 - f' p.1 p.2) ∂M.palm|
      ≤ ∫ p, |f p.1 p.2 - f' p.1 p.2| ∂M.palm := hnorm
    _ ≤ ∫ _ : MarkedCloudPoint × MarkedCloudPoint, ε ∂M.palm := hmono
    _ = ε := hpalm

/-! ## Window-supported stationary classes -/

/-- Stationary matchings whose Palm law is supported in a fixed marked-pair
window `T` and whose unweighted displacement second moment is bounded by `B`.
On this class the window-restricted coefficient/probe regularity suffices. -/
def forwardWindowClass (T : Set (MarkedCloudPoint × MarkedCloudPoint)) (B : ℝ) :
    Set (StationaryForwardMatching α β) :=
  {M | FiniteSecondMoment M ∧ (∀ᵐ p ∂M.palm, p ∈ T) ∧
    ∫ p, edgeDisplacement p ^ 2 ∂M.palm ≤ B}

/-- Uniform convergence of the concrete forward kinetic and probe families on a
window-supported class, from window-restricted coefficient convergence and
sample-restricted probe convergence.  No global coefficient/probe convergence is
needed: on the supported class the a.e. bounds apply. -/
theorem stationaryForward_kineticProbe_uniform_convergence_on_window
    {Z : Type*} [TopologicalSpace Z]
    {T : Set (MarkedCloudPoint × MarkedCloudPoint)}
    {S : Set (ℝ × ℝ)} (hheight : ∀ p ∈ T, (p.1.1, p.2.1) ∈ S)
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {C G B : ℝ}
    (hA_meas : ∀ (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A j z p.1.1 p.2.1))
    (hA_nonneg : ∀ (j : ℕ) (z : Z) a b, 0 ≤ A j z a b)
    (hA_bound : ∀ (j : ℕ) (z : Z) a b, A j z a b ≤ C)
    (hf_meas : ∀ (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f j z p.1 p.2))
    (hfG : ∀ (j : ℕ) (z : Z) x y, |f j z x y| ≤ G)
    (hA_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ s ∈ S,
      |A j z s.1 s.2 - A j z₀ s.1 s.2| ≤ ε)
    (hf_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ q ∈ T,
      |f j z q.1 q.2 - f j z₀ q.1 q.2| ≤ ε)
    (j : ℕ) (z₀ : Z) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ M ∈ forwardWindowClass (α := α) (β := β) T B,
        |stationaryForwardKineticFamily α β A j z M -
          stationaryForwardKineticFamily α β A j z₀ M| ≤ ε ∧
        |stationaryForwardProbeFamily α β f j z M -
          stationaryForwardProbeFamily α β f j z₀ M| ≤ ε := by
  intro ε hε
  have hBpos : (0 : ℝ) < |B| + 1 := by
    have := abs_nonneg B
    linarith
  have hηpos : 0 < 2 * ε / (|B| + 1) := div_pos (by linarith) hBpos
  filter_upwards [hf_conv j z₀ ε hε, hA_conv j z₀ (2 * ε / (|B| + 1)) hηpos]
    with z hfz hAz
  intro M hM
  obtain ⟨hM2, hsupp, hMB⟩ := hM
  have hS0 : 0 ≤ ∫ p, edgeDisplacement p ^ 2 ∂M.palm :=
    integral_nonneg (fun p ↦ sq_nonneg _)
  have hB0 : 0 ≤ B := hS0.trans hMB
  have hratio : B / (|B| + 1) ≤ 1 := by
    have habs : |B| = B := abs_of_nonneg hB0
    rw [habs, div_le_one (by linarith)]
    linarith
  constructor
  · have hae : ∀ᵐ p ∂M.palm,
        |A j z p.1.1 p.2.1 - A j z₀ p.1.1 p.2.1| ≤ 2 * ε / (|B| + 1) :=
      hsupp.mono (fun p hp ↦ hAz (p.1.1, p.2.1) (hheight p hp))
    have hbound := abs_palmKinetic_sub_le_of_ae_coefficient_bound
      (C := C) hM2 (hA_meas j z) (hA_meas j z₀) (hA_nonneg j z)
      (hA_bound j z) (hA_nonneg j z₀) (hA_bound j z₀) hae
    have hηhalf : (2 * ε / (|B| + 1)) / 2 = ε / (|B| + 1) := by
      field_simp
    have hstep : (2 * ε / (|B| + 1)) / 2 *
        ∫ p, edgeDisplacement p ^ 2 ∂M.palm ≤ ε := by
      rw [hηhalf]
      have h1 : ε / (|B| + 1) * ∫ p, edgeDisplacement p ^ 2 ∂M.palm ≤
          ε / (|B| + 1) * B := by
        apply mul_le_mul_of_nonneg_left hMB
        positivity
      have h2 : ε / (|B| + 1) * B = ε * (B / (|B| + 1)) := by ring
      have h3 : ε * (B / (|B| + 1)) ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left hratio hε.le
      linarith
    simpa only [stationaryForwardKineticFamily] using hbound.trans hstep
  · have hae : ∀ᵐ p ∂M.palm, |f j z p.1 p.2 - f j z₀ p.1 p.2| ≤ ε :=
      hsupp.mono (fun p hp ↦ hfz p hp)
    simpa only [stationaryForwardProbeFamily] using
      abs_palmProbe_sub_le_of_ae_bound (M := M) (hf_meas j z) (hf_meas j z₀)
        (hfG j z) (hfG j z₀) hae

/-- The two refinement hypotheses hold for the concrete forward families on every
window-supported class: the class is root-independent (hclass) and the energies
converge uniformly on it (hconv). -/
theorem stationaryForward_hclass_hconv_on_window
    {Z : Type*} [TopologicalSpace Z]
    {T : Set (MarkedCloudPoint × MarkedCloudPoint)}
    {S : Set (ℝ × ℝ)} (hheight : ∀ p ∈ T, (p.1.1, p.2.1) ∈ S)
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {C G B : ℝ}
    (hA_meas : ∀ (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A j z p.1.1 p.2.1))
    (hA_nonneg : ∀ (j : ℕ) (z : Z) a b, 0 ≤ A j z a b)
    (hA_bound : ∀ (j : ℕ) (z : Z) a b, A j z a b ≤ C)
    (hf_meas : ∀ (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f j z p.1 p.2))
    (hfG : ∀ (j : ℕ) (z : Z) x y, |f j z x y| ≤ G)
    (hA_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ s ∈ S,
      |A j z s.1 s.2 - A j z₀ s.1 s.2| ≤ ε)
    (hf_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ q ∈ T,
      |f j z q.1 q.2 - f j z₀ q.1 q.2| ≤ ε) :
    (∀ (j : ℕ) (z₀ : Z), ∀ᶠ z in 𝓝 z₀,
        (fun _ _ ↦ forwardWindowClass (α := α) (β := β) T B) j z =
          (fun _ _ ↦ forwardWindowClass (α := α) (β := β) T B) j z₀) ∧
      (∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
        ∀ w ∈ (fun _ _ ↦ forwardWindowClass (α := α) (β := β) T B) j z₀,
          |stationaryForwardKineticFamily α β A j z w -
            stationaryForwardKineticFamily α β A j z₀ w| ≤ ε ∧
          |stationaryForwardProbeFamily α β f j z w -
            stationaryForwardProbeFamily α β f j z₀ w| ≤ ε) := by
  refine ⟨fun j z₀ ↦ ?_, fun j z₀ ↦ ?_⟩
  · filter_upwards with z
    rfl
  · intro ε hε
    exact stationaryForward_kineticProbe_uniform_convergence_on_window hheight
      A f hA_meas hA_nonneg hA_bound hf_meas hfG hA_conv hf_conv j z₀ ε hε

end OTSelector.PointProcess

/-! ## Local pressure continuity on window-supported classes -/

namespace OTSelector.Reconstruction

open OTSelector.PointProcess.StationaryForwardMatching

/-- Local pressure continuity of the actual forward stationary pressure family on
every window-supported class: the window-restricted coefficient and probe
regularity suffices, because the class is Palm-supported in the window. -/
theorem continuousOn_stationaryForwardPressureFamily_on_window
    {Z : Type*} [TopologicalSpace Z]
    {α β : Measure UnitMark}
    {T : Set (PointProcess.MarkedCloudPoint × PointProcess.MarkedCloudPoint)}
    {S : Set (ℝ × ℝ)} (hheight : ∀ p ∈ T, (p.1.1, p.2.1) ∈ S)
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → PointProcess.MarkedCloudPoint → PointProcess.MarkedCloudPoint → ℝ)
    {C G B : ℝ} (hG : 0 ≤ G)
    (hA_meas : ∀ (j : ℕ) (z : Z), Measurable
      (fun p : PointProcess.MarkedCloudPoint × PointProcess.MarkedCloudPoint ↦
        A j z p.1.1 p.2.1))
    (hA_nonneg : ∀ (j : ℕ) (z : Z) a b, 0 ≤ A j z a b)
    (hA_bound : ∀ (j : ℕ) (z : Z) a b, A j z a b ≤ C)
    (hf_meas : ∀ (j : ℕ) (z : Z), Measurable
      (fun p : PointProcess.MarkedCloudPoint × PointProcess.MarkedCloudPoint ↦
        f j z p.1 p.2))
    (hfG : ∀ (j : ℕ) (z : Z) x y, |f j z x y| ≤ G)
    (hA_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ s ∈ S,
      |A j z s.1 s.2 - A j z₀ s.1 s.2| ≤ ε)
    (hf_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ q ∈ T,
      |f j z q.1 q.2 - f j z₀ q.1 q.2| ≤ ε)
    (hne : (PointProcess.forwardWindowClass (α := α) (β := β) T B).Nonempty)
    (j : ℕ) (Kcore : Set Z) :
    ContinuousOn (fun p : Z × ℝ ↦ stationaryPressureFamily
      (PointProcess.stationaryForwardKineticFamily α β A)
      (PointProcess.stationaryForwardProbeFamily α β f)
      (fun _ _ ↦ PointProcess.forwardWindowClass (α := α) (β := β) T B)
      j p.1 p.2) (Kcore ×ˢ univ) := by
  apply continuousOn_stationaryPressureFamily_of_uniform_convergence
    (K := PointProcess.stationaryForwardKineticFamily α β A)
    (P := PointProcess.stationaryForwardProbeFamily α β f)
    (Cw := fun _ _ ↦ PointProcess.forwardWindowClass (α := α) (β := β) T B)
    (G := G)
  · exact hG
  · intro j z
    exact hne
  · intro j z w _
    exact PointProcess.StationaryForwardMatching.palmKinetic_nonneg
      (hA_nonneg j z) w
  · intro j z w _
    exact PointProcess.StationaryForwardMatching.abs_palmProbe_le
      (hf_meas j z) (hfG j z) w
  · intro j z₀
    filter_upwards with z
    rfl
  · intro j z₀ ε hε
    have h := PointProcess.stationaryForward_kineticProbe_uniform_convergence_on_window
      (α := α) (β := β) (B := B) hheight A f hA_meas hA_nonneg hA_bound
      hf_meas hfG hA_conv hf_conv j z₀ ε hε
    filter_upwards [h] with z hz
    intro w hw
    exact hz w hw

/-! ## The legal Poisson Palm as bridge data for the forward carrier -/

/-- The zero label of the unit mark interval. -/
def legalUnitMarkZero : UnitMark := ⟨0, by norm_num⟩

/-- Canonical recoding of a legal Palm pair `((a,b), v)` to an abstract marked
pair of heights, with the zero unit mark at both endpoints. -/
def legalPairToMarkedPair {q : ℕ} (m : PhysicalPairPalmMark (Fin q)) :
    MarkedCloudPoint × MarkedCloudPoint :=
  ((m.1.1, legalUnitMarkZero), (m.1.2, legalUnitMarkZero))

/-- The recoded abstract displacement is the difference of the two original
continuous clocks. -/
theorem edgeDisplacement_legalPairToMarkedPair {q : ℕ}
    (m : PhysicalPairPalmMark (Fin q)) :
    edgeDisplacement (legalPairToMarkedPair m) = m.1.2 - m.1.1 := rfl

/-- The finite-second-moment reserve packaged as a probability Palm law with
finite displacement second moment in the legal Poisson pipeline (zero probe). -/
theorem exists_legalPalm_finiteSecondMoment
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {F : ContinuousFinslerNorm E M} {u : M → ℝ}
    {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) :
    ∃ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) (fun _ _ ↦ (0 : ℝ)),
      IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      Integrable (fun m ↦ ‖m.2‖ ^ 2)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  obtain ⟨Q, hQ⟩ := D.exists_original_focal_finiteSecondMoment_stationaryMatching
    hF hw hq hgap hbounds π hπ horder (G := 0) (g := fun _ _ ↦ 0) measurable_const
    (fun _ _ ↦ by simp)
  exact ⟨Q, Q.palm_probability, hQ⟩

/-- Nonemptiness of the bounded second-moment class from any abstract forward
carrier with a finite, bounded second-moment Palm law. -/
theorem nonempty_boundedSecondMomentClass_of_carrier
    {α β : Measure UnitMark} (M : StationaryForwardMatching α β) (B : ℝ)
    (hM : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
      edgeDisplacement p ^ 2) M.palm)
    (hB : ∫ p, edgeDisplacement p ^ 2 ∂M.palm ≤ B) :
    (PointProcess.StationaryForwardMatching.boundedSecondMomentClass
      (α := α) (β := β) B).Nonempty :=
  carrier_boundedSecondMoment_nonempty M B hM hB

/-- The bridge from the legal Poisson reserve to the abstract carrier class: if an
abstract forward carrier has the recoded legal reserve Palm as its Palm law, and
the abstract displacement second moment is finite and bounded on it, then the
abstract bounded second-moment class is nonempty. -/
theorem nonempty_boundedSecondMomentClass_of_legalPalm
    {q : ℕ} {α β : Measure UnitMark}
    {α' β' : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : StationaryForwardMatching α β)
    (Q : LegalWeightedStationaryPoissonMatching q α' β' kin g)
    (_hMpalm : M.palm = (legalMarkedJointPalm q Q.law).map legalPairToMarkedPair)
    (B : ℝ)
    (hM : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦
      edgeDisplacement p ^ 2) M.palm)
    (hB : ∫ p, edgeDisplacement p ^ 2 ∂M.palm ≤ B) :
    (PointProcess.StationaryForwardMatching.boundedSecondMomentClass
      (α := α) (β := β) B).Nonempty :=
  nonempty_boundedSecondMomentClass_of_carrier M B hM hB

end OTSelector.Reconstruction

end
