import OTSelector.PointProcess.StationaryForwardMatching
import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality
import OTSelector.Reconstruction.FinslerOriginalFiniteRootPartitionRefinement

/-!
# Continuity hypotheses for the concrete forward stationary classes

`FinslerOriginalFiniteRootPartitionRefinement` derives the local pressure
continuity of the stationary pressure family from two hypotheses on the
candidate data:

* `hclass`: local constancy of the stationary classes `Cw j z`, and
* `hconv`: uniform convergence, on those classes, of the kinetic and probe
  energies `K j z` and `P j z` as the root `z` tends to `z₀`.

This file discharges them for the concrete forward stationary families
`stationaryForwardKineticFamily`, `stationaryForwardProbeFamily` and
`stationaryForwardWeightedClass`:

* `hclass` holds for the actual weighted class `C_w` under a uniformly elliptic
  calibrated coefficient: there the weighted class coincides with the
  unweighted second-moment class (`weightedClass_eq_secondMomentClass_of_uniform_elliptic`),
  which does not depend on the root.
* the probe part of `hconv` holds for every stationary matching, uniformly, from
  uniform convergence of the probe family alone, because the Palm law is a
  probability measure.
* the kinetic part of `hconv` holds uniformly on every class of stationary
  matchings with a uniform unweighted second-moment bound `B`; the explicit
  bound is `2ε/(|B|+1)` on the coefficient family.  Uniform convergence over the
  whole weighted class is impossible without a second-moment bound, since the
  difference of two kinetic Palm means is controlled by the second moment,
  which is unbounded on `C_w`.

The capstone `continuousOn_stationaryForwardPressureFamily` feeds the discharged
hypotheses into
`continuousOn_stationaryPressureFamily_of_uniform_convergence` and obtains joint
continuity of the actual forward stationary pressure family on the bounded
second-moment class, closing the local pressure sub-gap on every uniformly
second-moment-bounded stationary subclass.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators

noncomputable section

namespace OTSelector.PointProcess
namespace StationaryForwardMatching

variable {α β : Measure UnitMark}

/-- The subclass of stationary forward matchings with a uniform unweighted
displacement second-moment bound `B`. -/
def boundedSecondMomentClass (B : ℝ) : Set (StationaryForwardMatching α β) :=
  {M | FiniteSecondMoment M ∧ ∫ p, edgeDisplacement p ^ 2 ∂M.palm ≤ B}

/-- Difference of two weighted kinetic Palm means under a uniformly close
calibrated coefficient: it is at most half the coefficient error times the
unweighted displacement second moment. -/
theorem abs_palmKinetic_sub_le_of_uniform_coefficient
    {A A' : ℝ → ℝ → ℝ} {M : StationaryForwardMatching α β} {C ε : ℝ}
    (hM : FiniteSecondMoment M)
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A p.1.1 p.2.1))
    (hA_meas' : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A' p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hA_nonneg' : ∀ a b, 0 ≤ A' a b) (hA_bound' : ∀ a b, A' a b ≤ C)
    (hdiff : ∀ a b, |A a b - A' a b| ≤ ε) :
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
  have hpoint : ∀ p : MarkedCloudPoint × MarkedCloudPoint,
      |kineticIntegrand A p - kineticIntegrand A' p| ≤
        ε / 2 * edgeDisplacement p ^ 2 := by
    intro p
    have hD : 0 ≤ edgeDisplacement p ^ 2 := sq_nonneg _
    have habs := hdiff p.1.1 p.2.1
    have hrew : kineticIntegrand A p - kineticIntegrand A' p =
        (1 / 2) * (A p.1.1 p.2.1 - A' p.1.1 p.2.1) * edgeDisplacement p ^ 2 := by
      unfold kineticIntegrand
      ring
    rw [hrew, abs_mul, abs_mul, abs_of_nonneg hD,
      show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
    calc (1 / 2) * |A p.1.1 p.2.1 - A' p.1.1 p.2.1| * edgeDisplacement p ^ 2
        ≤ (1 / 2) * ε * edgeDisplacement p ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hD
          exact mul_le_mul_of_nonneg_left habs (by norm_num)
      _ = ε / 2 * edgeDisplacement p ^ 2 := by ring
  have hnorm : |∫ p, (kineticIntegrand A p - kineticIntegrand A' p) ∂M.palm| ≤
      ∫ p, |kineticIntegrand A p - kineticIntegrand A' p| ∂M.palm := by
    have h := norm_integral_le_integral_norm
      (μ := M.palm) (f := fun p ↦ kineticIntegrand A p - kineticIntegrand A' p)
    simpa only [Real.norm_eq_abs] using h
  have hmono : (∫ p, |kineticIntegrand A p - kineticIntegrand A' p| ∂M.palm) ≤
      ∫ p, ε / 2 * edgeDisplacement p ^ 2 ∂M.palm := by
    apply integral_mono_ae (hInt.sub hInt').norm (hM.const_mul (ε / 2))
    exact Eventually.of_forall hpoint
  have hconst : (∫ p, ε / 2 * edgeDisplacement p ^ 2 ∂M.palm) =
      ε / 2 * ∫ p, edgeDisplacement p ^ 2 ∂M.palm :=
    integral_const_mul _ _
  rw [hsub]
  calc |∫ p, (kineticIntegrand A p - kineticIntegrand A' p) ∂M.palm|
      ≤ ∫ p, |kineticIntegrand A p - kineticIntegrand A' p| ∂M.palm := hnorm
    _ ≤ ∫ p, ε / 2 * edgeDisplacement p ^ 2 ∂M.palm := hmono
    _ = ε / 2 * ∫ p, edgeDisplacement p ^ 2 ∂M.palm := hconst

/-- Difference of two bounded measurable probe Palm means under a uniformly
close probe: it is at most the probe error, uniformly over all stationary
matchings, because the Palm law is a probability measure. -/
theorem abs_palmProbe_sub_le_of_uniform
    {f f' : MarkedCloudPoint → MarkedCloudPoint → ℝ}
    {M : StationaryForwardMatching α β} {G ε : ℝ}
    (hf_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f p.1 p.2))
    (hf_meas' : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f' p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G) (hfG' : ∀ x y, |f' x y| ≤ G)
    (hdiff : ∀ x y, |f x y - f' x y| ≤ ε) :
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
    exact Eventually.of_forall (fun p ↦ by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hdiff p.1 p.2)
  rw [hsub]
  calc |∫ p, (f p.1 p.2 - f' p.1 p.2) ∂M.palm|
      ≤ ∫ p, |f p.1 p.2 - f' p.1 p.2| ∂M.palm := hnorm
    _ ≤ ∫ _ : MarkedCloudPoint × MarkedCloudPoint, ε ∂M.palm := hmono
    _ = ε := hpalm

end StationaryForwardMatching
end OTSelector.PointProcess

namespace OTSelector.PointProcess
open StationaryForwardMatching

variable {α β : Measure UnitMark}

/-- Uniform convergence of the concrete forward kinetic and probe families on a
uniformly second-moment-bounded stationary subclass: for every root accuracy,
eventually in the root, both Palm energies differ from their values at the limit
root by at most the accuracy, uniformly over the subclass. -/
theorem stationaryForward_kineticProbe_uniform_convergence
    {Z : Type*} [TopologicalSpace Z]
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
    (hA_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ a b,
      |A j z a b - A j z₀ a b| ≤ ε)
    (hf_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ x y,
      |f j z x y - f j z₀ x y| ≤ ε)
    (j : ℕ) (z₀ : Z) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
      ∀ M ∈ boundedSecondMomentClass (α := α) (β := β) B,
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
  obtain ⟨hM2, hMB⟩ := hM
  have hS0 : 0 ≤ ∫ p, edgeDisplacement p ^ 2 ∂M.palm :=
    integral_nonneg (fun p ↦ sq_nonneg _)
  have hB0 : 0 ≤ B := hS0.trans hMB
  have hratio : B / (|B| + 1) ≤ 1 := by
    have habs : |B| = B := abs_of_nonneg hB0
    rw [habs, div_le_one (by linarith)]
    linarith
  constructor
  · have hbound := abs_palmKinetic_sub_le_of_uniform_coefficient (C := C) hM2
      (hA_meas j z) (hA_meas j z₀) (hA_nonneg j z) (hA_bound j z)
      (hA_nonneg j z₀) (hA_bound j z₀) hAz
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
  · simpa only [stationaryForwardProbeFamily] using
      abs_palmProbe_sub_le_of_uniform (M := M) (hf_meas j z) (hf_meas j z₀)
        (hfG j z) (hfG j z₀) hfz

/-- Local constancy of the actual weighted stationary class under a uniformly
elliptic calibrated coefficient: the weighted class and the unweighted
second-moment class coincide, so the class does not depend on the root. -/
theorem stationaryForwardWeightedClass_eventually_eq
    {Z : Type*} [TopologicalSpace Z]
    (A : ℕ → Z → ℝ → ℝ → ℝ) {c C : ℝ} (hc : 0 < c)
    (hA_meas : ∀ (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A j z p.1.1 p.2.1))
    (hA_low : ∀ j z a b, c ≤ A j z a b)
    (hA_bound : ∀ (j : ℕ) (z : Z) a b, A j z a b ≤ C)
    (j : ℕ) (z₀ : Z) :
    ∀ᶠ z in 𝓝 z₀,
      stationaryForwardWeightedClass α β A j z =
        stationaryForwardWeightedClass α β A j z₀ := by
  filter_upwards with z
  simp only [stationaryForwardWeightedClass]
  rw [weightedClass_eq_secondMomentClass_of_uniform_elliptic (hA_meas j z) hc
      (hA_low j z) (hA_bound j z),
    weightedClass_eq_secondMomentClass_of_uniform_elliptic (hA_meas j z₀) hc
      (hA_low j z₀) (hA_bound j z₀)]

/-- The two refinement hypotheses for the concrete forward families on the
uniformly second-moment-bounded subclass: the class family is constant in the
root (hclass) and the kinetic/probe energies converge uniformly on it (hconv). -/
theorem stationaryForward_boundedClass_hclass_hconv
    {Z : Type*} [TopologicalSpace Z]
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
    (hA_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ a b,
      |A j z a b - A j z₀ a b| ≤ ε)
    (hf_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ x y,
      |f j z x y - f j z₀ x y| ≤ ε) :
    (∀ j (z₀ : Z), ∀ᶠ z in 𝓝 z₀,
        (fun (_ : ℕ) (_ : Z) ↦ boundedSecondMomentClass (α := α) (β := β) B) j z =
          (fun (_ : ℕ) (_ : Z) ↦ boundedSecondMomentClass (α := α) (β := β) B) j z₀) ∧
      (∀ j (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀,
        ∀ w ∈ (fun (_ : ℕ) (_ : Z) ↦ boundedSecondMomentClass (α := α) (β := β) B) j z₀,
          |stationaryForwardKineticFamily α β A j z w -
            stationaryForwardKineticFamily α β A j z₀ w| ≤ ε ∧
          |stationaryForwardProbeFamily α β f j z w -
            stationaryForwardProbeFamily α β f j z₀ w| ≤ ε) := by
  refine ⟨fun j z₀ ↦ ?_, fun j z₀ ↦ ?_⟩
  · filter_upwards with z
    rfl
  · intro ε hε
    exact stationaryForward_kineticProbe_uniform_convergence A f hA_meas hA_nonneg
      hA_bound hf_meas hfG hA_conv hf_conv j z₀ ε hε

end OTSelector.PointProcess

namespace OTSelector.Reconstruction

open OTSelector.PointProcess

/-- Local pressure continuity for the actual forward stationary pressure family
on every uniformly second-moment-bounded stationary subclass: the refinement
hypotheses hclass/hconv are discharged for the concrete forward kinetic, probe
and class families, so the stationary pressure family
`stationaryPressureFamily K P Cw j` is jointly continuous in the root and the
tilt on any core times the full tilt line. -/
theorem continuousOn_stationaryForwardPressureFamily
    {Z : Type*} [TopologicalSpace Z]
    {α β : Measure UnitMark}
    (A : ℕ → Z → ℝ → ℝ → ℝ)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {C G B : ℝ} (hG : 0 ≤ G)
    (hA_meas : ∀ (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ A j z p.1.1 p.2.1))
    (hA_nonneg : ∀ (j : ℕ) (z : Z) a b, 0 ≤ A j z a b)
    (hA_bound : ∀ (j : ℕ) (z : Z) a b, A j z a b ≤ C)
    (hf_meas : ∀ (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ f j z p.1 p.2))
    (hfG : ∀ (j : ℕ) (z : Z) x y, |f j z x y| ≤ G)
    (hA_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ a b,
      |A j z a b - A j z₀ a b| ≤ ε)
    (hf_conv : ∀ (j : ℕ) (z₀ : Z), ∀ ε > 0, ∀ᶠ z in 𝓝 z₀, ∀ x y,
      |f j z x y - f j z₀ x y| ≤ ε)
    (hne : (PointProcess.StationaryForwardMatching.boundedSecondMomentClass
        (α := α) (β := β) B).Nonempty)
    (j : ℕ) (Kcore : Set Z) :
    ContinuousOn (fun p : Z × ℝ ↦ stationaryPressureFamily
      (PointProcess.stationaryForwardKineticFamily α β A)
      (PointProcess.stationaryForwardProbeFamily α β f)
      (fun _ _ ↦ PointProcess.StationaryForwardMatching.boundedSecondMomentClass
        (α := α) (β := β) B) j p.1 p.2) (Kcore ×ˢ univ) := by
  apply continuousOn_stationaryPressureFamily_of_uniform_convergence
    (K := PointProcess.stationaryForwardKineticFamily α β A)
    (P := PointProcess.stationaryForwardProbeFamily α β f)
    (Cw := fun _ _ ↦
      PointProcess.StationaryForwardMatching.boundedSecondMomentClass
        (α := α) (β := β) B)
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
    have h := PointProcess.stationaryForward_kineticProbe_uniform_convergence
      (α := α) (β := β) (B := B) A f hA_meas hA_nonneg hA_bound hf_meas hfG
      hA_conv hf_conv j z₀ ε hε
    filter_upwards [h] with z hz
    intro w hw
    exact hz w hw

end OTSelector.Reconstruction

end
