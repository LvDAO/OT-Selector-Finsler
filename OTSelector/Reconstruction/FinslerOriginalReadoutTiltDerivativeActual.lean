import OTSelector.Reconstruction.FinslerOriginalGeneralSelectorParameterized
import OTSelector.Reconstruction.FinslerOriginalShiftedReadoutBridge
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The readout tilt derivative of the actual lane

The parameterized final selector uses the single named input
FinslerReadoutTiltDerivative: the limiting lower pressure is differentiable in
the tilt at zero, for every probe.  This module produces that input from the
paper's readout identification of the stationary value.

## What is proved

1. **The kinetic squeeze derivative.**  For a stationary value
I(v) = inf over an admissible class of (K c + v P c), the derivative at zero is
the probe readout p of the kinetic near-minimizers, provided every admissible
candidate that is almost kinetic-minimal has probe close to p:

  for all delta > 0 and c in the class, K c <= I(0) + delta implies
  |P c - p| <= delta.

Under this squeeze the value is differentiable at zero with derivative p.  This
is exactly the analytic content of the paper's stationary readout
identification: the tilt derivative of the stationary pressure is the bounded
mark probe readout of the kinetic minimizers, not the value itself.

2. **Attainment producers.**  If the stationary value is eventually affine in
the tilt, because on a neighbourhood of zero a fixed candidate attains the
infimum (for instance when the admissible class is a singleton), then the value
is differentiable at zero with derivative the probe of that candidate.

3. **The lane reduction.**  The probe-shifted frozen lower pressure of the
actual lane is definitionally the unshifted Campbell averaged frozen cost minus
the probe constant.  Hence FinslerReadoutTiltDerivative for the actual lane
field is exactly differentiability at zero of the frozen Campbell readout
minus the probe constant.  By the named paper bridge FrozenCampbellReadout the
unshifted frozen readout equals the weighted stationary pressure of the datum,
so the squeeze producer applies to the unshifted readout.

4. **The probe constant is not differentiable.**  The probe constant
|t| ||f|| cannot be differentiated at zero when f is nonzero: its one-sided
slopes are plus or minus ||f||.  Consequently the probe-shifted readout of an affine
stationary value is not a valid carrier of the derivative input, and the
derivative has to be taken on the unshifted readout (or the shift has to be
absorbed in a shifted datum).  This is reported as the exact remaining gap for
the shifted field.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace Asymptotics
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## 1. Stationary values: eventual affine attainment -/

/-- If the stationary value is eventually affine in the tilt around zero, then
it is differentiable at zero with derivative the probe of the affine candidate. -/
theorem hasDerivAt_stationaryValue_of_eventually_affine {C : Type*} {K P : C → ℝ}
    {admissible : Set C} {c : C}
    (h : (fun v : ℝ => stationaryValue K P admissible v) =ᶠ[𝓝 0]
      (fun v : ℝ => K c + v * P c)) :
    HasDerivAt (fun v : ℝ => stationaryValue K P admissible v) (P c) 0 := by
  have hlin : HasDerivAt (fun v : ℝ => K c + v * P c) (P c) 0 := by
    have h1 : HasDerivAt (fun v : ℝ => v * P c) (P c) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (P c)
    simpa using h1.const_add (K c)
  exact hlin.congr_of_eventuallyEq h

/-- The weighted stationary pressure of a datum is differentiable at zero when
its value is eventually affine with probe readout of a fixed matching. -/
theorem hasDerivAt_Iw_of_eventually_affine {W : Type*} {G Cb : ℝ}
    (D : StationaryPressureDatum W G Cb) {c : W}
    (h : (fun v : ℝ => D.Iw v) =ᶠ[𝓝 0] (fun v : ℝ => D.K c + v * D.P c)) :
    HasDerivAt (fun v : ℝ => D.Iw v) (D.P c) 0 :=
  hasDerivAt_stationaryValue_of_eventually_affine (K := D.K) (P := D.P)
    (admissible := D.Cw) h

/-- The stationary value of a singleton admissible class is affine. -/
theorem stationaryValue_singleton {C : Type*} (K P : C → ℝ) (c : C) (v : ℝ) :
    stationaryValue K P ({c} : Set C) v = K c + v * P c := by
  unfold stationaryValue
  rw [Set.image_singleton]
  exact csInf_singleton (K c + v * P c)

/-- If a datum has a singleton weighted class then its weighted pressure is
differentiable at zero with derivative the singleton probe. -/
theorem hasDerivAt_Iw_of_singleton {W : Type*} {G Cb : ℝ}
    (D : StationaryPressureDatum W G Cb) {c : W} (hCw : D.Cw = {c}) :
    HasDerivAt (fun v : ℝ => D.Iw v) (D.P c) 0 := by
  refine hasDerivAt_Iw_of_eventually_affine (D := D) (c := c) ?_
  have h : ∀ v : ℝ, D.Iw v = D.K c + v * D.P c := by
    intro v
    show stationaryValue D.K D.P D.Cw v = D.K c + v * D.P c
    rw [hCw]
    exact stationaryValue_singleton D.K D.P c v
  exact Filter.Eventually.of_forall h

/-! ## 2. The kinetic squeeze derivative -/

/-- **The kinetic squeeze derivative.**  If every almost kinetic-minimal
admissible candidate has mark probe close to p, then the stationary value is
differentiable at zero with derivative p. -/
theorem hasDerivAt_stationaryValue_of_kinetic_squeeze {C : Type*} {K P : C → ℝ}
    {admissible : Set C} {G p : ℝ}
    (hne : admissible.Nonempty)
    (hK : ∀ c ∈ admissible, 0 ≤ K c)
    (hP : ∀ c ∈ admissible, |P c| ≤ G) (hG : 0 ≤ G)
    (hsqueeze : ∀ δ > 0, ∀ c ∈ admissible,
      K c ≤ stationaryValue K P admissible 0 + δ → |P c - p| ≤ δ) :
    HasDerivAt (fun v : ℝ => stationaryValue K P admissible v) p 0 := by
  have h0eq : stationaryValue K P admissible 0 = sInf (K '' admissible) := by
    unfold stationaryValue
    congr 1
    ext x
    simp
  have hKmin : ∀ c ∈ admissible, stationaryValue K P admissible 0 ≤ K c := by
    intro c hc
    rw [h0eq]
    exact csInf_le ⟨0, by rintro _ ⟨d, hd, rfl⟩; exact hK d hd⟩ ⟨c, hc, rfl⟩
  have hupper : ∀ v : ℝ, stationaryValue K P admissible v ≤
      stationaryValue K P admissible 0 + v * p + v ^ 2 + |v| * v ^ 2 := by
    intro v
    rcases eq_or_ne v 0 with hv | hv
    · simp [hv]
    · have hv2 : 0 < v ^ 2 := by positivity
      have hlt0 : sInf (K '' admissible) < stationaryValue K P admissible 0 + v ^ 2 := by
        rw [h0eq]
        exact lt_add_of_pos_right _ hv2
      obtain ⟨w, hw, hlt⟩ := exists_lt_of_csInf_lt (hne.image K) hlt0
      obtain ⟨c, hc, rfl⟩ := hw
      have hPc : |P c - p| ≤ v ^ 2 := hsqueeze (v ^ 2) hv2 c hc (le_of_lt hlt)
      have hle := stationaryValue_le (v := v)
        (bddBelow_stationaryValue (G := G) (v := v) hK hP) hc
      have h1 : K c - stationaryValue K P admissible 0 ≤ v ^ 2 := by linarith
      have h2 : v * (P c - p) ≤ |v| * v ^ 2 := by
        calc v * (P c - p) ≤ |v * (P c - p)| := le_abs_self _
          _ = |v| * |P c - p| := abs_mul v (P c - p)
          _ ≤ |v| * v ^ 2 := mul_le_mul_of_nonneg_left hPc (abs_nonneg v)
      nlinarith
  set C₀ : ℝ := |p| + G + 3 with hC₀
  have hC₀pos : 0 < C₀ := by have := abs_nonneg p; linarith
  have hC₀ge : 3 ≤ C₀ := by have := abs_nonneg p; linarith
  have hlower : ∀ v : ℝ, |v| ≤ 1 → 0 < v ^ 2 →
      stationaryValue K P admissible 0 + v * p - (C₀ + 1) * v ^ 2 ≤
        stationaryValue K P admissible v := by
    intro v hv1 hv2
    have hvne : v ≠ 0 := by rintro rfl; norm_num at hv2
    obtain ⟨w, hw, hlt⟩ := exists_lt_of_csInf_lt (hne.image (fun c => K c + v * P c))
      (lt_add_of_pos_right _ hv2)
    obtain ⟨c, hc, rfl⟩ := hw
    have hlt' : K c + v * P c < stationaryValue K P admissible v + v ^ 2 := by
      simpa [stationaryValue] using hlt
    have hup := hupper v
    have hvabs : (0 : ℝ) ≤ |v| := abs_nonneg v
    have hv2le : v ^ 2 ≤ |v| := by
      nlinarith [sq_abs v, abs_nonneg v, hv1]
    have hneg : -(v * P c) ≤ |v| * G := by
      calc -(v * P c) ≤ |v * P c| := neg_le_abs _
        _ = |v| * |P c| := abs_mul v (P c)
        _ ≤ |v| * G := mul_le_mul_of_nonneg_left (hP c hc) (abs_nonneg v)
    have hvp : v * p ≤ |v| * |p| := by
      calc v * p ≤ |v * p| := le_abs_self _
        _ = |v| * |p| := abs_mul v p
    have hKc : K c ≤ stationaryValue K P admissible 0 + C₀ * |v| := by
      have hstep : stationaryValue K P admissible v + v ^ 2 - v * P c ≤
          stationaryValue K P admissible 0 + C₀ * |v| := by
        nlinarith [hup, hneg, hvp, hv2le, hvabs, abs_nonneg p, hG]
      linarith [hlt', hstep]
    have hδpos : 0 < C₀ * |v| := mul_pos hC₀pos (abs_pos.mpr hvne)
    have hPc : |P c - p| ≤ C₀ * |v| := hsqueeze (C₀ * |v|) hδpos c hc hKc
    have hKminc := hKmin c hc
    have hv2' : |v| * |v| = v ^ 2 := by rw [← sq_abs v]; ring
    have h1 : v * (P c - p) ≥ -(|v| * (C₀ * |v|)) := by
      have hle : |v| * |P c - p| ≤ |v| * (C₀ * |v|) :=
        mul_le_mul_of_nonneg_left hPc (abs_nonneg v)
      have h2 : -(|v| * |P c - p|) ≤ v * (P c - p) := by
        rw [← abs_mul]
        exact neg_abs_le _
      linarith
    have hmain : stationaryValue K P admissible 0 + v * p - (C₀ + 1) * v ^ 2 ≤
        K c + v * P c - v ^ 2 := by
      nlinarith [hKminc, h1, hv2']
    linarith
  have herr : ∀ v : ℝ, |v| ≤ 1 →
      |stationaryValue K P admissible v - stationaryValue K P admissible 0 - v * p| ≤
        (C₀ + 3) * v ^ 2 := by
    intro v hv1
    rcases eq_or_ne v 0 with hv | hv
    · simp [hv]
    · have hv2 : 0 < v ^ 2 := by positivity
      have hup := hupper v
      have hlow := hlower v hv1 hv2
      have hv2le : v ^ 2 ≤ |v| := by nlinarith [sq_abs v, abs_nonneg v, hv1]
      rw [abs_le]
      constructor <;> nlinarith [hup, hlow, hv2le, hv2, hC₀ge]
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine isLittleO_of_tendsto ?_ ?_
  · intro v hv
    subst hv
    simp
  · have hbound : ∀ᶠ v : ℝ in 𝓝 0,
        ‖(stationaryValue K P admissible (0 + v) - stationaryValue K P admissible 0 -
          v • p) / v‖ ≤ (C₀ + 3) * |v| := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with v hv1
      have hv1' : |v| ≤ 1 := by simpa [Real.dist_eq] using hv1
      rw [Real.norm_eq_abs, abs_div]
      simp only [zero_add, smul_eq_mul]
      rcases eq_or_ne v 0 with hv | hv
      · simp [hv]
      · have hv2 : 0 < v ^ 2 := by positivity
        have herr' := herr v hv1'
        have hvabs : 0 < |v| := abs_pos.mpr hv
        have hstep : |stationaryValue K P admissible v - stationaryValue K P admissible 0 - v * p| / |v| ≤
            ((C₀ + 3) * v ^ 2) / |v| := by
          gcongr
        have hsq : v ^ 2 = |v| * |v| := by rw [← sq_abs v]; ring
        have hdiv : ((C₀ + 3) * v ^ 2) / |v| = (C₀ + 3) * |v| := by
          rw [hsq]
          field_simp
        linarith
    have hlim : Tendsto (fun v : ℝ => (C₀ + 3) * |v|) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous fun v : ℝ => (C₀ + 3) * |v| :=
        continuous_const.mul continuous_abs
      simpa using hcont.tendsto 0
    exact squeeze_zero_norm' hbound hlim

/-- The weighted pressure of a datum is differentiable at zero with derivative
p as soon as the kinetic squeeze holds on its weighted class. -/
theorem hasDerivAt_Iw_of_kinetic_squeeze {W : Type*} {G Cb : ℝ}
    (D : StationaryPressureDatum W G Cb) {p : ℝ}
    (hsqueeze : ∀ δ > 0, ∀ c ∈ D.Cw, D.K c ≤ D.Iw 0 + δ → |D.P c - p| ≤ δ) :
    HasDerivAt (fun v : ℝ => D.Iw v) p 0 :=
  hasDerivAt_stationaryValue_of_kinetic_squeeze (K := D.K) (P := D.P)
    (admissible := D.Cw) (G := G) D.nonempty_Cw D.kinetic_nonneg
    D.probe_bound D.bound_nonneg hsqueeze

/-! ## 3. The affine datum witness -/

/-- The unique affine stationary datum on the one-point matching type. -/
noncomputable def affineStationaryDatum (K P : ℝ) (hK : 0 ≤ K) :
    StationaryPressureDatum PUnit |P| K where
  K := fun _ => K
  P := fun _ => P
  Cw := Set.univ
  C2 := Set.univ
  C2_subset_Cw := subset_rfl
  kinetic_nonneg := fun _ _ => hK
  probe_bound := fun _ _ => le_rfl
  competitor := PUnit.unit
  competitor_mem := Set.mem_univ _
  kinetic_competitor_le := le_rfl
  competitor2 := PUnit.unit
  competitor2_mem := Set.mem_univ _
  kinetic_competitor2_le := le_rfl

/-- The weighted pressure of the affine datum is affine in the tilt. -/
theorem affineStationaryDatum_Iw (K P : ℝ) (hK : 0 ≤ K) (v : ℝ) :
    (affineStationaryDatum K P hK).Iw v = K + v * P := by
  unfold StationaryPressureDatum.Iw
  show sInf ((fun _ : PUnit => K + v * P) '' Set.univ) = K + v * P
  rw [Set.univ_nonempty.image_const (K + v * P)]
  exact csInf_singleton (K + v * P)

/-- The affine stationary readout carries the readout tilt derivative: the
derivative input is satisfiable by a canonical stationary datum. -/
theorem finslerReadoutTiltDerivative_affineStationaryReadout {A B : Set M}
    (K P : ℝ) (hK : 0 ≤ K) :
    FinslerReadoutTiltDerivative
      (fun (_ : FinalProbeSpace A B) (t : ℝ) => (affineStationaryDatum K P hK).Iw t) := by
  refine ⟨fun _ => P, fun f => ?_⟩
  exact hasDerivAt_Iw_of_eventually_affine (D := affineStationaryDatum K P hK)
    (c := PUnit.unit)
    (Filter.Eventually.of_forall fun v => affineStationaryDatum_Iw K P hK v)

/-! ## 4. The datum family producer -/

/-- A datum family whose weighted pressure satisfies the kinetic squeeze carries
the readout tilt derivative at the probe readout p. -/
theorem finslerReadoutTiltDerivative_stationaryReadout_of_kinetic_squeeze
    {A B : Set M} {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (p : FinalProbeSpace A B → ℝ)
    (hsqueeze : ∀ f (δ : ℝ), 0 < δ → ∀ c ∈ (datum f).Cw,
      (datum f).K c ≤ (datum f).Iw 0 + δ → |(datum f).P c - p f| ≤ δ) :
    FinslerReadoutTiltDerivative (fun f t => (datum f).Iw t) :=
  ⟨p, fun f => hasDerivAt_Iw_of_kinetic_squeeze (datum f) (hsqueeze f)⟩

/-! ## 5. The lane reduction and the probe-constant gap -/

/-- **The actual lane reduction.**  The probe-shifted frozen lower pressure of
the actual lane is differentiability-equivalent to the unshifted Campbell
averaged frozen cost minus the probe constant. -/
theorem finslerReadoutTiltDerivative_frozenProbePressureLowerField_iff
    {A B : Set M} (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ) :
    FinslerReadoutTiltDerivative (frozenProbePressureLowerField Seed a κ lambda g q) ↔
      ∃ derivative : FinalProbeSpace A B → ℝ,
        ∀ f : FinalProbeSpace A B,
          HasDerivAt (fun t : ℝ =>
            campbellAveragedFrozenCost Seed a κ lambda (g f t) q - probeShift f t)
            (derivative f) 0 := by
  simp only [FinslerReadoutTiltDerivative, frozenProbePressureLowerField_apply]

/-- The probe constant t ↦ |t| * c is not differentiable at zero for c nonzero. -/
theorem not_hasDerivAt_abs_mul {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    ¬ HasDerivAt (fun t : ℝ => |t| * c) d 0 := by
  intro h
  have hright : Tendsto (fun t : ℝ => t⁻¹ * (|t| * c - |0| * c)) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    simpa [smul_eq_mul] using h.tendsto_slope_zero_right
  have hevR : (fun t : ℝ => t⁻¹ * (|t| * c - |0| * c)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => c) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have ht' : (0 : ℝ) < t := ht
    simp only [abs_of_pos ht', abs_zero, zero_mul, sub_zero]
    field_simp
  have hR : d = c := tendsto_nhds_unique hright ((tendsto_congr' hevR).mpr tendsto_const_nhds)
  have hleft : Tendsto (fun t : ℝ => t⁻¹ * (|t| * c - |0| * c)) (𝓝[<] (0 : ℝ)) (𝓝 d) := by
    simpa [smul_eq_mul] using h.tendsto_slope_zero_left
  have hevL : (fun t : ℝ => t⁻¹ * (|t| * c - |0| * c)) =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => -c) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_lt ht
    have ht' : t < 0 := ht
    simp only [abs_of_neg ht', abs_zero, zero_mul, sub_zero]
    field_simp
  have hL : d = -c := tendsto_nhds_unique hleft ((tendsto_congr' hevL).mpr tendsto_const_nhds)
  have hc0 : c = 0 := by rw [hR] at hL; linarith
  exact hc hc0

/-- A probe-shifted affine readout does not carry the readout tilt derivative
when a nonzero probe exists: the probe constant has one-sided slopes
plus or minus ||f|| at zero. -/
theorem not_finslerReadoutTiltDerivative_shiftedAffine
    {A B : Set M} (A' B' : FinalProbeSpace A B → ℝ)
    (hne : ∃ f : FinalProbeSpace A B, (‖f‖₊ : ℝ) ≠ 0) :
    ¬ FinslerReadoutTiltDerivative (fun f t => A' f + t * B' f - probeShift f t) := by
  rintro ⟨derivative, hderiv⟩
  obtain ⟨f, hf⟩ := hne
  have h := hderiv f
  have haff : HasDerivAt (fun t : ℝ => A' f + t * B' f) (B' f) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * B' f) (B' f) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (B' f)
    simpa using h1.const_add (A' f)
  have hneg : HasDerivAt
      (fun t : ℝ => (A' f + t * B' f - probeShift f t) - (A' f + t * B' f))
      (derivative f - B' f) 0 := h.sub haff
  have hfun : (fun t : ℝ => (A' f + t * B' f - probeShift f t) - (A' f + t * B' f))
      = fun t : ℝ => -(|t| * (‖f‖₊ : ℝ)) := by
    funext t
    rw [probeShift_apply]
    ring
  rw [hfun] at hneg
  have habs : HasDerivAt (fun t : ℝ => |t| * (‖f‖₊ : ℝ)) (B' f - derivative f) 0 := by
    have h1 : HasDerivAt (-(fun t : ℝ => -(|t| * (‖f‖₊ : ℝ))))
        (-(derivative f - B' f)) 0 := hneg.neg
    have h2 : (-(derivative f - B' f)) = B' f - derivative f := by ring
    have h3 : (-(fun t : ℝ => -(|t| * (‖f‖₊ : ℝ)))) = fun t : ℝ => |t| * (‖f‖₊ : ℝ) := by
      funext t
      simp
    rw [h2, h3] at h1
    exact h1
  exact not_hasDerivAt_abs_mul hf (B' f - derivative f) habs

end OTSelector.Reconstruction