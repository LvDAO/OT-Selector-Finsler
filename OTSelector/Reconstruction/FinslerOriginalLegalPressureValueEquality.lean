import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMinimizingSequence
import OTSelector.Transport.Finite.RetainedPlanRepair
import OTSelector.PointProcess.StationaryForwardMatching

/-!
# Legal pressure value identification: weighted equals second-moment

This module records the value-identification interface between the two legal
stationary pressure classes of the general Finsler selector
(main.tex, definition general-gluing-two-classes):

* the weighted class C_w of stationary forward perfect matchings with finite
  weighted kinetic mean, defining the weighted legal pressure I_w, and
* the second-moment class C_2 of stationary forward perfect matchings with
  finite unweighted displacement second moment, defining I_2.

The paper proves I_w = I_2 by legal screening/reserve construction
(prop:general-finite-path-screening, thm:general-focal-value-equality).
The present module isolates the exact logical content of that identification
and proves every part that is independent of the remaining screening analysis:

1. **Screening is equivalent to value identification.**  For an arbitrary
   value functional on a class C_2 contained in C_w, the infima over the two
   classes coincide if and only if every member of C_w is approached in value
   from above, within every positive epsilon, by a member of C_2
   (sInf_image_eq_iff_screening).  Consequently the open value input hvalue of
   FinslerGeneralSelectorAssembly is *exactly* the paper's screening statement:
   no additional analytic content is hidden in it.  A quantitative form bounds
   the pressure gap I_2 - I_w by any uniform screening budget
   (sInf_image_le_add_of_screening_le), so an explicit residual-repair estimate
   is a value-gap estimate.

2. **Uniformly elliptic coefficients give an unconditional identification.**
   When the calibrated quadratic coefficient is bounded below by a positive
   constant (the paper's interior-collar case, and the elliptic approximation
   regime), the two classes coincide: every finite weighted kinetic mean is a
   finite unweighted second moment.  Hence I_w = I_2 unconditionally
   (weightedClass_eq_secondMomentClass_of_uniform_elliptic,
   weightedStationaryPressure_eq_secondMoment_of_uniform_elliptic).  The
   identity coefficient and every positive multiple of it are instances.

3. **The actual original Poisson framework.**  On the actual original
   independent marked Poisson inputs with the literal original focal kinetic
   cost of MarkedStationaryValueLegalOriginalFocalKinetic, the second-moment
   subclass of LegalWeightedStationaryPoissonMatching is nonempty (the existing
   finite-second-moment reserve) and its value infimum I_2 obeys the
   unconditional order I_w <= I_2.  The value equality I_w = I_2 is *equivalent*
   to the reserve-screening approximation of every weighted matching by
   second-moment matchings
   (originalWeightedStationaryInf_eq_secondMomentInf_iff_screening), and a
   uniform screening budget bounds the gap
   (originalSecondMomentStationaryInf_le_weighted_add).  The constant
   rho^{-1} C^2 / 2 supplied by legalResidualRepair_absSignedValue_le is a valid
   repair budget in this sense
   (originalSecondMomentStationaryInf_le_weighted_add_repairBudget).

4. **The actual finite legal pressure bound.**  For a legal family with the
   actual finite legal graph data (scalar bins, coupling of the original input
   laws, compact supports, and a continuous positive-definite coefficient matrix
   agreeing with the kinetic cost on the legal collar), there is a limit p_A of
   the actual legal maximum-cardinality finite pressures such that
   I_w <= I_2 <= p_A at every tilt
   (exists_legalPressureLimit_ge_secondMomentInf,
   exists_legalPressureLimit_ge_weighted_le_secondMoment).  This is the
   finite-legal-graph half of the paper's equality I_w = I_2 = p_A; the missing
   half is exactly the screening property of the remaining gap.

## Remaining gap

The paper's screening proposition constructs, for every weighted stationary
matching with finite weighted energy, a finite-second-moment competitor whose
value exceeds the weighted value by an arbitrarily small amount (reserve
density rho -> 0, density dilation, whole-path traffic and the Neumann /
Benamou--Brenier transport of the residual ports).  That construction is the
only missing ingredient: items 1, 3 and 4 above show that it is exactly, and
nothing more than, the value equality I_w = I_2 (equivalently the matching upper
bound I_2 <= I_w, equivalently I_2 = p_A), while item 2 covers the uniformly
elliptic special case unconditionally.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Topology Matrix.Norms.Operator

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Screening is equivalent to the value identification -/

section ScreeningEquivalence

variable {W : Type*}

/-- The screening (value-density) property of a pair of admissible classes: every
member of the larger class is approached in value from above within every
positive tolerance by a member of the smaller class.  This is the abstract form
of the paper's legal screening approximation. -/
def ScreeningApproximates (V : W → ℝ) (Cw C2 : Set W) : Prop :=
  ∀ Q ∈ Cw, ∀ ε : ℝ, 0 < ε → ∃ Q' ∈ C2, V Q' < V Q + ε

/-- **The value identification is exactly the screening approximation.**  For
classes C_2 contained in C_w with C_2 nonempty and the larger value set bounded
below, the two infima coincide if and only if C_2 is value-dense below C_w. -/
theorem sInf_image_eq_iff_screening
    (V : W → ℝ) (Cw C2 : Set W) (hsub : C2 ⊆ Cw) (hne : C2.Nonempty)
    (hbdd : BddBelow (V '' Cw)) :
    sInf (V '' Cw) = sInf (V '' C2) ↔ ScreeningApproximates V Cw C2 := by
  have hbdd2 : BddBelow (V '' C2) := BddBelow.mono (Set.image_mono hsub) hbdd
  constructor
  · intro heq Q hQ ε hε
    have hle : sInf (V '' Cw) ≤ V Q := csInf_le hbdd ⟨Q, hQ, rfl⟩
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt (hne.image V)
      (show sInf (V '' C2) < sInf (V '' C2) + ε from lt_add_of_pos_right _ hε)
    obtain ⟨Q', hQ', hQy⟩ := hy
    refine ⟨Q', hQ', ?_⟩
    rw [← heq] at hylt
    rw [← hQy] at hylt
    linarith
  · intro hdense
    refine le_antisymm ?_ ?_
    · apply le_csInf (hne.image V)
      rintro y ⟨Q', hQ', rfl⟩
      exact csInf_le hbdd ⟨Q', hsub hQ', rfl⟩
    · refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have hneW : (V '' Cw).Nonempty := (hne.mono hsub).image V
      obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hneW
        (show sInf (V '' Cw) < sInf (V '' Cw) + ε / 2 from
          lt_add_of_pos_right _ (half_pos hε))
      obtain ⟨Q, hQ, hQy⟩ := hy
      obtain ⟨Q', hQ', hQ'lt⟩ := hdense Q hQ (ε / 2) (half_pos hε)
      have hle : sInf (V '' C2) ≤ V Q' := csInf_le hbdd2 ⟨Q', hQ', rfl⟩
      rw [← hQy] at hylt
      linarith

/-- The positive-tolerance screening property gives the exact value equality. -/
theorem sInf_image_eq_of_screening
    (V : W → ℝ) (Cw C2 : Set W) (hsub : C2 ⊆ Cw) (hne : C2.Nonempty)
    (hbdd : BddBelow (V '' Cw)) (hdense : ScreeningApproximates V Cw C2) :
    sInf (V '' Cw) = sInf (V '' C2) :=
  (sInf_image_eq_iff_screening V Cw C2 hsub hne hbdd).mpr hdense

/-- **Quantitative value identification.**  A uniform screening budget B bounds
the value gap: I_2 <= I_w + B.  In the legal setting, the budget is the explicit
residual-repair value supplied by the Neumann/transport estimate. -/
theorem sInf_image_le_add_of_screening_le
    (V : W → ℝ) (Cw C2 : Set W) (hsub : C2 ⊆ Cw) (hne : C2.Nonempty)
    (hbdd : BddBelow (V '' Cw)) {B : ℝ}
    (hscreen : ∀ Q ∈ Cw, ∃ Q' ∈ C2, V Q' ≤ V Q + B) :
    sInf (V '' C2) ≤ sInf (V '' Cw) + B := by
  have hbdd2 : BddBelow (V '' C2) := BddBelow.mono (Set.image_mono hsub) hbdd
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hneW : (V '' Cw).Nonempty := (hne.mono hsub).image V
  obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hneW
    (show sInf (V '' Cw) < sInf (V '' Cw) + ε from lt_add_of_pos_right _ hε)
  obtain ⟨Q, hQ, hQy⟩ := hy
  obtain ⟨Q', hQ', hQ'le⟩ := hscreen Q hQ
  have hle : sInf (V '' C2) ≤ V Q' := csInf_le hbdd2 ⟨Q', hQ', rfl⟩
  rw [← hQy] at hylt
  linarith

end ScreeningEquivalence

/-! ## 2. The abstract stationary pressure datum -/

section StationaryDatum

/-- The screening property is exactly the value identification for the abstract
stationary pressure datum: I_w = I_2 if and only if the weighted class is
approached in value by the second-moment class. -/
theorem StationaryPressureDatum.Iw_eq_I2_iff_screening
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    D.Iw v = D.I2 v ↔
      ∀ Q ∈ D.Cw, ∀ ε : ℝ, 0 < ε →
        ∃ Q' ∈ D.C2, D.K Q' + v * D.P Q' < D.K Q + v * D.P Q + ε := by
  have h := sInf_image_eq_iff_screening (fun Q : W => D.K Q + v * D.P Q)
    D.Cw D.C2 D.C2_subset_Cw D.nonempty_C2 (D.bddBelow_Cw v)
  simpa only [StationaryPressureDatum.Iw, StationaryPressureDatum.I2,
    stationaryValue, ScreeningApproximates] using h

/-- Two classes with the same admissible set have the same stationary pressure. -/
theorem StationaryPressureDatum.Iw_eq_I2_of_classes_eq
    {W : Type*} {G Cb : ℝ} (D : StationaryPressureDatum W G Cb) (v : ℝ)
    (hclass : D.Cw = D.C2) :
    D.Iw v = D.I2 v := by
  simp only [StationaryPressureDatum.Iw, StationaryPressureDatum.I2, stationaryValue]
  rw [hclass]

end StationaryDatum

end OTSelector.Reconstruction

/-! ## 3. Stationary forward matching classes: uniformly elliptic identification -/

namespace OTSelector.PointProcess

open OTSelector.Reconstruction

namespace StationaryForwardMatching

/-- A uniformly positive calibrated coefficient identifies the two stationary
classes: finite weighted kinetic mean and finite unweighted displacement second
moment are then equivalent.  This is the paper's interior-collar lower bound
(and its elliptic approximation regime) in class form. -/
theorem weightedClass_eq_secondMomentClass_of_uniform_elliptic
    {α β : Measure UnitMark} {A : ℝ → ℝ → ℝ} {c C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hc : 0 < c) (hA_low : ∀ a b, c ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C) :
    weightedClass α β A = secondMomentClass α β := by
  ext M
  constructor
  · intro hM
    change Integrable (kineticIntegrand A) M.palm at hM
    change Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      edgeDisplacement p ^ 2) M.palm
    have hmeas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        edgeDisplacement p ^ 2) := by
      unfold edgeDisplacement
      exact ((measurable_fst.comp measurable_snd).sub
        (measurable_fst.comp measurable_fst)).pow_const 2
    have hdom : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        2 / c * kineticIntegrand A p) M.palm := hM.const_mul (2 / c)
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with p
    have hD : 0 ≤ edgeDisplacement p ^ 2 := sq_nonneg _
    have hAb := hA_low p.1.1 p.2.1
    have hstep : edgeDisplacement p ^ 2 ≤
        (A p.1.1 p.2.1 / c) * edgeDisplacement p ^ 2 := by
      have hcoef : (1 : ℝ) ≤ A p.1.1 p.2.1 / c := (one_le_div hc).mpr hAb
      calc edgeDisplacement p ^ 2 = 1 * edgeDisplacement p ^ 2 := by ring
        _ ≤ (A p.1.1 p.2.1 / c) * edgeDisplacement p ^ 2 :=
            mul_le_mul_of_nonneg_right hcoef hD
    have heq : 2 / c * kineticIntegrand A p =
        (A p.1.1 p.2.1 / c) * edgeDisplacement p ^ 2 := by
      unfold kineticIntegrand
      field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg hD, heq]
    exact hstep
  · intro hM
    exact finiteSecondMoment_subset_finiteWeightedKinetic hA_meas
      (fun a b => hc.le.trans (hA_low a b)) hA_bound hM

/-- Under a uniformly positive calibrated coefficient the weighted stationary
pressure equals the second-moment stationary pressure: the value identification
I_w = I_2 holds unconditionally in this regime. -/
theorem weightedStationaryPressure_eq_secondMoment_of_uniform_elliptic
    {α β : Measure UnitMark} {A : ℝ → ℝ → ℝ} {c C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hc : 0 < c) (hA_low : ∀ a b, c ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) (v : ℝ) :
    weightedStationaryPressure α β A f v = secondMomentStationaryPressure α β A f v := by
  simp only [weightedStationaryPressure, secondMomentStationaryPressure]
  rw [weightedClass_eq_secondMomentClass_of_uniform_elliptic hA_meas hc hA_low hA_bound]

/-- The paper's displayed chain -|v| G <= I_w <= I_2 <= C_b + |v| G becomes an
equality chain in the uniformly elliptic regime. -/
theorem neg_abs_mul_le_weighted_eq_secondMoment_le_upper
    {α β : Measure UnitMark} {A : ℝ → ℝ → ℝ}
    (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) {G Cb C c : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hc : 0 < c) (hA_low : ∀ a b, c ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    (competitor : StationaryForwardMatching α β)
    (hcompetitor : FiniteWeightedKinetic A competitor)
    (hcompetitor_K : palmKinetic A competitor ≤ Cb)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    (hcompetitor2_K : palmKinetic A competitor2 ≤ Cb) (v : ℝ) :
    -(|v| * G) ≤ weightedStationaryPressure α β A f v ∧
      weightedStationaryPressure α β A f v = secondMomentStationaryPressure α β A f v ∧
      secondMomentStationaryPressure α β A f v ≤ Cb + |v| * G := by
  have h := neg_abs_mul_le_weighted_le_secondMoment_le_upper A f hA_meas
    (fun a b => hc.le.trans (hA_low a b)) hA_bound hf hfG competitor hcompetitor
    hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K v
  exact ⟨h.1,
    weightedStationaryPressure_eq_secondMoment_of_uniform_elliptic hA_meas hc hA_low
      hA_bound f v, h.2.2⟩

/-- The root family of weighted stationary pressures coincides with the root
family of second-moment stationary pressures under a uniformly elliptic
calibrated coefficient, simultaneously at every root and tilt.  This is the
local form of the paper's integrated identification of the two Campbell-averaged
legal pressures. -/
theorem stationaryForwardPressureFamily_eq_secondMomentFamily_of_uniform_elliptic
    {Z : Type*} {α β : Measure UnitMark} {A : ℕ → Z → ℝ → ℝ → ℝ}
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) {c C : ℝ}
    (hA_meas : ∀ j z, Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      A j z p.1.1 p.2.1))
    (hc : 0 < c) (hA_low : ∀ j z a b, c ≤ A j z a b)
    (hA_bound : ∀ j z a b, A j z a b ≤ C) :
    ∀ (j : ℕ) (z : Z) (v : ℝ),
      stationaryForwardPressureFamily α β A f j z v =
        stationarySecondMomentFamily (stationaryForwardKineticFamily α β A)
          (stationaryForwardProbeFamily α β f) (fun _ _ => secondMomentClass α β) j z v := by
  intro j z v
  simp only [stationaryForwardPressureFamily, stationarySecondMomentFamily,
    stationaryPressureFamily, stationaryForwardWeightedClass]
  rw [weightedClass_eq_secondMomentClass_of_uniform_elliptic (hA_meas j z) hc
    (hA_low j z) (hA_bound j z)]

end StationaryForwardMatching

end OTSelector.PointProcess


/-! ## 4. The actual original Poisson framework -/

namespace OTSelector.Reconstruction

open Module Manifold OTSelector.Geometry ContinuousFinslerNorm
open scoped ContDiff

section LegalMatchingSecondMoment

namespace LegalWeightedStationaryPoissonMatching

/-- The paper's second-moment condition on an actual stationary legal Poisson
matching: the unweighted displacement second moment on the true source-anchored
Palm is finite. -/
def secondMomentSubclass {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) : Prop :=
  Integrable (fun m => ‖m.2‖ ^ 2) (legalMarkedJointPalm q Q.law)

end LegalWeightedStationaryPoissonMatching

/-- The sup norm squared of a finite real displacement vector is at most the sum
of its squared coordinates. -/
theorem norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  have hsum : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hle : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  calc ‖v‖ ^ 2 ≤ (Real.sqrt (∑ i, v i ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hle 2
    _ = ∑ i, v i ^ 2 := Real.sq_sqrt hsum

/-- A uniformly elliptic kinetic coefficient forces every legal weighted
matching to have finite unweighted displacement second moment: the weighted
kinetic integrability already dominates the second moment. -/
theorem secondMomentSubclass_of_uniform_elliptic
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v)
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    Q.secondMomentSubclass := by
  have hI := Q.kinetic_integrable
  have hdom : Integrable (fun m : PhysicalPairPalmMark (Fin q) =>
      (1 / c) * kin m.1.1 m.1.2 m.2) (legalMarkedJointPalm q Q.law) :=
    hI.const_mul (1 / c)
  have hmeas : AEStronglyMeasurable (fun m : PhysicalPairPalmMark (Fin q) => ‖m.2‖ ^ 2)
      (legalMarkedJointPalm q Q.law) :=
    ((measurable_norm.comp measurable_snd).pow_const 2).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards with m
  have hle : ‖m.2‖ ^ 2 ≤ ∑ i, m.2 i ^ 2 := norm_sq_le_sum_sq m.2
  have hsum_bound : ∑ i, m.2 i ^ 2 ≤ (1 / c) * kin m.1.1 m.1.2 m.2 := by
    have h := hkin m.1.1 m.1.2 m.2
    rw [show (1 / c) * kin m.1.1 m.1.2 m.2 = kin m.1.1 m.1.2 m.2 / c from by ring]
    exact (le_div_iff₀ hc).mpr (by linarith only [h])
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith only [hle, hsum_bound]

/-- The second-moment legal pressure I_2 of a fixed legal Poisson matching
family: the infimum of the signed value over the finite-second-moment subclass. -/
def legalSecondMomentInf (q : ℕ) (α β : Measure ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf ((fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t) ''
    {Q : LegalWeightedStationaryPoissonMatching q α β kin g | Q.secondMomentSubclass})

/-- The weighted legal pressure I_w of a fixed legal Poisson matching family:
the infimum of the signed value over all finite-weighted-energy matchings. -/
def legalWeightedInf (q : ℕ) (α β : Measure ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g =>
    Q.value t))

/-- Under uniform ellipticity of the kinetic coefficient every weighted legal
matching is a second-moment matching, so the two legal pressures coincide:
the unconditional value identification I_w = I_2 in the elliptic regime. -/
theorem legalSecondMomentInf_eq_legalWeightedInf_of_uniform_elliptic
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin q → ℝ), c * ∑ i, v i ^ 2 ≤ kin a b v) (t : ℝ) :
    legalSecondMomentInf q α β kin g t = legalWeightedInf q α β kin g t := by
  unfold legalSecondMomentInf legalWeightedInf
  have hclass : {Q : LegalWeightedStationaryPoissonMatching q α β kin g |
      Q.secondMomentSubclass} = Set.univ := by
    ext Q
    exact ⟨fun _ => trivial, fun _ => secondMomentSubclass_of_uniform_elliptic hc hkin Q⟩
  rw [hclass, Set.image_univ]

end LegalMatchingSecondMoment

/-! ### The actual original focal kinetic data -/

section OriginalPoisson

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments

variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The second-moment subclass of the actual original weighted stationary class
of the literal original focal kinetic cost: those genuine matchings whose
unweighted displacement second moment on the true Palm is finite. -/
def originalSecondMomentSubclass (gap : ℝ) (g : ℝ → ℝ → ℝ) :
    Set (LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :=
  {Q | Q.secondMomentSubclass}

/-- The actual second-moment legal pressure I_2 of the original focal kinetic
cost: the infimum of the signed value over the finite-second-moment subclass. -/
def originalSecondMomentStationaryInf (gap : ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf ((fun Q => Q.value t) '' D.originalSecondMomentSubclass gap g)

/-- The common actual signed lower bound of the original weighted class. -/
theorem originalWeightedStationaryInf_bddBelow
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    BddBelow (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) := by
  refine ⟨-(|t| * G), ?_⟩
  rintro _ ⟨Q, rfl⟩
  exact Q.value_lower_bound (D.originalFocalKinetic_nonneg hF hw hgap) hgb t

/-- The same lower bound for the second-moment subclass. -/
theorem originalSecondMomentSubclass_bddBelow
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    BddBelow ((fun Q => Q.value t) '' D.originalSecondMomentSubclass gap g) := by
  refine ⟨-(|t| * G), ?_⟩
  rintro _ ⟨Q, _hQ, rfl⟩
  exact Q.value_lower_bound (D.originalFocalKinetic_nonneg hF hw hgap) hgb t

/-- The second-moment legal pressure is below the value of every actual
finite-second-moment original matching. -/
theorem originalSecondMomentStationaryInf_le_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g}
    (hQ : Q ∈ D.originalSecondMomentSubclass gap g) :
    D.originalSecondMomentStationaryInf gap g t ≤ Q.value t :=
  csInf_le (D.originalSecondMomentSubclass_bddBelow hF hw hgap hgb t) ⟨Q, hQ, rfl⟩

/-- The actual finite-second-moment reserve supplies a nonempty second-moment
subclass of the original weighted stationary class. -/
theorem originalSecondMomentSubclass_nonempty
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    (D.originalSecondMomentSubclass gap g).Nonempty := by
  obtain ⟨Q, hQ⟩ := D.exists_original_focal_finiteSecondMoment_stationaryMatching
    hF hw hq hgap hbounds pi hpi horder hg hgb
  exact ⟨Q, hQ⟩

/-- The unconditional order of the two actual legal pressures: the weighted
value is at most the second-moment value. -/
theorem originalWeightedStationaryInf_le_secondMomentStationaryInf
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    D.originalWeightedStationaryInf gap g t ≤ D.originalSecondMomentStationaryInf gap g t := by
  have hne := D.originalSecondMomentSubclass_nonempty hF hw hq hgap hbounds pi hpi horder hg hgb
  have hbdd := D.originalWeightedStationaryInf_bddBelow hF hw hgap hgb t
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨Q, _hQ, rfl⟩
  exact csInf_le hbdd ⟨Q, rfl⟩

/-- **The actual original value identification is exactly screening.**  The
weighted and second-moment legal pressures of the original focal kinetic cost
coincide if and only if every weighted matching is approached in value from
above by a finite-second-moment matching.  This is the precise form of the open
input hvalue of the general selector assembly. -/
theorem originalWeightedStationaryInf_eq_secondMomentInf_iff_screening
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    D.originalWeightedStationaryInf gap g t = D.originalSecondMomentStationaryInf gap g t ↔
      ∀ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) g,
        ∀ ε : ℝ, 0 < ε ->
          ∃ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
              (D.originalFocalKinetic gap) g,
            Q' ∈ D.originalSecondMomentSubclass gap g ∧ Q'.value t < Q.value t + ε := by
  obtain ⟨Q₀, hQ₀⟩ :=
    D.originalSecondMomentSubclass_nonempty hF hw hq hgap hbounds pi hpi horder hg hgb
  have hne : (D.originalSecondMomentSubclass gap g).Nonempty := ⟨Q₀, hQ₀⟩
  have hbdd : BddBelow ((fun Q : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t) ''
      Set.univ) := by
    simpa only [Set.image_univ] using D.originalWeightedStationaryInf_bddBelow hF hw hgap hgb t
  have h := sInf_image_eq_iff_screening (fun Q : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)
    Set.univ (D.originalSecondMomentSubclass gap g) (Set.subset_univ _) hne hbdd
  rw [Set.image_univ] at h
  have hL : D.originalWeightedStationaryInf gap g t = sInf (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) := rfl
  have hR : D.originalSecondMomentStationaryInf gap g t = sInf ((fun Q :
      LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g => Q.value t) ''
      D.originalSecondMomentSubclass gap g) := rfl
  rw [hL, hR]
  simpa only [ScreeningApproximates, Set.mem_univ, true_implies] using h

/-- **Quantitative original value identification.**  A uniform screening budget
bounds the gap between the second-moment and weighted original legal pressures. -/
theorem originalSecondMomentStationaryInf_le_weighted_add
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) {B : ℝ}
    (hscreen : ∀ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker)
        μ ν (D.originalFocalKinetic gap) g,
      ∃ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) g,
        Q' ∈ D.originalSecondMomentSubclass gap g ∧ Q'.value t <= Q.value t + B) :
    D.originalSecondMomentStationaryInf gap g t <=
      D.originalWeightedStationaryInf gap g t + B := by
  obtain ⟨Q₀, hQ₀⟩ :=
    D.originalSecondMomentSubclass_nonempty hF hw hq hgap hbounds pi hpi horder hg hgb
  have hne : (D.originalSecondMomentSubclass gap g).Nonempty := ⟨Q₀, hQ₀⟩
  have hbdd : BddBelow ((fun Q : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t) ''
      Set.univ) := by
    simpa only [Set.image_univ] using D.originalWeightedStationaryInf_bddBelow hF hw hgap hgb t
  have h := sInf_image_le_add_of_screening_le (fun Q : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)
    Set.univ (D.originalSecondMomentSubclass gap g) (Set.subset_univ _) hne hbdd
    (fun Q _ => hscreen Q)
  rw [Set.image_univ] at h
  have hL : D.originalSecondMomentStationaryInf gap g t = sInf ((fun Q :
      LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g => Q.value t) ''
      D.originalSecondMomentSubclass gap g) := rfl
  have hR : D.originalWeightedStationaryInf gap g t = sInf (Set.range
      (fun Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) := rfl
  rwa [hL, hR]

/-- The explicit Neumann residual-repair constant is nonnegative. -/
theorem repairValueBudget_nonneg {rho C : ℝ} (hrho : 0 < rho) :
    0 ≤ rho⁻¹ * C ^ 2 / 2 := by
  have : 0 < rho⁻¹ := inv_pos.mpr hrho
  positivity

/-- **Original value gap controlled by the Neumann repair budget.**  When the
residual repair of every original weighted matching adds at most the explicit
constant rho⁻¹ C² / 2 of legalResidualRepair_absSignedValue_le to the signed
value, the original pressure gap is bounded by that same constant. -/
theorem originalSecondMomentStationaryInf_le_weighted_add_repairBudget
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {rho C : ℝ} (hrho : 0 < rho) (hC : 0 ≤ C)
    (hscreen : ∀ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker)
        μ ν (D.originalFocalKinetic gap) g,
      ∃ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
          (D.originalFocalKinetic gap) g,
        Q' ∈ D.originalSecondMomentSubclass gap g ∧
          Q'.value t <= Q.value t + rho⁻¹ * C ^ 2 / 2) :
    D.originalSecondMomentStationaryInf gap g t <=
      D.originalWeightedStationaryInf gap g t + rho⁻¹ * C ^ 2 / 2 := by
  have hbudget_nonneg : 0 ≤ rho⁻¹ * C ^ 2 / 2 := repairValueBudget_nonneg hrho
  have hC_nonneg : 0 ≤ C := hC
  exact D.originalSecondMomentStationaryInf_le_weighted_add hF hw hq hgap hbounds
    pi hpi horder hg hgb t hscreen

end OriginalSeedConditionalMoments

end OriginalPoisson

end OTSelector.Reconstruction


/-! ## 5. The actual finite legal pressure bound -/

namespace OTSelector.Reconstruction

/-- The second-moment legal pressure is below the value of every second-moment
matching of the same legal family. -/
theorem legalSecondMomentInf_le_value {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hkn : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {Q : LegalWeightedStationaryPoissonMatching q α β kin g}
    (hQ : Q.secondMomentSubclass) :
    legalSecondMomentInf q α β kin g t ≤ Q.value t := by
  have hbdd : BddBelow ((fun Q : LegalWeightedStationaryPoissonMatching q α β kin g =>
      Q.value t) '' {Q : LegalWeightedStationaryPoissonMatching q α β kin g |
        Q.secondMomentSubclass}) := by
    refine ⟨-(|t| * G), ?_⟩
    rintro _ ⟨Q, _hQ, rfl⟩
    exact Q.value_lower_bound hkn hgb t
  exact csInf_le hbdd ⟨Q, hQ, rfl⟩

/-- The unconditional order of the two legal pressures of a fixed legal family. -/
theorem legalWeightedInf_le_legalSecondMomentInf {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hkn : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (hne : {Q : LegalWeightedStationaryPoissonMatching q α β kin g |
      Q.secondMomentSubclass}.Nonempty) (t : ℝ) :
    legalWeightedInf q α β kin g t ≤ legalSecondMomentInf q α β kin g t := by
  have hbdd : BddBelow (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
      q α β kin g => Q.value t)) := by
    refine ⟨-(|t| * G), ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact Q.value_lower_bound hkn hgb t
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨Q, _hQ, rfl⟩
  exact csInf_le hbdd ⟨Q, rfl⟩

/-- The actual legal maximum-cardinality finite pressure limit bounds both
stationary legal values from above.  This is the finite-legal-graph half of the
paper's equality I_w = I_2 = p_A: the weighted and second-moment values of the
same legal family are bounded by the limit of the actual finite legal pressures
of the same kinetic cost, probe and independent input laws. -/
theorem exists_legalPressureLimit_ge_secondMomentInf
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (hIm : MeasurableSet I)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hpi : Vlasov.IsCoupling pi α β)
    (hI : ∀ᵐ z ∂pi, z.1 ∈ I ∧ z.2 ∈ I) (hgap : ∀ᵐ z ∂pi, δ ≤ z.2 - z.1)
    (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|)
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ => kin z.1 z.2)))
    (hkn : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hkb : ∀ a b (v : Fin q → ℝ), |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hgc : ContinuousOn (Function.uncurry g) K) :
    ∃ p : ℝ → ℝ,
      (∀ t : ℝ, Tendsto (fun R : ℝ =>
        legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 (p t))) ∧
      ∀ t : ℝ, legalSecondMomentInf q α β kin g t ≤ p t := by
  obtain ⟨p, hp, _hconc, _hlip, hM⟩ :=
    D.exists_legalWeightedStationaryPoissonMatching_energy_le hδ hIm pi α β hpi
      hI hgap hsep q hq hC hG hk hkn hkb hhom hg hgb hA hB hα hβ hK matrix
      hmatrix hpos hlegal hactual hgc
  refine ⟨p, hp, fun t => ?_⟩
  obtain ⟨M, hsecond, hvalue, _hscene⟩ := hM t
  exact (legalSecondMomentInf_le_value hkn hgb t hsecond).trans hvalue

/-- The full finite-legal-graph value chain: both stationary legal values are
bounded by the actual legal maximum-cardinality finite pressure limit, and the
weighted value is below the second-moment value. -/
theorem exists_legalPressureLimit_ge_weighted_le_secondMoment
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (hIm : MeasurableSet I)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hpi : Vlasov.IsCoupling pi α β)
    (hI : ∀ᵐ z ∂pi, z.1 ∈ I ∧ z.2 ∈ I) (hgap : ∀ᵐ z ∂pi, δ ≤ z.2 - z.1)
    (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|)
    (q : ℕ) (hq : 4 < q)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ => kin z.1 z.2)))
    (hkn : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v)
    (hkb : ∀ a b (v : Fin q → ℝ), |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hgc : ContinuousOn (Function.uncurry g) K) :
    ∃ p : ℝ → ℝ,
      (∀ t : ℝ, Tendsto (fun R : ℝ =>
        legalMarkedScalePressure q id id α β kin g R t) atTop (𝓝 (p t))) ∧
      ∀ t : ℝ, legalWeightedInf q α β kin g t ≤ legalSecondMomentInf q α β kin g t ∧
        legalSecondMomentInf q α β kin g t ≤ p t := by
  obtain ⟨p, hp, hbound⟩ :=
    exists_legalPressureLimit_ge_secondMomentInf D hδ hIm pi α β hpi hI hgap hsep
      q hq hC hG hk hkn hkb hhom hg hgb hA hB hα hβ hK matrix hmatrix hpos
      hlegal hactual hgc
  refine ⟨p, hp, fun t => ⟨?_, hbound t⟩⟩
  obtain ⟨_p', _hp', _hc', _hl', hM'⟩ :=
    D.exists_legalWeightedStationaryPoissonMatching_energy_le hδ hIm pi α β hpi
      hI hgap hsep q hq hC hG hk hkn hkb hhom hg hgb hA hB hα hβ hK matrix
      hmatrix hpos hlegal hactual hgc
  obtain ⟨M, hsecond, _hvalue, _hscene⟩ := hM' t
  exact legalWeightedInf_le_legalSecondMomentInf hkn hgb ⟨M, hsecond⟩ t

end OTSelector.Reconstruction

