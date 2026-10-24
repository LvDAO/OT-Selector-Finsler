import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality
import OTSelector.Reconstruction.FinslerOriginalPaperGeometricBundleActual
import OTSelector.Reconstruction.FinslerOriginalPopulationCalibratedTube
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Ellipticity and seed-data producers for the consolidated theorem

This module attacks the two geometric/analytic input families of
paperEndgameData_actual_consolidated
(FinslerOriginalPaperTheoremConsolidated.lean) that are not produced anywhere in
the repository: the population seed datum PaperGeometricSeedDatum and the
uniform-ellipticity triple (c, hc, hA_low).

## 1. Exact statements (with line numbers)

Seed datum, FinslerOriginalPaperGeometricBundleActual.lean:67-78:

  structure PaperGeometricSeedDatum (F : ContinuousFinslerNorm E M) (u : M to Real)
      (mu nu : ProbabilityMeasure M) where
    seed : F.CalibratedLevelSeedPatch u
    seed_tube_open : IsOpen (seedTubeImage seed)
    hu_measurable : Measurable u
    source_clock_atomless : NullSingletonClass ((mu : Measure M).map u)
    target_clock_atomless : NullSingletonClass ((nu : Measure M).map u)

The only consumer is paperGeometricHypotheses_of_seedDatum
(FinslerOriginalPaperGeometricBundleActual.lean:107), which feeds the geometric
field of the endgame data.  There is NO producer of PaperGeometricSeedDatum and
no term of CalibratedLevelSeedPatch (FinslerOriginalGeometry.CalibratedLevelSeedPatch.lean:63)
anywhere in the repo: the patch structure itself asks for the complete
Euler-Lagrange family curve, a C11 level-seed presentation, countable local
charts with Lipschitz constants and a chart cover -- the paper's calibrated
level-seed hypothesis.  We provide the missing constructor and the end-to-end
producer of the geometric hypotheses from the five inputs, so that the datum
binder disappears (Section 3).  The residual inputs are exactly: (i) a
calibrated level seed patch, (ii) openness of its tube image (the paper's local
openness of the seed tube, main.tex:1063-1078), (iii) measurability of u, (iv)
atomlessness of the two population clock laws.

Uniform ellipticity, FinslerOriginalPaperTheoremConsolidated.lean:237 and :468:

  (c : Real) (hc : 0 < c) (hA_low : forall (phi : FinalProbeSpace A B) (x y : Real),
    c <= (Ag phi) x y)                                    -- no time-like lower bound
  (C : FinalProbeSpace A B -> Real) (hA_bound : forall phi x y, (Ag phi) x y <= C phi)
  (hA_meas : ... Measurable (Ag phi ...))

They are consumed only through
weightedClass_eq_secondMomentClass_of_uniform_elliptic
(FinslerOriginalLegalPressureValueEquality.lean:208), whose hypotheses are the
GLOBAL bounds 0 < c, forall a b, c <= A a b, forall a b, A a b <= C; that class
equality implies the screening field hscreen of the consolidated theorem.

## 2. Paper provenance of the elliptic constants

The weighted stationary cost is (1/2) D^T A_z(a,b) D with the compliance matrix
A_z(a,b) = [ Integral_a^b H(r,z)^{-1} dr ]^{-1} (main.tex:7803,
general-gluing-full-matrix).  There, H is continuous positive definite; its upper
bound is uniform and the scalar support gap is at least delta > 0, so
A_z <= C Id with C = Lambda/delta; a lower bound lambda > 0 is uniform on an
interior collar with bounded conditional support span L = u - ell (main.tex
7819-7828), so A_z >= c Id with c = lambda/L; this bound may degenerate as the
source approaches the lower ray endpoint, which is exactly why the paper restricts
the elliptic case to the interior collar.  Section 1 of this file machine-checks
the scalar case of this derivation: the compliance of H with
lambda <= H <= Lambda on the collar gives c = lambda/L and C = Lambda/delta
explicitly (rayCompliance_lower / rayCompliance_upper).

## 3. What is and is not derivable from the Finsler geometry alone

The Finsler strong convexity structure IsSmoothStronglyConvex
(OTSelector/Geometry/FinslerEnergy.lean:124-128) has exactly two fields:
contMDiffOn_energy and hessian_pos, where hessian_pos is a POINTWISE strict
positivity statement  forall x v != 0, forall w != 0, 0 < fderiv (fderiv fiberEnergyModel x) v w w.
It carries no uniform constant, no compactness or collar data, and no upper
bound.  Hence it cannot produce the uniform constants c and C on its own, and the
calibrated coefficient Ag is a free binder in the consolidated theorem with no
geometric definition in the repo.  What is needed, and what the paper supplies,
is the ray-collapse data H with uniform two-sided bounds on a bounded interior
collar (the printed Lemma in the elliptic case).  Section 2 bundles exactly
that as UniformEllipticRayData and produces the consolidated triple from it, with
the ellipse constants computed; the only remaining analytic input is joint
measurability of the coefficient (hA_meas), which the paper obtains from
continuity of H on the collar.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

/-! ## 1. The scalar compliance coefficient and the paper's elliptic constants -/

/-- The scalar ray compliance A(a,b) = (Integral_a^b H(r)^{-1} dr)^{-1} of the
paper's matrix formula general-gluing-full-matrix (main.tex:7803) in the scalar
case. -/
def rayCompliance (H : Real → Real) (a b : Real) : Real :=
  (∫ r in a..b, (H r)⁻¹)⁻¹

/-- The reciprocal field of a continuous positive field is interval integrable. -/
theorem intervalIntegrable_inv {H : Real → Real} {a b : Real} (hab : a ≤ b)
    (hHc : Continuous H) (hHpos : ∀ r ∈ Icc a b, 0 < H r) :
    IntervalIntegrable (fun r => (H r)⁻¹) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab
    (hHc.continuousOn.inv₀ (fun r hr => (hHpos r hr).ne'))

/-- The integral of the compliance density is at least the interval length
divided by the upper field bound: this is the quantitative content of
A_z(a,b) <= (Lambda/(b-a)) Id. -/
theorem integral_inv_lower {H : Real → Real} {a b Lambda : Real} (hab : a ≤ b)
    (hHc : Continuous H) (hLam : 0 < Lambda)
    (hHpos : ∀ r ∈ Icc a b, 0 < H r) (hhi : ∀ r ∈ Icc a b, H r ≤ Lambda) :
    (b - a) / Lambda ≤ ∫ r in a..b, (H r)⁻¹ := by
  have hint : IntervalIntegrable (fun r => (H r)⁻¹) volume a b :=
    intervalIntegrable_inv hab hHc hHpos
  have hmono : (∫ _ in a..b, (1 / Lambda : Real)) ≤ ∫ r in a..b, (H r)⁻¹ :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
      (fun x hx => by
        have h : (1 : Real) / Lambda ≤ 1 / H x :=
          one_div_le_one_div_of_le (hHpos x hx) (hhi x hx)
        simpa [one_div] using h)
  have hconst : (∫ _ in a..b, (1 / Lambda : Real)) = (b - a) / Lambda := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-- The integral of the compliance density is at most the interval length
divided by the lower field bound: this is the quantitative content of
A_z(a,b) >= (lambda/(b-a)) Id. -/
theorem integral_inv_upper {H : Real → Real} {a b lam : Real} (hab : a ≤ b)
    (hHc : Continuous H) (hlam : 0 < lam)
    (hHpos : ∀ r ∈ Icc a b, 0 < H r) (hlo : ∀ r ∈ Icc a b, lam ≤ H r) :
    (∫ r in a..b, (H r)⁻¹) ≤ (b - a) / lam := by
  have hint : IntervalIntegrable (fun r => (H r)⁻¹) volume a b :=
    intervalIntegrable_inv hab hHc hHpos
  have hmono : (∫ r in a..b, (H r)⁻¹) ≤ ∫ _ in a..b, (1 / lam : Real) :=
    intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
      (fun x hx => by
        have h : (1 : Real) / H x ≤ 1 / lam :=
          one_div_le_one_div_of_le hlam (hlo x hx)
        simpa [one_div] using h)
  have hconst : (∫ _ in a..b, (1 / lam : Real)) = (b - a) / lam := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-- The compliance is at most Lambda/(b-a): the paper's upper bound
A_z <= (Lambda/(b-a)) Id. -/
theorem rayCompliance_le_upper {H : Real → Real} {a b Lambda : Real} (hab : a < b)
    (hHc : Continuous H) (hLam : 0 < Lambda)
    (hHpos : ∀ r ∈ Icc a b, 0 < H r) (hhi : ∀ r ∈ Icc a b, H r ≤ Lambda) :
    rayCompliance H a b ≤ Lambda / (b - a) := by
  have hb := hab.le
  have hSlo := integral_inv_lower hb hHc hLam hHpos hhi
  have hSpos : 0 < ∫ r in a..b, (H r)⁻¹ :=
    lt_of_lt_of_le (div_pos (sub_pos.2 hab) hLam) hSlo
  have hA : rayCompliance H a b = 1 / (∫ r in a..b, (H r)⁻¹) := by
    rw [rayCompliance, inv_eq_one_div]
  rw [hA]
  refine (div_le_iff₀ hSpos).2 ?_
  have hprod : (Lambda / (b - a)) * ((b - a) / Lambda) ≤
      (Lambda / (b - a)) * (∫ r in a..b, (H r)⁻¹) :=
    mul_le_mul_of_nonneg_left hSlo (div_pos hLam (sub_pos.2 hab)).le
  have hval : (Lambda / (b - a)) * ((b - a) / Lambda) = 1 := by
    rw [div_mul_div_comm, mul_comm Lambda (b - a)]
    exact div_self (mul_ne_zero (sub_pos.2 hab).ne' hLam.ne')
  linarith

/-- **The paper's elliptic constants, scalar case.**  For a continuous scalar
stiffness field H with lambda <= H <= Lambda on the collar and collar width
b - a <= L, the compliance satisfies lambda/L <= A(a,b) <= Lambda/(b-a);
with the support gap delta <= b - a this gives A(a,b) <= Lambda/delta. -/
theorem rayCompliance_bounds {H : Real → Real} {a b lam Lambda L : Real} (hab : a < b)
    (hHc : Continuous H) (hlam : 0 < lam) (hLam : 0 < Lambda)
    (hHpos : ∀ r ∈ Icc a b, 0 < H r)
    (hlo : ∀ r ∈ Icc a b, lam ≤ H r) (hhi : ∀ r ∈ Icc a b, H r ≤ Lambda)
    (hL : b - a ≤ L) (hLpos : 0 < L) :
    lam / L ≤ rayCompliance H a b ∧ rayCompliance H a b ≤ Lambda / (b - a) := by
  refine ⟨?_, rayCompliance_le_upper hab hHc hLam hHpos hhi⟩
  have hb := hab.le
  have hSlo := integral_inv_lower hb hHc hLam hHpos hhi
  have hShi := integral_inv_upper hb hHc hlam hHpos hlo
  have hSpos : 0 < ∫ r in a..b, (H r)⁻¹ :=
    lt_of_lt_of_le (div_pos (sub_pos.2 hab) hLam) hSlo
  have hA : rayCompliance H a b = 1 / (∫ r in a..b, (H r)⁻¹) := by
    rw [rayCompliance, inv_eq_one_div]
  rw [hA]
  refine (le_div_iff₀ hSpos).2 ?_
  have hprod : (lam / L) * (∫ r in a..b, (H r)⁻¹) ≤ (lam / L) * ((b - a) / lam) :=
    mul_le_mul_of_nonneg_left hShi (div_pos hlam hLpos).le
  have hval : (lam / L) * ((b - a) / lam) = (b - a) / L := by
    field_simp
  have hle1 : (b - a) / L ≤ 1 := by
    rw [div_le_one hLpos]
    exact hL
  linarith

/-- Lower elliptic constant c = lambda/L on a collar of width at most L. -/
theorem rayCompliance_lower {H : Real → Real} {a b lam Lambda L : Real} (hab : a < b)
    (hHc : Continuous H) (hlam : 0 < lam) (hLam : 0 < Lambda)
    (hHpos : ∀ r ∈ Icc a b, 0 < H r)
    (hlo : ∀ r ∈ Icc a b, lam ≤ H r) (hhi : ∀ r ∈ Icc a b, H r ≤ Lambda)
    (hL : b - a ≤ L) (hLpos : 0 < L) :
    lam / L ≤ rayCompliance H a b :=
  (rayCompliance_bounds hab hHc hlam hLam hHpos hlo hhi hL hLpos).1

/-- Upper elliptic constant C = Lambda/delta on supported pairs with gap delta. -/
theorem rayCompliance_upper {H : Real → Real} {a b Lambda delta : Real} (hab : a < b)
    (hHc : Continuous H) (hLam : 0 < Lambda) (hdelta : 0 < delta)
    (hHpos : ∀ r ∈ Icc a b, 0 < H r) (hhi : ∀ r ∈ Icc a b, H r ≤ Lambda)
    (hdelta_le : delta ≤ b - a) :
    rayCompliance H a b ≤ Lambda / delta := by
  have h1 := rayCompliance_le_upper hab hHc hLam hHpos hhi
  have h2 : Lambda / (b - a) ≤ Lambda / delta := by
    rw [div_le_div_iff₀ (sub_pos.2 hab) hdelta]
    nlinarith [hLam.le, hdelta_le]
  linarith

/-! ## 2. The single typed geometric input and the produced ellipticity triple -/

/-- **The ray-collapse data of the paper's elliptic case.**  The index phi
ranges over the probe/test family (for instance FinalProbeSpace A B).  H phi is
the scalar stiffness (the collapsed Jacobi/compliance field) on the bounded
interior collar [left, right], continuous and with uniform two-sided bounds
lambda <= H <= Lambda; delta is the uniform support gap of the forward legal
pairs, no larger than the collar width.  This is exactly the geometric Lemma
content used by the paper at general-gluing-full-matrix (main.tex:7803). -/
structure UniformEllipticRayData (iota : Type*) where
  /-- Lower collar endpoint in ray time. -/
  left : Real
  /-- Upper collar endpoint in ray time. -/
  right : Real
  /-- The collar is nondegenerate. -/
  hleft_right : left < right
  /-- Uniform lower stiffness bound on the collar. -/
  lam : Real
  /-- Uniform upper stiffness bound on the collar. -/
  Lambda : Real
  /-- Uniform support gap of forward legal pairs. -/
  delta : Real
  /-- The lower stiffness bound is positive. -/
  hlam : 0 < lam
  /-- The upper stiffness bound is positive. -/
  hLambda : 0 < Lambda
  /-- The support gap is positive. -/
  hdelta : 0 < delta
  /-- The support gap is at most the collar width. -/
  hdelta_span : delta ≤ right - left
  /-- The lower bound does not exceed the upper bound. -/
  hlam_le_Lambda : lam ≤ Lambda
  /-- The scalar stiffness field, indexed by the test function. -/
  H : iota → Real → Real
  /-- Continuity of the stiffness field. -/
  hH_cont : ∀ phi, Continuous (H phi)
  /-- Pointwise positivity of the stiffness field on the collar. -/
  hH_pos : ∀ phi r, left ≤ r → r ≤ right → 0 < H phi r
  /-- Uniform lower stiffness bound on the collar. -/
  hH_lower : ∀ phi r, left ≤ r → r ≤ right → lam ≤ H phi r
  /-- Uniform upper stiffness bound on the collar. -/
  hH_upper : ∀ phi r, left ≤ r → r ≤ right → H phi r ≤ Lambda

namespace UniformEllipticRayData

variable {iota : Type*} (R : UniformEllipticRayData iota)

/-- The paper's scalar compliance A_z(a,b) at the test function phi. -/
def compliance (phi : iota) : Real → Real → Real :=
  fun a b => rayCompliance (R.H phi) a b

theorem hHpos' (phi : iota) {a b : Real} (ha : R.left ≤ a) (hb : b ≤ R.right) :
    ∀ r ∈ Icc a b, 0 < R.H phi r :=
  fun r hr => R.hH_pos phi r (le_trans ha hr.1) (le_trans hr.2 hb)

theorem hHlower' (phi : iota) {a b : Real} (ha : R.left ≤ a) (hb : b ≤ R.right) :
    ∀ r ∈ Icc a b, R.lam ≤ R.H phi r :=
  fun r hr => R.hH_lower phi r (le_trans ha hr.1) (le_trans hr.2 hb)

theorem hHupper' (phi : iota) {a b : Real} (ha : R.left ≤ a) (hb : b ≤ R.right) :
    ∀ r ∈ Icc a b, R.H phi r ≤ R.Lambda :=
  fun r hr => R.hH_upper phi r (le_trans ha hr.1) (le_trans hr.2 hb)

/-- The uniform lower elliptic constant c = lambda/(right - left). -/
theorem c_pos : 0 < R.lam / (R.right - R.left) :=
  div_pos R.hlam (sub_pos.2 R.hleft_right)

/-- The elliptic constants are compatible: c <= C. -/
theorem c_le_C : R.lam / (R.right - R.left) ≤ R.Lambda / R.delta := by
  rw [div_le_div_iff₀ (sub_pos.2 R.hleft_right) R.hdelta]
  nlinarith [R.hlam.le, R.hLambda.le, R.hdelta.le, R.hdelta_span, R.hlam_le_Lambda]

/-- c = lambda/L is a uniform lower bound for the compliance on the collar. -/
theorem lower (phi : iota) {a b : Real} (ha : R.left ≤ a) (hb : b ≤ R.right)
    (hab : a < b) :
    R.lam / (R.right - R.left) ≤ R.compliance phi a b :=
  rayCompliance_lower hab (R.hH_cont phi) R.hlam R.hLambda (R.hHpos' phi ha hb)
    (R.hHlower' phi ha hb) (R.hHupper' phi ha hb) (by linarith) (sub_pos.2 R.hleft_right)

/-- C = Lambda/delta is a uniform upper bound for the compliance on supported
pairs with gap at least delta. -/
theorem upper (phi : iota) {a b : Real} (ha : R.left ≤ a) (hb : b ≤ R.right)
    (hab : a < b) (hgap : R.delta ≤ b - a) :
    R.compliance phi a b ≤ R.Lambda / R.delta :=
  rayCompliance_upper hab (R.hH_cont phi) R.hLambda R.hdelta (R.hHpos' phi ha hb)
    (R.hHupper' phi ha hb) hgap

/-- The global elliptic coefficient consumed by the class equality: the
physical compliance on the supported forward-pair domain (where it is clamped by
the uniform upper bound, which it already satisfies), and the constant
C = Lambda/delta off that domain.  On the supported domain it equals the
physical A_z. -/
def ellipticCoefficient (phi : iota) (a b : Real) : Real :=
  if R.left ≤ a ∧ a < b ∧ b ≤ R.right ∧ R.delta ≤ b - a then
    min (R.compliance phi a b) (R.Lambda / R.delta)
  else R.Lambda / R.delta

/-- Global lower bound: the elliptic constant c works for every pair. -/
theorem ellipticCoefficient_lower (phi : iota) (a b : Real) :
    R.lam / (R.right - R.left) ≤ R.ellipticCoefficient phi a b := by
  unfold ellipticCoefficient
  split_ifs with h
  · exact le_min (R.lower phi h.1 h.2.2.1 h.2.1) R.c_le_C
  · exact R.c_le_C

/-- Global upper bound with the explicit constant C = Lambda/delta. -/
theorem ellipticCoefficient_upper (phi : iota) (a b : Real) :
    R.ellipticCoefficient phi a b ≤ R.Lambda / R.delta := by
  unfold ellipticCoefficient
  split_ifs with h
  · exact min_le_right _ _
  · exact le_rfl

end UniformEllipticRayData

/-- **Screening is reduced to the single typed geometric input.**  The class
identification behind the consolidated screening field holds for the coefficient
produced from UniformEllipticRayData; the only remaining input is joint
measurability of the coefficient (hA_meas in the consolidated theorem), which
the paper obtains from continuity of the collapsed stiffness field. -/
theorem weightedClass_eq_secondMomentClass_of_rayData {iota : Type*}
    (R : UniformEllipticRayData iota) (alpha beta : Measure UnitMark)
    (hA_meas : ∀ phi : iota, Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      R.ellipticCoefficient phi p.1.1 p.2.1)) :
    ∀ phi : iota,
      weightedClass alpha beta (R.ellipticCoefficient phi) = secondMomentClass alpha beta := by
  intro phi
  exact weightedClass_eq_secondMomentClass_of_uniform_elliptic
    (A := R.ellipticCoefficient phi) (C := R.Lambda / R.delta) (hA_meas phi) R.c_pos
    (R.ellipticCoefficient_lower phi) (R.ellipticCoefficient_upper phi)

/-! ## 3. The population seed datum: the missing constructor and producer -/

universe uE uM

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(Real, E) ∞ M]
  [IsManifold 𝓘(Real, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Constructor of the paper geometric seed datum.**  This is the missing
inhabitant interface of PaperGeometricSeedDatum
(FinslerOriginalPaperGeometricBundleActual.lean:67): the paper's five geometric
inputs suffice, and nothing engineered is hidden. -/
def paperGeometricSeedDatum_mk {F : ContinuousFinslerNorm E M} {u : M → Real}
    {mu nu : ProbabilityMeasure M} (seed : F.CalibratedLevelSeedPatch u)
    (hopen : IsOpen (seedTubeImage seed)) (humeas : Measurable u)
    (hμatom : NullSingletonClass ((mu : Measure M).map u))
    (hνatom : NullSingletonClass ((nu : Measure M).map u)) :
    PaperGeometricSeedDatum F u mu nu :=
  ⟨seed, hopen, humeas, hμatom, hνatom⟩

/-- **End-to-end producer of the paper geometric hypotheses.**  From the five
seed/population inputs (and the standing smooth strongly convex structure and
one-Lipschitz potential) this produces FinslerPaperGeometricHypotheses without
passing the seed datum as an opaque binder. -/
def paperGeometricHypotheses_of_seedInputs {F : ContinuousFinslerNorm E M}
    {u : M → Real} {mu nu : ProbabilityMeasure M} (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (seed : F.CalibratedLevelSeedPatch u) (hopen : IsOpen (seedTubeImage seed))
    (humeas : Measurable u)
    (hμatom : NullSingletonClass ((mu : Measure M).map u))
    (hνatom : NullSingletonClass ((nu : Measure M).map u)) :
    FinslerPaperGeometricHypotheses F u mu nu :=
  paperGeometricHypotheses_of_seedDatum F u mu nu hF hu
    (paperGeometricSeedDatum_mk seed hopen humeas hμatom hνatom)

end OTSelector.Reconstruction
