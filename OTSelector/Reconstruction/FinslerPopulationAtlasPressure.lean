import OTSelector.Reconstruction.FinslerPopulationSeedIntensityCompactCore
import OTSelector.Reconstruction.FinslerCoefficientCorePartition
import OTSelector.Reconstruction.FinslerPopulationPressureCore
import OTSelector.Analysis.Convex.AffineInfimum
import OTSelector.Reconstruction.FinslerPopulationAtlasChangeOfMeasure

/-!
# The population atlas pressure and its finite weighted approximation

This module supplies the missing population-level definition of the paper's
atlas pressure
`P_w(t) = Σ_j ∫ θ_j(z)^s I_{j,w}(z, t θ_j(z)^(2/q)) dz`
(`main.tex`, the display `general-gluing-integrated-pressures`), with
`s = 1 - 2/q`.

The paper integrates theta^(1-2/q) against Haar coordinates. Because
`lambda` itself has Haar density theta, its root integrand is theta^(-2/q).
`populationAtlasHaarIntegrand` records the original Haar expression explicitly.

The original population root measure `lambda` is split into the measurable,
pairwise disjoint seed pieces `populationSeedRootPiece`.  On the `j`-th piece the
original Haar intensity is `populationSeedPieceHaarDensity`, read at the actual
inverse label `populationSeedRootLabelValue`.  This gives the theta-weighted
integrand the normalized root integrand `populationAtlasIntegrand` and pressure `populationAtlasPressure`
as the sum of the piece integrals.  The sum is shown to be summable as soon as
the integrand has a uniform bound; the disjointness of the pieces and the
finiteness of `lambda` are the only measure-theoretic inputs.

The second half proves the finite weighted-sum approximation
`∫_K f dλ ≈ Σ_i λ(cell_i) f(center_i)` on an arbitrary finite measurable root
partition `FiniteRootNeighborhoodPartition`.  The abstract statement uses the
cell oscillation bound; a companion version obtains it from compact uniform
continuity, and the specialization to a compact intensity core
`PopulationSeedIntensityCore` derives continuity of the atlas integrand from
continuity of the Haar density and of the local pressure.

Nothing here assumes or constructs the stationary values `I_{j,w}`/`I_{j,2}`
themselves: `populationAtlasPressure` takes the local pressures as a family
`I : ℕ → Z → ℝ → ℝ`, so that once `I_{j,w}` is defined (for instance through
`stationaryValue`) the pressure is `populationAtlasPressure ... I q t`.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-! ## Exponent arithmetic for the atlas weight -/

/-- The two atlas exponents sum to one: `(1 - 2/q) + 2/q = 1` for `q ≠ 0`. -/
theorem one_sub_two_div_add_two_div {q : ℝ} (hq : q ≠ 0) :
    (1 - 2 / q) + 2 / q = 1 := by
  field_simp
  ring

/-- The probe factor of the atlas integrand is majorized by `|t| * theta`.
This is the exponent computation `θ^(1-2/q) |t θ^(2/q)| = |t| θ`. -/
theorem abs_probe_mul_rpow_le {theta t q : ℝ} (htheta : 0 ≤ theta) (hq : 0 < q) :
    theta ^ (1 - 2 / q) * |t * theta ^ (2 / q)| ≤ |t| * theta := by
  rcases eq_or_lt_of_le htheta with htheta0 | hthetapos
  · rw [← htheta0]
    by_cases hq2 : q = 2
    · subst hq2
      norm_num [Real.rpow_zero, Real.zero_rpow]
    · have hexp : (1 - 2 / q : ℝ) ≠ 0 := by
        intro hexp0
        apply hq2
        have htwo : 2 / q = 1 := by linarith
        field_simp at htwo
        linarith
      rw [Real.zero_rpow hexp]
      simp
  · have hrearr : theta ^ (1 - 2 / q) * (|t| * theta ^ (2 / q)) =
        |t| * (theta ^ (1 - 2 / q) * theta ^ (2 / q)) := by ring
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hthetapos.le _), hrearr,
      ← Real.rpow_add hthetapos, one_sub_two_div_add_two_div hq.ne',
      Real.rpow_one]

/-- The stationary value inherits the paper's linear growth bound from a uniform
candidate with nonnegative kinetic energy and bounded probe: if every candidate
has nonnegative kinetic energy, the probe is bounded by `G`, and one candidate
has kinetic energy at most `Cb`, then
`|stationaryValue K P admissible v| ≤ Cb + |v| * G`.

This is the bridge from `StationaryPressureClasses` to the growth hypothesis
`|I z w| ≤ Cb + |w| * G` used for the atlas integrand. -/
theorem abs_stationaryValue_le_add_abs_mul {C : Type*} {K P : C → ℝ}
    {admissible : Set C} {Cb G : ℝ} (hCb : 0 ≤ Cb)
    (hne : admissible.Nonempty)
    (hK : ∀ c ∈ admissible, 0 ≤ K c)
    (hP : ∀ c ∈ admissible, |P c| ≤ G)
    (hupper : ∃ c ∈ admissible, K c ≤ Cb) (v : ℝ) :
    |stationaryValue K P admissible v| ≤ Cb + |v| * G := by
  obtain ⟨c, hc, hKc⟩ := hupper
  have hbd : BddBelow ((fun d ↦ K d + v * P d) '' admissible) :=
    bddBelow_stationaryValue (G := G) (v := v) hK hP
  have hlow : -(|v| * G) ≤ stationaryValue K P admissible v :=
    neg_abs_mul_le_stationaryValue (G := G) (v := v) hne hK hP
  have hupper' : stationaryValue K P admissible v ≤ Cb + |v| * G := by
    have hle := stationaryValue_le hbd hc
    have hvP : v * P c ≤ |v| * G := by
      calc v * P c ≤ |v * P c| := le_abs_self _
        _ = |v| * |P c| := abs_mul v (P c)
        _ ≤ |v| * G := mul_le_mul_of_nonneg_left (hP c hc) (abs_nonneg v)
    linarith
  exact abs_le.mpr ⟨by nlinarith [hlow, hCb], hupper'⟩

/-! ## The theta-weighted atlas integrand -/

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original Haar intensity `θ_j` read at an original population root, in the
actual seed label coordinates of the `j`-th selected piece. -/
def populationAtlasTheta (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (j : ℕ) (z : Z) : ℝ :=
  (populationSeedPieceHaarDensity P a κ lambda j
    (populationSeedRootLabelValue (P j).seed a z)).toReal

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The Haar intensity is nonnegative; the atlas weight is its power. -/
theorem populationAtlasTheta_nonneg (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (j : ℕ) (z : Z) : 0 ≤ populationAtlasTheta P a κ lambda j z :=
  ENNReal.toReal_nonneg

/-- The pressure integrand against the ORIGINAL POPULATION root measure.
Since `d lambda = theta d kappa`, its kinetic weight is `theta^(-2/q)`.
The corresponding Haar integrand has weight `theta^(1-2/q)`. -/
def populationAtlasIntegrand (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : Z → ℝ → ℝ) (j : ℕ) (q t : ℝ) (z : Z) : ℝ :=
  populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
    I z (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))

/-- The pressure integrand against the original seed HAAR reference.
Exactly one density factor relates it to `populationAtlasIntegrand`. -/
def populationAtlasHaarIntegrand (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : Z → ℝ → ℝ) (j : ℕ) (q t : ℝ) (z : Z) : ℝ :=
  populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) *
    I z (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
@[simp]
theorem populationAtlasIntegrand_def (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : Z → ℝ → ℝ) (j : ℕ) (q t : ℝ) (z : Z) :
    populationAtlasIntegrand P a κ lambda I j q t z =
      populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        I z (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) := rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The population-measure integrand is zero at zero density. No positive
lower bound is imposed on the original density. -/
theorem populationAtlasIntegrand_eq_zero_of_theta_eq_zero
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : Z → ℝ → ℝ) {j : ℕ} {q t : ℝ} (hq : 2 < q) {z : Z}
    (hz : populationAtlasTheta P a κ lambda j z = 0) :
    populationAtlasIntegrand P a κ lambda I j q t z = 0 := by
  have hneg : (-2 / q : ℝ) ≠ 0 := div_ne_zero (by norm_num) (by linarith)
  rw [populationAtlasIntegrand_def,hz,Real.zero_rpow hneg,zero_mul]

/-- The bounded probe contribution against the population root measure has
no remaining density factor. At zero density it vanishes. -/
theorem abs_probe_mul_inverse_rpow_le {theta t q : ℝ} (htheta : 0 ≤ theta) (hq : 0 < q) :
    theta ^ (-2 / q) * |t * theta ^ (2 / q)| ≤ |t| := by
  rcases eq_or_lt_of_le htheta with hzero | hpos
  · rw [← hzero]
    have hpow : (-2 / q : ℝ) ≠ 0 := div_ne_zero (by norm_num) hq.ne'
    rw [Real.zero_rpow hpow,zero_mul]
    exact abs_nonneg _
  · rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    calc
      _ = |t| * (theta ^ (-2 / q) * theta ^ (2 / q)) := by ring
      _ = |t| := by
        rw [← Real.rpow_add hpos]
        have hexp : (-2 / q : ℝ) + 2 / q = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_one]
      _ ≤ |t| := le_rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The correct population-measure growth bound. The inverse density power
is controlled on produced compact cores; no global density lower bound is assumed. -/
theorem abs_populationAtlasIntegrand_le
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : Z → ℝ → ℝ) {Cb G : ℝ} (_hCb : 0 ≤ Cb) (hG : 0 ≤ G)
    (hI : ∀ z w, |I z w| ≤ Cb + |w| * G)
    {j : ℕ} {q t : ℝ} (hq : 0 < q) (z : Z) :
    |populationAtlasIntegrand P a κ lambda I j q t z| ≤
      Cb * populationAtlasTheta P a κ lambda j z ^ (-2 / q) + |t| * G := by
  have htheta : 0 ≤ populationAtlasTheta P a κ lambda j z :=
    populationAtlasTheta_nonneg P a κ lambda j z
  rw [populationAtlasIntegrand_def,abs_mul,abs_of_nonneg (Real.rpow_nonneg htheta _)]
  calc
    _ ≤ populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
        (Cb + |t * populationAtlasTheta P a κ lambda j z ^ (2 / q)| * G) :=
      mul_le_mul_of_nonneg_left (hI z _) (Real.rpow_nonneg htheta _)
    _ = Cb * populationAtlasTheta P a κ lambda j z ^ (-2 / q) +
        G * (populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
          |t * populationAtlasTheta P a κ lambda j z ^ (2 / q)|) := by ring
    _ ≤ _ := by
      have hprobe := abs_probe_mul_inverse_rpow_le (t := t) htheta hq
      nlinarith [mul_le_mul_of_nonneg_left hprobe hG]

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The linear-growth bound for the local pressure transfers to the atlas
integrand: `|θ^(1-2/q) I z (t θ^(2/q))| ≤ Cb θ^(1-2/q) + |t| G θ`. -/
theorem abs_populationAtlasHaarIntegrand_le
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : Z → ℝ → ℝ) {Cb G : ℝ} (_hCb : 0 ≤ Cb) (hG : 0 ≤ G)
    (hI : ∀ z w, |I z w| ≤ Cb + |w| * G)
    {j : ℕ} {q t : ℝ} (hq : 0 < q) (z : Z) :
    |populationAtlasHaarIntegrand P a κ lambda I j q t z| ≤
      Cb * populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) +
        |t| * G * populationAtlasTheta P a κ lambda j z := by
  have htheta : 0 ≤ populationAtlasTheta P a κ lambda j z :=
    populationAtlasTheta_nonneg P a κ lambda j z
  rw [populationAtlasHaarIntegrand, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg htheta _)]
  calc populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) *
        |I z (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))|
      ≤ populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) *
          (Cb + |t * populationAtlasTheta P a κ lambda j z ^ (2 / q)| * G) :=
        mul_le_mul_of_nonneg_left (hI z _) (Real.rpow_nonneg htheta _)
    _ = Cb * populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) +
          G * (populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) *
            |t * populationAtlasTheta P a κ lambda j z ^ (2 / q)|) := by ring
    _ ≤ Cb * populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) +
          G * (|t| * populationAtlasTheta P a κ lambda j z) := by
        have hprobe := abs_probe_mul_rpow_le (t := t) htheta hq
        exact add_le_add_right (mul_le_mul_of_nonneg_left hprobe hG) _
    _ = Cb * populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) +
          |t| * G * populationAtlasTheta P a κ lambda j z := by ring


/-! ## The atlas pressure -/

/-- The population atlas pressure: the sum over the countably many disjoint
selected seed pieces of the population-measure-normalized atlas integral.  The family `I`
supplies the local pressure `I_j` of each piece; the paper's `I_{j,w}` and
`I_{j,2}` are the two instances. -/
def populationAtlasPressure (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : ℕ → Z → ℝ → ℝ) (q t : ℝ) : ℝ :=
  ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
    populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
@[simp]
theorem populationAtlasPressure_def (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : ℕ → Z → ℝ → ℝ) (q t : ℝ) :
    populationAtlasPressure P a κ lambda I q t =
      ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda := rfl

/-! ## Exact original Haar-coordinate normalization -/

/-- The original Haar-coordinate pressure density, with its root argument read
through the actual seed curve. Its exponent is `1-2/q` because the reference
measure here is the original Haar measure, rather than `lambda`. -/
def populationAtlasCoordinateHaarIntegrand
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : Z → ℝ → ℝ) (j : ℕ) (q t : ℝ) (w : (P j).seed.covector.ker) : ℝ :=
  (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (1 - 2 / q) *
    I (a ((P j).seed.curve w 0))
      (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q))

section OriginalHaar

variable [MeasurableSpace.CountablySeparated Z]
  (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  [IsFiniteMeasure lambda]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Exact change of measure on every measurable retained part of a seed piece.
The density is the original Radon--Nikodym derivative. Zero density is allowed. -/
theorem integral_populationAtlasIntegrand_eq_coordinate_haar
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (I : Z → ℝ → ℝ) {q t : ℝ} (hq : 2 < q)
    (hread : AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        I (a ((P j).seed.curve w 0))
          (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)))
      ((lambda.restrict K).map (populationSeedRootLabelValue (P j).seed a))) :
    (∫ z in K, populationAtlasIntegrand P a κ lambda I j q t z ∂lambda) =
      ∫ w in populationSeedRootLabelValue (P j).seed a '' K,
        populationAtlasCoordinateHaarIntegrand P a κ lambda I j q t w ∂κ j :=
  integral_populationSeedCore_root_pressure_eq_haar P a κ lambda hF hcomplete hu ha hinj
    j hK hsub hq I t hread

/-- The root-measure definition of the full pressure equals exactly the paper's
Haar-coordinate series. This is a measure-change identity, with no positive
lower density bound and no integrability assumption hidden in the notation. -/
theorem populationAtlasPressure_eq_haar_tsum
    [∀ j, SigmaFinite (κ j)] (I : ℕ → Z → ℝ → ℝ) {q t : ℝ} (hq : 2 < q)
    (hread : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        I j (a ((P j).seed.curve w 0))
          (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)))
      ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).map
        (populationSeedRootLabelValue (P j).seed a))) :
    populationAtlasPressure P a κ lambda I q t =
      ∑' j, ∫ w in populationSeedRootLabelValue (P j).seed a ''
          populationSeedRootPiece P a κ lambda j,
        populationAtlasCoordinateHaarIntegrand P a κ lambda (I j) j q t w ∂κ j := by
  unfold populationAtlasPressure
  apply tsum_congr
  intro j
  exact integral_populationAtlasIntegrand_eq_coordinate_haar P a κ lambda
    hF hcomplete hu ha hinj j
    (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
    Subset.rfl (I j) hq (hread j)

/-- A summable majorant of the actual Haar-coordinate L1 integrals suffices for
full-atlas summability. This analytic input allows densities approaching zero;
it does not assert a false uniform bound for the population integrand. -/
theorem summable_populationAtlasIntegral_of_haar_majorant
    [∀ j, SigmaFinite (κ j)] (I : ℕ → Z → ℝ → ℝ) {q t : ℝ} (hq : 2 < q)
    (hread : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        I j (a ((P j).seed.curve w 0))
          (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)))
      ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).map
        (populationSeedRootLabelValue (P j).seed a)))
    {B : ℕ → ℝ} (hB : Summable B)
    (hbound : ∀ j,
      (∫ w in populationSeedRootLabelValue (P j).seed a ''
          populationSeedRootPiece P a κ lambda j,
        |populationAtlasCoordinateHaarIntegrand P a κ lambda (I j) j q t w| ∂κ j) ≤ B j) :
    Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda) := by
  apply Summable.of_norm_bounded hB
  intro j
  rw [integral_populationAtlasIntegrand_eq_coordinate_haar P a κ lambda
    hF hcomplete hu ha hinj j
    (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
    Subset.rfl (I j) hq (hread j)]
  exact (norm_integral_le_integral_norm _).trans (by simpa only [Real.norm_eq_abs] using hbound j)

/-- The same true Haar L1 majorant controls the absolute full pressure. -/
theorem abs_populationAtlasPressure_le_haar_majorant
    [∀ j, SigmaFinite (κ j)] (I : ℕ → Z → ℝ → ℝ) {q t : ℝ} (hq : 2 < q)
    (hread : ∀ j, AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        I j (a ((P j).seed.curve w 0))
          (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)))
      ((lambda.restrict (populationSeedRootPiece P a κ lambda j)).map
        (populationSeedRootLabelValue (P j).seed a)))
    {B : ℕ → ℝ} (hB : Summable B)
    (hbound : ∀ j,
      (∫ w in populationSeedRootLabelValue (P j).seed a ''
          populationSeedRootPiece P a κ lambda j,
        |populationAtlasCoordinateHaarIntegrand P a κ lambda (I j) j q t w| ∂κ j) ≤ B j) :
    |populationAtlasPressure P a κ lambda I q t| ≤ ∑' j, B j := by
  have hterm (j : ℕ) :
      ‖∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda‖ ≤ B j := by
    rw [integral_populationAtlasIntegrand_eq_coordinate_haar P a κ lambda
      hF hcomplete hu ha hinj j
      (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
      Subset.rfl (I j) hq (hread j)]
    exact (norm_integral_le_integral_norm _).trans (by simpa only [Real.norm_eq_abs] using hbound j)
  simpa only [populationAtlasPressure, Real.norm_eq_abs] using
    tsum_of_norm_bounded hB.hasSum hterm

end OriginalHaar

section Summability

variable [MeasurableSpace.CountablySeparated Z]

/-- The disjoint selected pieces carry exactly the full root mass, provided
they cover `lambda`-almost every root. -/
theorem tsum_measure_populationSeedRootPiece
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasCoverMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j) :
    ∑' j, lambda (populationSeedRootPiece P a κ lambda j) = lambda univ := by
  have hmeas : ∀ j, MeasurableSet (populationSeedRootPiece P a κ lambda j) :=
    fun j ↦ measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j
  have hdisj : Pairwise (Disjoint on populationSeedRootPiece P a κ lambda) :=
    pairwiseDisjoint_populationSeedRootPiece P a κ lambda
  have heq : (⋃ j, populationSeedRootPiece P a κ lambda j) =ᵐ[lambda] univ := by
    filter_upwards [hcover] with z hz
    exact propext ⟨fun _ ↦ mem_univ z, fun _ ↦ hz⟩
  rw [← MeasureTheory.measure_iUnion hdisj hmeas]
  exact measure_congr heq

/-- The atlas pressure is well defined: if the integrand is uniformly bounded,
the piece integrals form a summable family.  Disjointness of the selected pieces
and finiteness of `lambda` give the summable majorant
`B * λ(piece_j)`. -/
theorem summable_populationAtlasIntegral
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instAtlasSummableMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (I : ℕ → Z → ℝ → ℝ) {q t B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ j (z : Z),
      |populationAtlasIntegrand P a κ lambda (I j) j q t z| ≤ B) :
    Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda) := by
  classical
  have hmeas : ∀ j, MeasurableSet (populationSeedRootPiece P a κ lambda j) :=
    fun j ↦ measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j
  have hdisj : Pairwise (Disjoint on populationSeedRootPiece P a κ lambda) :=
    pairwiseDisjoint_populationSeedRootPiece P a κ lambda
  have hsum_le : (∑' j, lambda (populationSeedRootPiece P a κ lambda j)) ≤ lambda univ :=
    MeasureTheory.tsum_measure_le_measure_univ
      (fun j ↦ (hmeas j).nullMeasurableSet) hdisj.aedisjoint
  have hsum_lt_top :
      (∑' j, lambda (populationSeedRootPiece P a κ lambda j)) < (∞ : ℝ≥0∞) :=
    hsum_le.trans_lt (measure_lt_top lambda univ)
  have hsummable_measure :
      Summable (fun j ↦ (lambda (populationSeedRootPiece P a κ lambda j)).toReal) :=
    ENNReal.summable_toReal hsum_lt_top.ne
  refine Summable.of_norm_bounded
    (f := fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda)
    (g := fun j ↦ B * (lambda (populationSeedRootPiece P a κ lambda j)).toReal)
    (hsummable_measure.mul_left B) ?_
  intro j
  have h := norm_integral_le_of_norm_le_const
    (μ := lambda.restrict (populationSeedRootPiece P a κ lambda j))
    (f := fun z ↦ populationAtlasIntegrand P a κ lambda (I j) j q t z)
    (C := B) (Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact hbound j z)
  rwa [Measure.real, Measure.restrict_apply_univ] at h

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace.CountablySeparated Z] in
/-- The atlas pressure is the sum of the summable piece integrals. -/
theorem hasSum_populationAtlasPressure
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (I : ℕ → Z → ℝ → ℝ) {q t : ℝ}
    (h : Summable (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda)) :
    HasSum (fun j ↦ ∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda)
      (populationAtlasPressure P a κ lambda I q t) :=
  h.hasSum

end Summability

/-! ## Finite weighted sums on a measurable root partition -/

section FiniteRootApproximation

variable {Z : Type*} [MeasurableSpace Z]

/-- The root measure of the disjoint partition cells adds up to the measure of
their union. -/
theorem FiniteRootNeighborhoodPartition.sum_measure_eq
    {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda] :
    ∑ i : Fin D.count, lambda (D.cell i) = lambda K := by
  have h := congrArg (fun μ : Measure Z ↦ μ univ) (D.sum_restrict lambda)
  rw [Measure.sum_fintype] at h
  simpa only [Measure.coe_finsetSum, Finset.sum_apply,
    Measure.restrict_apply_univ] using h

/-- The real cell masses add up to the real mass of the root core. -/
theorem FiniteRootNeighborhoodPartition.sum_toReal_measure_eq
    {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda] :
    ∑ i : Fin D.count, (lambda (D.cell i)).toReal = (lambda K).toReal := by
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin D.count)),
      lambda (D.cell i) ≠ (∞ : ℝ≥0∞) :=
    fun i _ ↦ measure_ne_top lambda (D.cell i)
  rw [← ENNReal.toReal_sum hne]
  exact congrArg ENNReal.toReal (D.sum_measure_eq lambda)

/-- Finite weighted-sum approximation on a measurable root partition: if the
integrand oscillates by at most `ε` on every cell, then the integral over the
core differs from the cell-mass weighted sum at the centers by at most
`ε * λ(K)`. -/
theorem FiniteRootNeighborhoodPartition.integral_sub_weighted_sum_le
    {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {ε : ℝ}
    (hf : IntegrableOn f K lambda) (_hε : 0 ≤ ε)
    (hosc : ∀ (i : Fin D.count) (z : Z), z ∈ D.cell i →
      |f z - f (D.center i)| ≤ ε) :
    |∫ z in K, f z ∂lambda -
      ∑ i : Fin D.count, (lambda (D.cell i)).toReal * f (D.center i)|
      ≤ ε * (lambda K).toReal := by
  classical
  have hcellsub : ∀ i : Fin D.count, D.cell i ⊆ K :=
    fun i ↦ (D.cell_subset i).trans inter_subset_left
  have hfcell : ∀ i : Fin D.count, IntegrableOn f (D.cell i) lambda :=
    fun i ↦ hf.mono_set (hcellsub i)
  have hsplit : ∫ z in K, f z ∂lambda =
      ∑ i : Fin D.count, ∫ z in D.cell i, f z ∂lambda := by
    calc ∫ z in K, f z ∂lambda
        = ∫ z in ⋃ i : Fin D.count, D.cell i, f z ∂lambda := by
            rw [D.union_eq]
      _ = ∑ i : Fin D.count, ∫ z in D.cell i, f z ∂lambda :=
          integral_iUnion_fintype D.measurable_cell D.disjoint hfcell
  have hterm : ∀ i : Fin D.count,
      |∫ z in D.cell i, f z ∂lambda -
        (lambda (D.cell i)).toReal * f (D.center i)|
        ≤ ε * (lambda (D.cell i)).toReal := by
    intro i
    have hconst : IntegrableOn (fun _ : Z ↦ f (D.center i)) (D.cell i) lambda :=
      integrable_const _
    have hconst_int : ∫ z in D.cell i, f (D.center i) ∂lambda =
        (lambda (D.cell i)).toReal * f (D.center i) := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    have heq : ∫ z in D.cell i, f z ∂lambda -
        (lambda (D.cell i)).toReal * f (D.center i) =
        ∫ z in D.cell i, (f z - f (D.center i)) ∂lambda := by
      rw [← hconst_int, integral_sub (hfcell i) hconst]
    rw [heq]
    have hae : ∀ᵐ z ∂(lambda.restrict (D.cell i)),
        ‖f z - f (D.center i)‖ ≤ ε := by
      filter_upwards [ae_restrict_mem (D.measurable_cell i)] with z hz
      rw [Real.norm_eq_abs]
      exact hosc i z hz
    have h := norm_integral_le_of_norm_le_const
      (μ := lambda.restrict (D.cell i))
      (f := fun z ↦ f z - f (D.center i)) (C := ε) hae
    rwa [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] at h
  calc
    |∫ z in K, f z ∂lambda -
        ∑ i : Fin D.count, (lambda (D.cell i)).toReal * f (D.center i)|
        = |∑ i : Fin D.count,
            (∫ z in D.cell i, f z ∂lambda -
              (lambda (D.cell i)).toReal * f (D.center i))| := by
          rw [hsplit, Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin D.count,
          |∫ z in D.cell i, f z ∂lambda -
            (lambda (D.cell i)).toReal * f (D.center i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin D.count, ε * (lambda (D.cell i)).toReal :=
        Finset.sum_le_sum fun i _ ↦ hterm i
    _ = ε * ∑ i : Fin D.count, (lambda (D.cell i)).toReal := by
        rw [Finset.mul_sum]
    _ = ε * (lambda K).toReal := by
        rw [D.sum_toReal_measure_eq lambda]

end FiniteRootApproximation

/-! ## The complement term of a retained core -/

section Complement

variable {Z : Type*} [MeasurableSpace Z]

/-- The complement of a retained core contributes at most its `lambda`-mass times
a uniform bound on the integrand. -/
theorem abs_integral_compl_le_of_bound {K : Set Z} (lambda : Measure Z)
    [IsFiniteMeasure lambda] {f : Z → ℝ} {B : ℝ}
    (_hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B) :
    |∫ z in Kᶜ, f z ∂lambda| ≤ B * (lambda Kᶜ).toReal := by
  have h := norm_integral_le_of_norm_le_const
    (μ := lambda.restrict Kᶜ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact hbound z)
  rwa [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] at h

/-- Replacing the full atlas integral by its integral over a retained measurable
core costs at most the mass of the complement times a uniform integrand bound.
For the population core this complement has exactly the original label mass
`lambda rootsᶜ < ε` (`PopulationPressureCore.complement_small`). -/
theorem abs_integral_sub_integral_core_le_of_bound {K : Set Z}
    (hK : MeasurableSet K) (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hint : Integrable f lambda) (hbound : ∀ z, |f z| ≤ B) :
    |∫ z, f z ∂lambda - ∫ z in K, f z ∂lambda| ≤ B * (lambda Kᶜ).toReal := by
  rw [← setIntegral_compl hK hint]
  exact abs_integral_compl_le_of_bound lambda hB hbound

end Complement

/-! ## Compact uniform continuity and the metric mesh version -/

section MetricMesh

variable {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]

omit [MeasurableSpace Z] in
/-- Compact uniform continuity: a continuous real function on a compact set has
arbitrarily small oscillation below an explicit distance mesh. -/
theorem exists_forall_abs_sub_le_of_dist_lt
    {K : Set Z} (hK : IsCompact K) {f : Z → ℝ} (hcont : ContinuousOn f K)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → |f x - f y| ≤ η := by
  have huc : UniformContinuousOn f K := hK.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hosc⟩ := huc η hη
  exact ⟨δ, hδ, fun x hx y hy hxy ↦ by
    have h := hosc x hx y hy hxy
    rw [Real.dist_eq] at h
    exact h.le⟩

/-- Metric mesh form of the finite weighted-sum approximation.  The mesh `δ`
is chosen from compact uniform continuity; any partition whose cells have
diameter below `δ` and whose centers lie on the core then satisfies the
approximation with error `η * λ(K)`. -/
theorem FiniteRootNeighborhoodPartition.exists_integral_sub_weighted_sum_le
    {K centers : Set Z} {U : Z → Set Z}
    (D : FiniteRootNeighborhoodPartition K centers U)
    (lambda : Measure Z) [IsFiniteMeasure lambda]
    {f : Z → ℝ} {η : ℝ}
    (hf : IntegrableOn f K lambda) (hK : IsCompact K) (hcont : ContinuousOn f K)
    (hη : 0 < η) :
    ∃ δ > 0, (∀ i : Fin D.count, D.center i ∈ K) →
      (∀ (i : Fin D.count) (z : Z), z ∈ D.cell i →
        dist z (D.center i) < δ) →
      |∫ z in K, f z ∂lambda -
        ∑ i : Fin D.count, (lambda (D.cell i)).toReal * f (D.center i)|
        ≤ η * (lambda K).toReal := by
  obtain ⟨δ, hδ, hmod⟩ := exists_forall_abs_sub_le_of_dist_lt hK hcont hη
  refine ⟨δ, hδ, fun hcenters hdiam ↦ ?_⟩
  refine D.integral_sub_weighted_sum_le lambda hf hη.le (fun i z hz ↦ ?_)
  exact hmod z (D.cell_subset i hz).1 (D.center i) (hcenters i) (hdiam i z hz)

end MetricMesh

/-! ## Continuity of the atlas integrand on a compact intensity core -/

section AtlasContinuous

variable [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
  (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [PolishSpace Z] [BorelSpace Z] in
/-- On a compact intensity core, the atlas integrand is continuous whenever the
local pressure is continuous in `(z, w)`: the Haar intensity is continuous in the
actual inverse label, and `x ↦ x^(1-2/q)`, `x ↦ x^(2/q)` are continuous for
`q > 2` on the nonnegative reals. -/
theorem PopulationSeedIntensityCore.continuousOn_populationAtlasIntegrand
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (I : Z → ℝ → ℝ) {q t : ℝ} (hq : 2 < q)
    (hI : ContinuousOn (fun p : Z × ℝ ↦ I p.1 p.2) (D.roots ×ˢ univ)) :
    ContinuousOn (fun z ↦ populationAtlasIntegrand P a κ lambda I j q t z) D.roots := by
  have hqpos : 0 < q := by linarith
  have htheta : ContinuousOn (populationAtlasTheta P a κ lambda j) D.roots := by
    unfold populationAtlasTheta
    exact D.continuous_density.comp D.continuous_label (fun z hz ↦ mem_image_of_mem _ hz)
  have h2 : 0 ≤ 2 / q := div_nonneg (by norm_num) hqpos.le
  have hpow1 : ContinuousOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q)) D.roots :=
    htheta.rpow_const (fun z hz ↦ Or.inl (ne_of_gt
      (D.lower_pos.trans_le ((D.bounds _ (mem_image_of_mem _ hz)).1))))
  have hpow2 : ContinuousOn
      (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (2 / q)) D.roots :=
    (Real.continuous_rpow_const h2).comp_continuousOn htheta
  have hpair : ContinuousOn
      (fun z ↦ (z, t * populationAtlasTheta P a κ lambda j z ^ (2 / q))) D.roots :=
    continuousOn_id.prodMk (continuousOn_const.mul hpow2)
  have hIcomp : ContinuousOn
      (fun z ↦ I z (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))) D.roots :=
    hI.comp hpair (fun z hz ↦ ⟨hz, mem_univ _⟩)
  change ContinuousOn
    (fun z ↦ populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
      I z (t * populationAtlasTheta P a κ lambda j z ^ (2 / q))) D.roots
  exact hpow1.mul hIcomp

end AtlasContinuous

/-! ## The atlas integral approximated by a finite weighted sum -/

section AtlasApproximation

variable [PseudoMetricSpace Z] [PolishSpace Z] [BorelSpace Z]
  (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  [IsFiniteMeasure lambda]

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- On a compact original intensity core, the atlas integral over the core is
approximated within `η * λ(roots)` by the cell-mass weighted sum of the atlas
integrand at the centers of any sufficiently fine finite measurable partition.
All constants are the original population ones; no probability normalization is
performed. -/
theorem PopulationSeedIntensityCore.exists_weighted_sum_approximation
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (I : Z → ℝ → ℝ) {q t η : ℝ} (hq : 2 < q) (hη : 0 < η)
    (hI : ContinuousOn (fun p : Z × ℝ ↦ I p.1 p.2) (D.roots ×ˢ univ)) :
    ∃ δ > 0, ∀ {centers : Set Z} {U : Z → Set Z}
      (Q : FiniteRootNeighborhoodPartition D.roots centers U),
      (∀ i : Fin Q.count, Q.center i ∈ D.roots) →
      (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      |∫ z in D.roots, populationAtlasIntegrand P a κ lambda I j q t z ∂lambda -
        ∑ i : Fin Q.count, (lambda (Q.cell i)).toReal *
          populationAtlasIntegrand P a κ lambda I j q t (Q.center i)|
        ≤ η * (lambda D.roots).toReal := by
  have hcont : ContinuousOn
      (fun z ↦ populationAtlasIntegrand P a κ lambda I j q t z) D.roots :=
    D.continuousOn_populationAtlasIntegrand P a κ lambda I hq hI
  have hf : IntegrableOn
      (fun z ↦ populationAtlasIntegrand P a κ lambda I j q t z) D.roots lambda :=
    hcont.integrableOn_of_subset_isCompact D.compact D.compact.measurableSet
      Subset.rfl (measure_ne_top lambda D.roots)
  obtain ⟨δ, hδ, hmod⟩ := exists_forall_abs_sub_le_of_dist_lt D.compact hcont hη
  refine ⟨δ, hδ, fun Q hcenters hdiam ↦ ?_⟩
  refine Q.integral_sub_weighted_sum_le lambda hf hη.le (fun i z hz ↦ ?_)
  exact hmod z (Q.cell_subset i hz).1 (Q.center i) (hcenters i) (hdiam i z hz)

end AtlasApproximation

end OTSelector.Reconstruction
