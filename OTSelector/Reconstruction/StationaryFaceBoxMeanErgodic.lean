import OTSelector.Analysis.InnerProductSpace.TranslationCoboundary
import OTSelector.Probability.StationaryHyperplaneInvariantProjection
import Mathlib.Topology.MetricSpace.Equicontinuity
import OTSelector.MeasureTheory.Integral.CommonShell
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary

/-!
Conditions: A family of Hilbert isometries and actual contraction operators annihilating every translation coboundary along the stated filter.

Objects: Orthogonal complement/closure identities for the coboundary span and convergence to zero on the complement of global invariants.

Proof detail: Identify the orthogonal complement by the isometry pairing, apply double orthogonal closure and extend convergence from the dense coboundary span using the uniform contraction norm.

Sources: Terence Tao, Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61); Terence Tao, Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57).
Relation: Hilbert closure/density argument. The general contraction family need not be literal time averages, so this is not claimed as a verbatim classical mean-ergodic theorem.
-/

/-! Genuine Hilbert-space spatial box averages and their mean-ergodic limit. -/

open Set Function Filter Submodule MeasureTheory
open scoped InnerProductSpace Topology BigOperators
noncomputable section
namespace OTSelector.Probability

variable {F H : Type*} [AddCommGroup F] [Module ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]











/-- The genuine Koopman representation has precisely the actual invariant
sigma algebra's L² space as its whole joint fixed subspace. -/
theorem stationaryKoopman_jointFixed_eq_lpMeas
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : F → Ω → Ω) (hT : ∀ a, MeasurePreserving (T a) P P)
    (hzero : T 0 = id) (haddT : ∀ a b ω, T a (T b ω) = T (a + b) ω) :
    translationFixedSubspace (stationaryKoopman P T hT hzero haddT) ⊤ =
      lpMeas ℝ ℝ (aeInvariantEventSigma P T) 2 P := by
  ext f
  rw [mem_lpMeas_aeInvariantEventSigma_iff P T hT]
  constructor
  · intro hf a
    exact hf a (by trivial)
  · intro hf a _
    exact hf a

end OTSelector.Probability

namespace OTSelector.Reconstruction
open OTSelector.Probability MeasureTheory
open scoped ENNReal

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- The literal normalized Haar cube integral for Banach-valued observations. -/
theorem integral_haarCubeRootLaw_banach {R : ℝ} (hR : 0 ≤ R)
    (f : (ι → ℝ) → V) :
    (∫ z, f z ∂haarCubeRootLaw ι R) =
      ((2 * R) ^ Fintype.card ι)⁻¹ • ∫ z in haarRootCube ι R, f z := by
  rw [haarCubeRootLaw, cavityRootMeasure, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]

/-- The actual translated cube has the same concrete normalized shell bound
for a Banach-valued observable as for a scalar one. -/
theorem norm_integral_haarCubeRootLaw_shift_sub_le_banach
    {f : (ι → ℝ) → V} (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C)
    (v : ι → ℝ) {R S : ℝ}
    (hS : 0 ≤ S) (hRS : S ≤ R) (hv : ∀ i, |v i| ≤ S) :
    ‖(∫ z, f (z + v) ∂haarCubeRootLaw ι R) - ∫ z, f z ∂haarCubeRootLaw ι R‖ ≤
      2 * C * (((2 * (R + S)) ^ Fintype.card ι -
        (2 * (R - S)) ^ Fintype.card ι) / (2 * R) ^ Fintype.card ι) := by
  have hR : 0 ≤ R := hS.trans hRS
  have hshape := haarRootCube_shift_shell ι v (R := R) hS hv
  have houter : volume (haarRootCube ι (R + S)) < ∞ := isCompact_Icc.measure_lt_top
  have hset := norm_setIntegral_sub_le_common_shell_banach volume
    (s := (fun z ↦ z + v) '' haarRootCube ι R) (t := haarRootCube ι R)
    (core := haarRootCube ι (R - S)) (outer := haarRootCube ι (R + S))
    measurableSet_Icc houter hshape.2.1 hshape.1 hshape.2.2.2 hshape.2.2.1 hf hC hbound
  rw [(measurePreserving_add_right volume v).setIntegral_image_emb
    (MeasurableEquiv.addRight v).measurableEmbedding] at hset
  rw [volume_real_haarRootCube ι (by linarith),
    volume_real_haarRootCube ι (sub_nonneg.mpr hRS)] at hset
  rw [integral_haarCubeRootLaw_banach hR, integral_haarCubeRootLaw_banach hR,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((2 * R) ^ Fintype.card ι)⁻¹ *
        (2 * C * ((2 * (R + S)) ^ Fintype.card ι -
          (2 * (R - S)) ^ Fintype.card ι)) :=
      mul_le_mul_of_nonneg_left hset (by positivity)
    _ = _ := by ring

/-- Fixed translations of a genuinely bounded Banach observable have
vanishing difference of their ACTUAL normalized cube averages. -/
theorem tendsto_integral_haarCubeRootLaw_shift_sub_banach
    {f : (ι → ℝ) → V} (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) (v : ι → ℝ) :
    Tendsto (fun R : ℝ ↦
      (∫ z, f (z + v) ∂haarCubeRootLaw ι R) - ∫ z, f z ∂haarCubeRootLaw ι R)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Filter.eventually_atTop.2 ⟨‖v‖, fun R hR ↦ ?_⟩)
    (tendsto_haarCube_boundaryError (Fintype.card ι) C ‖v‖)
  exact norm_integral_haarCubeRootLaw_shift_sub_le_banach hf hC hbound v
    (norm_nonneg _) hR (fun i ↦ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)

section HilbertAverages

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (U : (ι → ℝ) → H ≃ₗᵢ[ℝ] H)
  (hcont : ∀ x, Continuous (fun v ↦ U v x))
include hcont

omit [CompleteSpace H] in
/-- A strongly continuous isometric orbit is genuinely Bochner-integrable
under each positive-radius original normalized Haar cube law. -/
theorem integrable_stationaryHaarCubeOrbit {R : ℝ} (hR : 0 < R) (x : H) :
    Integrable (fun v ↦ U v x) (haarCubeRootLaw ι R) := by
  have : IsProbabilityMeasure (haarCubeRootLaw ι R) :=
    isProbabilityMeasure_haarCubeRootLaw ι hR
  have hb : ∀ v, ‖U v x‖ ≤ ‖x‖ := fun v ↦ ((U v).norm_map x).le
  exact ⟨(hcont x).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hb)⟩

/-- The actual positive-radius normalized cube average as a linear map. -/
def stationaryHaarCubeAverageLinear (R : ℝ) (hR : 0 < R) : H →ₗ[ℝ] H where
  toFun x := ∫ v, U v x ∂haarCubeRootLaw ι R
  map_add' x y := by
    simp_rw [map_add]
    exact integral_add (integrable_stationaryHaarCubeOrbit U hcont hR x)
      (integrable_stationaryHaarCubeOrbit U hcont hR y)
  map_smul' c x := by
    simp_rw [map_smul]
    exact integral_smul c _

omit [CompleteSpace H] in
/-- Averaging the actual isometric orbit contracts the original Hilbert norm. -/
theorem norm_stationaryHaarCubeAverageLinear_le {R : ℝ} (hR : 0 < R) (x : H) :
    ‖stationaryHaarCubeAverageLinear U hcont R hR x‖ ≤ ‖x‖ := by
  have : IsProbabilityMeasure (haarCubeRootLaw ι R) :=
    isProbabilityMeasure_haarCubeRootLaw ι hR
  change ‖∫ v, U v x ∂haarCubeRootLaw ι R‖ ≤ ‖x‖
  simpa using norm_integral_le_of_norm_le_const (μ := haarCubeRootLaw ι R)
    (Filter.Eventually.of_forall fun v ↦ ((U v).norm_map x).le)

/-- The literal normalized Bochner cube-average operator for positive radii.
At nonpositive radii it is zero; every positive-radius formula remains exact. -/
def stationaryHaarCubeAverage (R : ℝ) : H →L[ℝ] H :=
  if hR : 0 < R then
    (stationaryHaarCubeAverageLinear U hcont R hR).mkContinuous 1
      (fun x ↦ by simpa only [one_mul] using
        norm_stationaryHaarCubeAverageLinear_le U hcont hR x)
  else 0

omit [CompleteSpace H] in
/-- Every spatial cube-average operator is a contraction. -/
theorem norm_stationaryHaarCubeAverage_le (R : ℝ) :
    ‖stationaryHaarCubeAverage U hcont R‖ ≤ 1 := by
  unfold stationaryHaarCubeAverage
  split_ifs with hR
  · exact LinearMap.mkContinuous_norm_le _ (by norm_num) _
  · simp

omit [CompleteSpace H] in
/-- Positive-radius averaging retains its literal normalized Haar integral. -/
theorem stationaryHaarCubeAverage_apply {R : ℝ} (hR : 0 < R) (x : H) :
    stationaryHaarCubeAverage U hcont R x = ∫ v, U v x ∂haarCubeRootLaw ι R := by
  simp only [stationaryHaarCubeAverage, dite_eq_left hR, LinearMap.mkContinuous_apply]
  rfl

variable (hadd : ∀ a b x, U a (U b x) = U (a + b) x)
include hadd

/-- The ACTUAL cube averages annihilate each translation coboundary. The
proof uses the explicit translated-cube shell bound, with bound equal to the
original vector norm, rather than an assumed mean-ergodic limit. -/
theorem tendsto_stationaryHaarCubeAverage_coboundary (a : ι → ℝ) (x : H) :
    Tendsto (fun R : ℝ ↦ stationaryHaarCubeAverage U hcont R (U a x - x))
      atTop (𝓝 0) := by
  have hlim := tendsto_integral_haarCubeRootLaw_shift_sub_banach
    (hcont x).aestronglyMeasurable (norm_nonneg x)
    (fun v ↦ ((U v).norm_map x).le) a
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [stationaryHaarCubeAverage_apply U hcont hR]
  symm
  calc
    (∫ v, U v (U a x - x) ∂haarCubeRootLaw ι R) =
        ∫ v, U v (U a x) - U v x ∂haarCubeRootLaw ι R := by
      congr 1
      funext v
      exact map_sub (U v) _ _
    _ = (∫ v, U v (U a x) ∂haarCubeRootLaw ι R) -
        ∫ v, U v x ∂haarCubeRootLaw ι R :=
      integral_sub (integrable_stationaryHaarCubeOrbit U hcont hR (U a x))
        (integrable_stationaryHaarCubeOrbit U hcont hR x)
    _ = _ := by simp_rw [hadd]

/-- Actual normalized Haar cube averages converge strongly to zero on the
orthogonal complement of all spatial invariants. -/
theorem tendsto_stationaryHaarCubeAverage_zero
    {x : H} (hx : x ∈ (translationFixedSubspace U ⊤)ᗮ) :
    Tendsto (fun R : ℝ ↦ stationaryHaarCubeAverage U hcont R x) atTop (𝓝 0) := by
  exact tendsto_contractions_zero_of_translation_coboundaries atTop U
    (stationaryHaarCubeAverage U hcont) (norm_stationaryHaarCubeAverage_le U hcont)
    (tendsto_stationaryHaarCubeAverage_coboundary U hcont hadd) hx

/-- Continuous spatial box mean ergodicity: the original strongly continuous
unitary action averages to its full joint invariant orthogonal projection. -/
theorem tendsto_stationaryHaarCubeAverage_projection (x : H) :
    Tendsto (fun R : ℝ ↦ stationaryHaarCubeAverage U hcont R x) atTop
      (𝓝 ((translationFixedSubspace U ⊤).starProjection x)) := by
  let p := (translationFixedSubspace U ⊤).starProjection x
  have hp : p ∈ translationFixedSubspace U ⊤ := Submodule.starProjection_apply_mem _ _
  have hlim := tendsto_stationaryHaarCubeAverage_zero U hcont hadd
    (Submodule.sub_starProjection_mem_orthogonal (K := translationFixedSubspace U ⊤) x)
  have hevent : ∀ᶠ R : ℝ in atTop, stationaryHaarCubeAverage U hcont R p = p := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have : IsProbabilityMeasure (haarCubeRootLaw ι R) :=
      isProbabilityMeasure_haarCubeRootLaw ι hR
    rw [stationaryHaarCubeAverage_apply U hcont hR]
    apply integral_eq_const
    exact Filter.Eventually.of_forall fun v ↦ hp v (by trivial)
  have hplus : Tendsto (fun R : ℝ ↦
      stationaryHaarCubeAverage U hcont R (x - p) + p) atTop (𝓝 p) := by
    simpa only [zero_add] using hlim.add_const p
  apply hplus.congr'
  filter_upwards [hevent] with R hR
  rw [map_sub, hR]
  exact sub_add_cancel _ _

end HilbertAverages

section FaceAverages

variable {G H : Type*} [AddCommGroup G] [Module ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual box averages in linear FACE coordinates converge strongly to
the original action's invariant projection on that face's tangent range. -/
theorem tendsto_stationaryFaceHaarCubeAverage_projection
    (U : G → H ≃ₗᵢ[ℝ] H) (hadd : ∀ a b x, U a (U b x) = U (a + b) x)
    (L : (ι → ℝ) →ₗ[ℝ] G)
    (hcont : ∀ x, Continuous (fun v ↦ U (L v) x)) (x : H) :
    Tendsto (fun R : ℝ ↦ stationaryHaarCubeAverage (fun v ↦ U (L v)) hcont R x)
      atTop (𝓝 ((translationFixedSubspace U L.range).starProjection x)) := by
  have haddL : ∀ a b x, U (L a) (U (L b) x) = U (L (a + b)) x := by
    intro a b y
    simpa only [map_add] using hadd (L a) (L b) y
  simpa only [translationFixedSubspace_comp_linearMap] using
    tendsto_stationaryHaarCubeAverage_projection (fun v ↦ U (L v)) hcont haddL x

end FaceAverages

/-- For an ACTUAL strongly continuous measure-preserving translation action,
its literal L²-valued Haar averages converge to the ACTUAL invariant
conditional expectation, identified as a Hilbert orthogonal projection. -/
theorem tendsto_stationaryKoopmanHaarCubeAverage_condExpL2
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (T : (ι → ℝ) → Ω → Ω) (hT : ∀ a, MeasurePreserving (T a) P P)
    (hzero : T 0 = id) (haddT : ∀ a b ω, T a (T b ω) = T (a + b) ω)
    (hcont : ∀ f : Lp ℝ 2 P, Continuous (fun v ↦
      Lp.compMeasurePreserving (T v) (hT v) f)) (f : Lp ℝ 2 P) :
    Tendsto (fun R : ℝ ↦ stationaryHaarCubeAverage
      (stationaryKoopman P T hT hzero haddT) hcont R f) atTop
      (𝓝 (condExpL2 ℝ ℝ (aeInvariantEventSigma_le P T) f : Lp ℝ 2 P)) := by
  have : Fact (aeInvariantEventSigma P T ≤ mΩ) := ⟨aeInvariantEventSigma_le P T⟩
  have hlim := tendsto_stationaryHaarCubeAverage_projection
    (stationaryKoopman P T hT hzero haddT) hcont
    (stationaryKoopman_add P T hT hzero haddT) f
  simpa only [stationaryKoopman_jointFixed_eq_lpMeas,
    Submodule.starProjection_apply, condExpL2] using hlim

end OTSelector.Reconstruction
