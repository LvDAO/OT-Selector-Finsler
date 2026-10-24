import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReserveInput
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilationPalm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Concrete original reserve intensity and its actual energy scaling

A positive prescribed physical intensity determines the actual spatial
dilation. Complementary intensities give exactly the original unit Poisson
input law. The original retained value converges as its intensity tends to
one, and a fixed genuine reserve has vanishing kinetic cost at zero intensity
in every dimension strictly larger than two.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalReserveIntensityInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalReserveIntensityPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Physical dilation realizing the specified positive Haar intensity. -/
def legalIntensityDilation (q : ℕ) (ρ : ℝ) : ℝ := ρ ^ (-(q : ℝ)⁻¹)

theorem legalIntensityDilation_pos (q : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < legalIntensityDilation q ρ := Real.rpow_pos_of_pos hρ _

/-- The actual Haar Jacobian is exactly the prescribed original intensity. -/
theorem legalIntensityDilation_jacobian {q : ℕ} (hq : 0 < q) {ρ : ℝ} (hρ : 0 < ρ) :
    |((legalIntensityDilation q ρ) ^ q)⁻¹| = ρ := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow : (legalIntensityDilation q ρ) ^ q = ρ⁻¹ := by
    unfold legalIntensityDilation
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    have he : -(q : ℝ)⁻¹ * q = -1 := by field_simp
    rw [he, Real.rpow_neg_one]
  rw [hpow, inv_inv, abs_of_pos hρ]

/-- The actual original kinetic intensity is the correct fractional power,
with no silent renormalization of the displaced original point process. -/
theorem legalIntensityDilation_kinetic_scale {q : ℕ} (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) :
    |((legalIntensityDilation q ρ) ^ q)⁻¹| * (legalIntensityDilation q ρ) ^ 2 =
      ρ ^ (1 - 2 / (q : ℝ)) := by
  rw [legalIntensityDilation_jacobian hq hρ]
  unfold legalIntensityDilation
  have hsq : (ρ ^ (-(q : ℝ)⁻¹)) ^ 2 = ρ ^ (-(q : ℝ)⁻¹ * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  rw [hsq]
  calc
    _ = ρ ^ (1 : ℝ) * ρ ^ (-(q : ℝ)⁻¹ * 2) := by rw [Real.rpow_one]
    _ = ρ ^ (1 + -(q : ℝ)⁻¹ * 2) := (Real.rpow_add hρ _ _).symm
    _ = _ := by congr 1; ring

/-- No external Jacobian-sum hypothesis is needed for complementary actual
retained and reserve input intensities. -/
theorem legalIntensityDilation_complementary_jacobians {q : ℕ} (hq : 0 < q)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    |((legalIntensityDilation q (1 - θ)) ^ q)⁻¹| +
      |((legalIntensityDilation q θ) ^ q)⁻¹| = 1 := by
  rw [legalIntensityDilation_jacobian hq (sub_pos.mpr hθ1),
    legalIntensityDilation_jacobian hq hθ]
  ring

/-- The actual independently dilated original input copies realize precisely
the original unit-intensity compact Poisson field. -/
theorem original_complementary_intensity_reserve_input_laplace
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (S : ℝ) (hS : 0 < S) (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (hz : ∀ (x : LegalMarkedPhysicalPoint q) (k : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, k) = 0) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(legalMarkedReserveInputLaw q
      (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' M.law)
      (legalMarkedInputDilationLaw q (legalIntensityDilation q θ)
        (legalIntensityDilation_pos q hθ).ne' N.law) : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ z, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) z
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  exact original_dilated_reserve_input_laplace M N _ _ _ _
    (legalIntensityDilation_complementary_jacobians hq hθ hθ1) S hS F hF hz

/-- Retaining asymptotically all actual original input preserves its original
kinetic intensity factor. This statement works along any index filter. -/
theorem tendsto_legalIntensityDilation_kinetic_scale_one
    {J : Type*} {l : Filter J} {q : ℕ} (hq : 0 < q)
    {ρ : J → ℝ} (hρ : ∀ j, 0 < ρ j) (hlim : Tendsto ρ l (𝓝 1)) :
    Tendsto (fun j ↦ |((legalIntensityDilation q (ρ j)) ^ q)⁻¹| *
      (legalIntensityDilation q (ρ j)) ^ 2) l (𝓝 1) := by
  have h := hlim.rpow_const (p := 1 - 2 / (q : ℝ)) (Or.inl one_ne_zero)
  simpa only [legalIntensityDilation_kinetic_scale hq (hρ _), Real.one_rpow] using h

/-- A fixed actual original reserve has a vanishing kinetic intensity factor
at zero reserve density. No displacement moment is being inferred. -/
theorem tendsto_legalIntensityDilation_kinetic_scale_zero
    {J : Type*} {l : Filter J} {q : ℕ} (hq : 2 < q)
    {ρ : J → ℝ} (hρ : ∀ j, 0 < ρ j) (hlim : Tendsto ρ l (𝓝 0)) :
    Tendsto (fun j ↦ |((legalIntensityDilation q (ρ j)) ^ q)⁻¹| *
      (legalIntensityDilation q (ρ j)) ^ 2) l (𝓝 0) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have he : (0 : ℝ) < 1 - 2 / (q : ℝ) := by
    have hq2 : (2 : ℝ) < q := by exact_mod_cast hq
    exact sub_pos.mpr ((div_lt_one hq0).mpr hq2)
  simpa only [legalIntensityDilation_kinetic_scale (show 0 < q by omega) (hρ _)] using
    hlim.rpow_const_nhds_zero he

/-- Retain the same original matching at intensity one minus theta and add
an independently sampled original reserve at intensity theta. -/
def legalOriginalIntensityReserveLaw
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  legalMarkedReserveInputLaw q
    (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' M.law)
    (legalMarkedInputDilationLaw q (legalIntensityDilation q θ)
      (legalIntensityDilation_pos q hθ).ne' N.law)

/-- The actual retained Palm keeps the whole original pair law from the
first original copy; the second original input reserve remains unused. -/
theorem legalMarkedJointPalm_originalIntensityReserveLaw
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    legalMarkedJointPalm q (legalOriginalIntensityReserveLaw M N θ hθ hθ1) =
      legalMarkedJointPalm q (legalMarkedInputDilationLaw q (legalIntensityDilation q (1 - θ))
        (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne' M.law) := by
  unfold legalMarkedJointPalm legalOriginalIntensityReserveLaw
  rw [legalMarkedInputPairLaw_reserveInputLaw]

/-- The actual retained original kinetic expectation has its exact
complementary intensity scaling on the actual superposed input scene. -/
theorem integral_kinetic_originalIntensityReserveLaw
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v, kin a b (c • v) = c ^ 2 * kin a b v)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ m, kin m.1.1 m.1.2 m.2
      ∂legalMarkedJointPalm q (legalOriginalIntensityReserveLaw M N θ hθ hθ1)) =
      (1 - θ) ^ (1 - 2 / (q : ℝ)) *
        ∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q M.law := by
  rw [legalMarkedJointPalm_originalIntensityReserveLaw]
  change (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q
    (M.law.map (continuous_legalMarkedInputSceneDilation q (legalIntensityDilation q (1 - θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne').measurable.aemeasurable)) = _
  rw [integral_kinetic_dilated_legalMarkedJointPalm M _ _ hk
      (fun a b v ↦ hhom a b _ (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).le v),
    legalIntensityDilation_kinetic_scale hq (sub_pos.mpr hθ1)]

/-- The original paired-clock probe is retained with exactly its actual
source intensity, while its clocks themselves are unchanged. -/
theorem integral_probe_originalIntensityReserveLaw
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hg : Measurable (Function.uncurry g))
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ m, g m.1.1 m.1.2
      ∂legalMarkedJointPalm q (legalOriginalIntensityReserveLaw M N θ hθ hθ1)) =
      (1 - θ) * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q M.law := by
  rw [legalMarkedJointPalm_originalIntensityReserveLaw]
  change (∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q
    (M.law.map (continuous_legalMarkedInputSceneDilation q (legalIntensityDilation q (1 - θ))
      (legalIntensityDilation_pos q (sub_pos.mpr hθ1)).ne').measurable.aemeasurable)) = _
  rw [integral_probe_dilated_legalMarkedJointPalm M _ _ hg,
    legalIntensityDilation_jacobian hq (sub_pos.mpr hθ1)]

/-- The literal retained kinetic-plus-probe expectation converges to the
unchanged original matching value as the actual reserve intensity tends to
zero. The index filter is arbitrary and the matching law is fixed. -/
theorem tendsto_originalIntensityReserveLaw_value
    {J : Type*} {l : Filter J} {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v, kin a b (c • v) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (θ : J → ℝ) (hθ : ∀ j, 0 < θ j) (hθ1 : ∀ j, θ j < 1)
    (hlim : Tendsto θ l (𝓝 0)) :
    Tendsto (fun j ↦
      (∫ m, kin m.1.1 m.1.2 m.2
        ∂legalMarkedJointPalm q (legalOriginalIntensityReserveLaw M N (θ j) (hθ j) (hθ1 j))) +
        t * ∫ m, g m.1.1 m.1.2
          ∂legalMarkedJointPalm q (legalOriginalIntensityReserveLaw M N (θ j) (hθ j) (hθ1 j)))
      l (𝓝 (M.value t)) := by
  have hretained : Tendsto (fun j ↦ 1 - θ j) l (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hlim
  have hpower := hretained.rpow_const (p := 1 - 2 / (q : ℝ)) (Or.inl one_ne_zero)
  have hkin := hpower.mul_const
    (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q M.law)
  have hprobe := (hretained.mul_const
    (∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q M.law)).const_mul t
  simpa only [integral_kinetic_originalIntensityReserveLaw hq M N hk hhom,
    integral_probe_originalIntensityReserveLaw hq M N hg, Real.one_rpow, one_mul,
    LegalWeightedStationaryPoissonMatching.value] using hkin.add hprobe

/-- The actual kinetic expectation of a fixed reserve vanishes when diluted
to zero density in dimension greater than two. This uses the genuine finite
weighted energy of that same reserve, without a varying-law tail argument. -/
theorem tendsto_original_reserve_kinetic_zero
    {J : Type*} {l : Filter J} {q : ℕ} (hq : 2 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v, kin a b (c • v) = c ^ 2 * kin a b v)
    (θ : J → ℝ) (hθ : ∀ j, 0 < θ j) (hlim : Tendsto θ l (𝓝 0)) :
    Tendsto (fun j ↦ ∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q
      (legalMarkedInputDilationLaw q (legalIntensityDilation q (θ j))
        (legalIntensityDilation_pos q (hθ j)).ne' N.law)) l (𝓝 0) := by
  have hscale := tendsto_legalIntensityDilation_kinetic_scale_zero hq hθ hlim
  have h := hscale.mul_const (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q N.law)
  convert h using 1
  · funext j
    exact integral_kinetic_dilated_legalMarkedJointPalm N _ _ hk
      (fun a b v ↦ hhom a b _ (legalIntensityDilation_pos q (hθ j)).le v)
  · rw [zero_mul]

end OTSelector.Reconstruction
