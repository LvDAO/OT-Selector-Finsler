import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureRegularity
import OTSelector.Probability.GridRepairError

/-! Actual legal pressure is uniformly bounded after scale normalization.
The large-scale upper bound uses the proved legal grid comparison; its local
seed and the lower bound come directly from original finite cloud moments. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A finite-volume bound from the original expected source count. -/
theorem abs_legalMarkedPressure_le (q : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    |legalMarkedPressure q source target α β r kin probe t| ≤
      (r : ℝ) * ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G) := by
  have hI := integrable_legalMarkedTilted q hs ht α β r hC hG hk hkb hp hpb t
  have hB : 0 ≤ (r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G := by positivity
  have hpt (ω : TwoMarkedCloudSpace q A B) :
      |legalMarkedTilted q source target r kin probe t ω| ≤
      (mSourceCount ω : ℝ) * ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G) :=
    (abs_legalMarkedTilted_le q source target r.coe_nonneg hC hG hkb hpb t ω).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_left _ _)) hB)
  calc
    _ ≤ ∫ ω, |legalMarkedTilted q source target r kin probe t ω|
        ∂twoMarkedCloudLaw q A B α β r := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (mSourceCount ω : ℝ) * ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)
        ∂twoMarkedCloudLaw q A B α β r :=
      integral_mono hI.abs ((integrable_mSourceCount q α β r).mul_const _) hpt
    _ = _ := by rw [integral_mul_const, integral_mSourceCount_eq]

/-- The crude local scale bound is quadratic in the cube side. -/
theorem abs_legalMarkedScalePressure_le (q : ℕ) (hq : 0 < q)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) {L : ℝ} (hL : 0 < L) :
    |legalMarkedScalePressure q source target α β kin probe L t| ≤ L ^ 2 * (C * q) + |t| * G := by
  have h := abs_legalMarkedPressure_le q hs ht α β (Real.toNNReal (L ^ q)) hC hG hk hkb hp hpb t
  rw [Real.coe_toNNReal _ (pow_nonneg hL.le q)] at h
  have hpow : (L ^ q) ^ (2 / (q : ℝ)) = L ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    have hq' : (q : ℝ) * (2 / (q : ℝ)) = 2 := by
      field_simp
    rw [hq', Real.rpow_two]
  rw [hpow] at h
  simp only [legalMarkedScalePressure, hL, ↓reduceIte, abs_div, abs_of_pos (pow_pos hL q)]
  exact (div_le_iff₀ (pow_pos hL q)).mpr (by nlinarith [h])

/-- Nonnegative original kinetic energy gives a scale-independent lower bound. -/
theorem legalMarkedScalePressure_lower_bound (q : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) {L : ℝ} (hL : 0 < L) :
    -(|t| * G) ≤ legalMarkedScalePressure q source target α β kin probe L t := by
  have h := legalMarkedPressure_lower_bound q hs ht α β (Real.toNNReal (L ^ q)) hC hG hk
    (fun a b _ ↦ hkn a b) (fun a b _ ↦ hkb a b) hp (fun a b _ ↦ hpb a b) t
  rw [Real.coe_toNNReal _ (pow_nonneg hL.le q)] at h
  simp only [legalMarkedScalePressure, hL, ↓reduceIte]
  exact (le_div_iff₀ (pow_pos hL q)).mpr (by nlinarith [h])

/-- Actual legal block subadditivity upgrades the original finite-volume
estimate to a uniform bound for all large real cube scales. -/
theorem exists_legalMarkedScalePressure_bound_of_block
    (q : ℕ) (hq : 4 < q)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G K : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hK : 0 ≤ K)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G)
    (hblock : ∀ t (m : ℕ), 0 < m → ∀ L, 0 < L →
      legalMarkedScalePressure q source target α β kin probe ((m : ℝ) * L) t ≤
        legalMarkedScalePressure q source target α β kin probe L t + gridRepairError q K C G t L) :
    ∀ t, ∃ B : ℝ, ∀ R : ℝ, 1 ≤ R →
      |legalMarkedScalePressure q source target α β kin probe R t| ≤ B := by
  intro t
  let B : ℝ := 4 * (C * q) + |t| * G + 2 * K * (C + |t| * G)
  refine ⟨B, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let m : ℕ := Nat.floor R
  have hm : 0 < m := Nat.floor_pos.mpr hR
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let L := R / (m : ℝ)
  have hL1 : 1 ≤ L := (le_div_iff₀ hmR).mpr (by simpa using Nat.floor_le hRpos.le)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hL2 : L ≤ 2 := by
    have hlt : R < (m : ℝ) + 1 := Nat.lt_floor_add_one R
    exact (div_le_iff₀ hmR).mpr (by linarith)
  have heq : (m : ℝ) * L = R := mul_div_cancel₀ R hmR.ne'
  have hupper := hblock t m hm L hL
  rw [heq] at hupper
  have hlocal := (abs_le.mp (abs_legalMarkedScalePressure_le q (by omega) hs ht α β
    hC hG hk hkb hp hpb t hL)).2
  have herror : gridRepairError q K C G t L ≤ 2 * K * (C + |t| * G) := by
    have hqR : (4 : ℝ) < q := by exact_mod_cast hq
    have hkin : Real.rpow L (2 - (q : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith : 2 - (q : ℝ) / 2 ≤ 0)
    have hprobe : Real.rpow L (-((q : ℝ) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith : -((q : ℝ) / 2) ≤ 0)
    unfold gridRepairError
    have hcoef : 0 ≤ K * (C + |t| * G) := by positivity
    exact (mul_le_mul_of_nonneg_left (add_le_add hkin hprobe) hcoef).trans_eq (by ring)
  have hlower := legalMarkedScalePressure_lower_bound q hs ht α β hC hG hk hkn hkb hp hpb t hRpos
  have hLsq : L ^ 2 ≤ 4 := by nlinarith
  have hquadratic := mul_le_mul_of_nonneg_right hLsq (mul_nonneg hC (Nat.cast_nonneg q))
  rw [abs_le]
  constructor
  · have hBprobe : |t| * G ≤ B := by
      have hquad : 0 ≤ 4 * (C * q) := by positivity
      have herr : 0 ≤ 2 * K * (C + |t| * G) := by positivity
      dsimp [B]
      linarith
    linarith
  · dsimp [B]
    linarith

end OTSelector.Reconstruction
