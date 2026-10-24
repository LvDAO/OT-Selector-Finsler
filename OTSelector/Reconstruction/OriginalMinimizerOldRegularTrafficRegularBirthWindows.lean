import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirth
import OTSelector.Reconstruction.FinslerOriginalCompletePathClockPieces
import OTSelector.Reconstruction.OriginalRegularClockRegionGeometry

/-! Literal regular births and deaths reuse the actual dyadic narrow bands and
finite physical clock windows, with only finitely many endpoint-distance shells. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- The actual regular birth/death region in a pre-existing full-span birth window. -/
def originalRegularBirthWindowMask (H ε cap : ℝ) (side : Fin 2) (n j i ell : ℕ)
    (z : MarkClock) : ℝ≥0∞ :=
  if side = 0 then
    originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 1 z *
      D.originalSupportedLeftBirthPhysicalClockMask H cap n j i ell z
  else
    originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z *
      D.originalSupportedRightBirthPhysicalClockMask H cap n j i ell z

theorem measurable_originalRegularBirthWindowMask (H ε cap : ℝ) (side : Fin 2)
    (n j i ell : ℕ) : Measurable (D.originalRegularBirthWindowMask H ε cap side n j i ell) := by
  unfold originalRegularBirthWindowMask
  split_ifs
  · exact (measurable_originalClockTrafficRegionMask _ _ ε 1).mul
      (D.measurable_originalSupportedLeftBirthPhysicalClockMask H cap n j i ell)
  · exact (measurable_originalClockTrafficRegionMask _ _ ε 5).mul
      (D.measurable_originalSupportedRightBirthPhysicalClockMask H cap n j i ell)

theorem originalRegularBirthWindowMask_le_one (H ε cap : ℝ) (side : Fin 2)
    (n j i ell : ℕ) (z : MarkClock) : D.originalRegularBirthWindowMask H ε cap side n j i ell z ≤ 1 := by
  unfold originalRegularBirthWindowMask
  split_ifs
  · exact (mul_le_mul' (originalClockTrafficRegionMask_le_one _ _ ε 1 z)
      (D.originalSupportedLeftBirthPhysicalClockMask_le_one H cap n j i ell z)).trans_eq (one_mul _)
  · exact (mul_le_mul' (originalClockTrafficRegionMask_le_one _ _ ε 5 z)
      (D.originalSupportedRightBirthPhysicalClockMask_le_one H cap n j i ell z)).trans_eq (one_mul _)

/-- Every actual left regular birth belongs to the full-span birth family. -/
theorem originalRegularBirth_left_fullSpan_region_eq_one {H ε : ℝ}
    (hH : D.hi-D.lo ≤ H) (z : MarkClock)
    (hz : originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 1 z ≠ 0) :
    originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) H 0 z = 1 ∧
      D.originalLeftBirthClockRegionMask H z = 1 := by
  obtain ⟨hl,hh,ha,hb,hidx⟩ := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hz
  obtain ⟨hnear,hbirth,_⟩ := (originalClockTrafficRegionIndex_eq_one_iff _ _ _ z).mp hidx
  have hsource : z.1.1.1-(D.lo+S.level) ≤ H := by linarith
  have hzero : originalClockTrafficRegionIndex (D.lo+S.level) (D.hi+S.level) H z = 0 :=
    (originalClockTrafficRegionIndex_eq_zero_iff _ _ _ z).mpr ⟨hnear,hbirth,hsource⟩
  constructor
  · simp [originalClockTrafficRegionMask,Set.indicator,hl,hh,ha,hb,hzero]
  · apply indicator_of_mem
    change 0 < z.1.1.1-S.level-D.lo ∧ z.1.1.1-S.level-D.lo ≤ H ∧
      0 < z.2-z.1.1.1 ∧ z.2-z.1.1.1 ≤ z.1.1.1-S.level-D.lo
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

/-- The actual target-side regular death belongs to the reflected full-span birth family. -/
theorem originalRegularBirth_right_fullSpan_region_eq_one {H ε : ℝ}
    (hH : D.hi-D.lo ≤ H) (z : MarkClock)
    (hz : originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z ≠ 0) :
    originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) H 4 z = 1 ∧
      D.originalRightBirthClockRegionMask H z = 1 := by
  obtain ⟨hl,hh,ha,hb,hidx⟩ := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hz
  obtain ⟨hnear,hbirth,_⟩ := (originalClockTrafficRegionIndex_eq_five_iff _ _ _ z).mp hidx
  have htarget : D.hi+S.level-z.1.1.2 ≤ H := by linarith
  have hfour : originalClockTrafficRegionIndex (D.lo+S.level) (D.hi+S.level) H z = 4 :=
    (originalClockTrafficRegionIndex_eq_four_iff _ _ _ z).mpr ⟨hnear,hbirth,htarget⟩
  constructor
  · simp [originalClockTrafficRegionMask,Set.indicator,hl,hh,ha,hb,hfour]
  · apply indicator_of_mem
    change 0 < D.hi-(z.1.1.2-S.level) ∧ D.hi-(z.1.1.2-S.level) ≤ H ∧
      0 < z.1.1.2-z.2 ∧ z.1.1.2-z.2 ≤ D.hi-(z.1.1.2-S.level)
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

/-- The unchanged dyadic bands and finite physical windows reconstruct exactly
the literal supported regular birth or death mask, pointwise in the original pair. -/
theorem tsum_finiteSum_originalRegularBirthWindowMask
    {H ε cap : ℝ} (hH : 0 < H) (hspan : D.hi-D.lo ≤ H) (hcap : 0 < cap)
    (side : Fin 2) (z : MarkClock) :
    (∑' n : ℕ,∑' j : ℕ,∑ i ∈ Finset.range (dyadicBirthBandCount j),
      ∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
        D.originalRegularBirthWindowMask H ε cap side n j i ell z) =
    originalPairClockSupportMask qdim μ ν z *
      originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε
        (if side = 0 then 1 else 5) z := by
  fin_cases side
  · change (∑' n : ℕ,∑' j : ℕ,∑ i ∈ Finset.range (dyadicBirthBandCount j),
        ∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
          D.originalRegularBirthWindowMask H ε cap 0 n j i ell z) =
      originalPairClockSupportMask qdim μ ν z *
        originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 1 z
    let coeff := originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 1 z *
      originalPairClockSupportMask qdim μ ν z *
        originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) H 0 z
    have heq (n j i ell : ℕ) : D.originalRegularBirthWindowMask H ε cap 0 n j i ell z =
        coeff*D.originalLeftBirthPhysicalClockMask H cap n j i ell z := by
      dsimp [originalRegularBirthWindowMask,originalSupportedLeftBirthPhysicalClockMask,coeff]
      ac_rfl
    simp_rw [heq,← Finset.mul_sum,D.sum_originalLeftBirthPhysicalClockMask hH hcap]
    simp_rw [ENNReal.tsum_mul_left]
    rw [D.tsum_finiteSum_originalLeftBirthClockMask hH]
    by_cases hz : originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 1 z = 0
    · simp only [coeff,hz,zero_mul,mul_zero]
    · obtain ⟨hregion,hbirth⟩ := D.originalRegularBirth_left_fullSpan_region_eq_one hspan z hz
      simp only [coeff,hregion,hbirth,mul_one]
      ac_rfl
  · change (∑' n : ℕ,∑' j : ℕ,∑ i ∈ Finset.range (dyadicBirthBandCount j),
        ∑ ell ∈ Finset.range (birthPhysicalClockWindowCount cap),
          D.originalRegularBirthWindowMask H ε cap 1 n j i ell z) =
      originalPairClockSupportMask qdim μ ν z *
        originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z
    let coeff := originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z *
      originalPairClockSupportMask qdim μ ν z *
        originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) H 4 z
    have heq (n j i ell : ℕ) : D.originalRegularBirthWindowMask H ε cap 1 n j i ell z =
        coeff*D.originalRightBirthPhysicalClockMask H cap n j i ell z := by
      dsimp [originalRegularBirthWindowMask,originalSupportedRightBirthPhysicalClockMask,coeff]
      ac_rfl
    simp_rw [heq,← Finset.mul_sum,D.sum_originalRightBirthPhysicalClockMask hH hcap]
    simp_rw [ENNReal.tsum_mul_left]
    rw [D.tsum_finiteSum_originalRightBirthClockMask hH]
    by_cases hz : originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z = 0
    · simp only [coeff,hz,zero_mul,mul_zero]
    · obtain ⟨hregion,hbirth⟩ := D.originalRegularBirth_right_fullSpan_region_eq_one hspan z hz
      simp only [coeff,hregion,hbirth,mul_one]
      ac_rfl

/-- Only finitely many endpoint-distance shells can meet a regular birth
region. The elapsed-time dyadic index and its original band partition remain unchanged. -/
theorem exists_originalRegularBirthWindowMask_finite_shell_support
    {H ε : ℝ} (_hH : 0 < H) (hε : 0 < ε) :
    ∃ N : ℕ,∀ n ≥ N,∀ cap : ℝ,∀ side : Fin 2,∀ j i ell : ℕ,∀ z : MarkClock,
      D.originalRegularBirthWindowMask H ε cap side n j i ell z = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (H/ε)
  have hpow (n : ℕ) : (n:ℝ)+1 ≤ (2:ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n hn =>
        simp only [Nat.cast_add,Nat.cast_one,pow_succ]
        nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n := n)]
  refine ⟨N,?_⟩
  intro n hn cap side j i ell z
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast hn
  have ht : 2*birthDyadicShellScale H n ≤ ε := by
    rw [two_mul_birthDyadicShellScale]
    apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr
    have := (div_lt_iff₀ hε).mp hN
    nlinarith [hpow n]
  by_contra hz
  fin_cases side
  · have hmask := left_ne_zero_of_mul hz
    have hsupported := right_ne_zero_of_mul hz
    have hbirth := (D.originalSupportedLeftBirthPhysicalClockMask_birth H cap n j i ell z hsupported).1
    have hshell := (D.originalLeftBirthClockMask_clock_bounds H n j i z hbirth).1
    have hregion := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hmask
    have hregular := (originalClockTrafficRegionIndex_eq_one_iff _ _ _ z).mp hregion.2.2.2.2
    linarith [hshell.2,hregular.2.2]
  · have hmask := left_ne_zero_of_mul hz
    have hsupported := right_ne_zero_of_mul hz
    have hbirth := (D.originalSupportedRightBirthPhysicalClockMask_birth H cap n j i ell z hsupported).1
    have hshell := (D.originalRightBirthClockMask_clock_bounds H n j i z hbirth).1
    have hregion := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hmask
    have hregular := (originalClockTrafficRegionIndex_eq_five_iff _ _ _ z).mp hregion.2.2.2.2
    linarith [hshell.2,hregular.2.2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
