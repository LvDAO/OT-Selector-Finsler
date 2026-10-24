import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveFiniteMesh
import OTSelector.MeasureTheory.AtomlessClockMesh
import OTSelector.Probability.ClockPrefixMesh

/-!
# Uniform original Poisson prefix concentration on compact clock carriers

The finite clock mesh is selected from the original atomless marginal before
volume grows.  The same actual finite cloud is tested at every threshold,
including thresholds chosen after observing that cloud.
-/
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The original prefix counts preserve inclusion of the original clock sets. -/
theorem originalReserveClockCount_mono (q : ℕ) (z : MarkedCloudSpace q ℝ)
    {U V : Set ℝ} (hUV : U ⊆ V) :
    originalReserveClockCount q U z ≤ originalReserveClockCount q V z := by
  apply Finset.card_le_card
  intro i hi
  obtain ⟨him, hiU⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨him, hUV hiU⟩

/-- All thresholds are tested against the same original count and clock law. -/
def originalReserveUniformPrefixBad (q : ℕ) (α : Measure ℝ) (r : ℝ≥0)
    (U : ℝ → Set ℝ) (K : Set ℝ) (ε : ℝ) : Set (MarkedCloudSpace q ℝ) :=
  {z | ∃ c ∈ K, (r : ℝ) * ε <
    |(originalReserveClockCount q (U c) z : ℝ) - (r : ℝ) * (α (U c)).toReal|}

/-- Interpolating the actual count turns any continuum bad event into a finite
mesh bad event.  No measurability or independence of a selected threshold is assumed. -/
theorem originalReserveUniformPrefixBad_subset_finiteDeviation
    {J : Type*} [Fintype J] (q : ℕ) (α : Measure ℝ) [IsFiniteMeasure α]
    (r : ℝ≥0) (U : ℝ → Set ℝ) (hUmono : Monotone U)
    (hUmass : ∀ c, α.real (U c) = α.real (Iic c))
    (K : Set ℝ) (lo hi : J → ℝ) (ε : ℝ)
    (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ c ∈ K, ∃ j, lo j ≤ c ∧ c ≤ hi j)
    (hstrip : ∀ j, α.real (Ioc (lo j) (hi j)) ≤ ε / 2) :
    originalReserveUniformPrefixBad q α r U K ε ⊆
      {z | (r : ℝ) * (ε / 2) ≤ originalReserveFiniteDeviation q α r
        (fun j : J × Bool ↦ U (if j.2 then hi j.1 else lo j.1)) z} := by
  intro z hz
  let sets : J × Bool → Set ℝ := fun j ↦ U (if j.2 then hi j.1 else lo j.1)
  let D := originalReserveFiniteDeviation q α r sets z
  have hendpoint (j : J × Bool) :
      |(originalReserveClockCount q (sets j) z : ℝ) - (r : ℝ) * α.real (sets j)| ≤ D :=
    Finset.single_le_sum (f := fun k : J × Bool ↦
      |(originalReserveClockCount q (sets k) z : ℝ) - (r : ℝ) * α.real (sets k)|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
  have hend (j : J) (b : Bool) :
      |(originalReserveClockCount q (U (if b then hi j else lo j)) z : ℝ) -
        (r : ℝ) * α.real (Iic (if b then hi j else lo j))| ≤ D := by
    simpa only [sets, hUmass] using hendpoint (j, b)
  have hbound : ∀ c ∈ K,
      |(originalReserveClockCount q (U c) z : ℝ) - (r : ℝ) * α.real (Iic c)| ≤
        D + (r : ℝ) * (ε / 2) := by
    apply abs_sub_le_of_monotone_mesh
      (fun c ↦ (originalReserveClockCount q (U c) z : ℝ))
      (fun c ↦ (r : ℝ) * α.real (Iic c))
      (fun _ _ h ↦ Nat.cast_le.mpr (originalReserveClockCount_mono q z (hUmono h)))
      (fun _ _ h ↦ mul_le_mul_of_nonneg_left (measureReal_mono (Iic_subset_Iic.mpr h))
        r.coe_nonneg) lo hi K D ((r : ℝ) * (ε / 2)) hcover
      (fun j ↦ by simpa using hend j false) (fun j ↦ by simpa using hend j true)
    intro j
    have heq : α.real (Iic (hi j)) - α.real (Iic (lo j)) =
        α.real (Ioc (lo j) (hi j)) := by
      rw [← Iic_sdiff_Iic]
      exact (measureReal_sdiff (Iic_subset_Iic.mpr (horder j)) measurableSet_Iic).symm
    rw [← mul_sub, heq]
    exact mul_le_mul_of_nonneg_left (hstrip j) r.coe_nonneg
  obtain ⟨c, hc, hbad⟩ := hz
  have hb := hbound c hc
  rw [← hUmass c] at hb
  change (r : ℝ) * (ε / 2) ≤ D
  change (r : ℝ) * ε <
    |(originalReserveClockCount q (U c) z : ℝ) - (r : ℝ) * α.real (U c)| at hbad
  linarith

/-- The internally chosen fixed mesh gives a square-root probability rate for
all original volumes.  Its constant is independent of the later volume. -/
theorem exists_originalReserveUniformPrefixBad_sqrtRate
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] [NullSingletonClass α]
    (U : ℝ → Set ℝ) (hUmeas : ∀ c, MeasurableSet (U c)) (hUmono : Monotone U)
    (hUmass : ∀ c, α.real (U c) = α.real (Iic c))
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0, 0 < r →
      (markedPoissonLaw q ℝ α r).real
        (originalReserveUniformPrefixBad q α r U K ε) ≤ C / Real.sqrt (r : ℝ) := by
  obtain ⟨t, lo, hi, horder, hcover, hstrip⟩ :=
    exists_finite_clockPrefixMesh α K hK (half_pos hε)
  let L : t → ℝ := fun j ↦ lo j
  let H : t → ℝ := fun j ↦ hi j
  have hc : ∀ c ∈ K, ∃ j : t, L j ≤ c ∧ c ≤ H j := by
    intro c hc
    obtain ⟨j, hj, hlj, hjh⟩ := hcover c hc
    exact ⟨⟨j, hj⟩, hlj, hjh⟩
  let sets : t × Bool → Set ℝ := fun j ↦ U (if j.2 then H j.1 else L j.1)
  refine ⟨(Fintype.card (t × Bool) : ℝ) / (ε / 2), by positivity, ?_⟩
  intro r hr
  have hsub := originalReserveUniformPrefixBad_subset_finiteDeviation q α r U hUmono
    hUmass K L H ε (fun j ↦ horder j j.2) hc (fun j ↦ hstrip j j.2)
  calc
    _ ≤ (markedPoissonLaw q ℝ α r).real
        {z | (r : ℝ) * (ε / 2) ≤ originalReserveFiniteDeviation q α r sets z} :=
      measureReal_mono hsub
    _ ≤ (Fintype.card (t × Bool) : ℝ) / ((ε / 2) * Real.sqrt (r : ℝ)) :=
      originalReserveFiniteDeviation_failure_bound q α r hr (half_pos hε)
        sets (fun _ ↦ hUmeas _)
    _ = _ := by rw [div_div]

/-- Every compact carrier enjoys uniform original-prefix concentration.  The
statement controls outer probability, so it also covers arbitrary adaptive thresholds. -/
theorem tendsto_originalReserveUniformPrefixBad_zero
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] [NullSingletonClass α]
    (U : ℝ → Set ℝ) (hUmeas : ∀ c, MeasurableSet (U c)) (hUmono : Monotone U)
    (hUmass : ∀ c, α.real (U c) = α.real (Iic c))
    (K : Set ℝ) (hK : IsCompact K)
    (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      (originalReserveUniformPrefixBad q α (r n) U K ε)) atTop (𝓝 0) := by
  obtain ⟨t, lo, hi, horder, hcover, hstrip⟩ :=
    exists_finite_clockPrefixMesh α K hK (half_pos hε)
  let L : t → ℝ := fun j ↦ lo j
  let H : t → ℝ := fun j ↦ hi j
  have hc : ∀ c ∈ K, ∃ j : t, L j ≤ c ∧ c ≤ H j := by
    intro c hc
    obtain ⟨j, hj, hlj, hjh⟩ := hcover c hc
    exact ⟨⟨j, hj⟩, hlj, hjh⟩
  let sets : t × Bool → Set ℝ := fun j ↦ U (if j.2 then H j.1 else L j.1)
  have hsub (n : ℕ) := originalReserveUniformPrefixBad_subset_finiteDeviation q α (r n)
    U hUmono hUmass K L H ε (fun j ↦ horder j j.2) hc (fun j ↦ hstrip j j.2)
  have hlim := tendsto_originalReserveFiniteDeviation_failure_zero q α r hr hrtop
    (half_pos hε) sets (fun _ ↦ hUmeas _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ ENNReal.toReal_nonneg) (fun n ↦ measureReal_mono (hsub n))

/-- Non-strict original prefixes are uniform in the threshold on any compact carrier. -/
theorem tendsto_originalReserveIic_bad_zero
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] [NullSingletonClass α]
    (K : Set ℝ) (hK : IsCompact K) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      (originalReserveUniformPrefixBad q α (r n) Iic K ε)) atTop (𝓝 0) :=
  tendsto_originalReserveUniformPrefixBad_zero q α Iic (fun _ ↦ measurableSet_Iic)
    (fun _ _ h ↦ Iic_subset_Iic.mpr h) (fun _ ↦ rfl) K hK r hr hrtop hε

/-- Strict original prefixes are controlled separately; sample ties at an adaptive
threshold are retained in the actual count rather than discarded. -/
theorem tendsto_originalReserveIio_bad_zero
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] [NullSingletonClass α]
    (K : Set ℝ) (hK : IsCompact K) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      (originalReserveUniformPrefixBad q α (r n) Iio K ε)) atTop (𝓝 0) := by
  apply tendsto_originalReserveUniformPrefixBad_zero q α Iio (fun _ ↦ measurableSet_Iio)
    (fun _ _ h ↦ Iio_subset_Iio h) ?_ K hK r hr hrtop hε
  intro c
  exact congrArg ENNReal.toReal (measure_congr (Iio_ae_eq_Iic (μ := α) (a := c)))

end OTSelector.Reconstruction
