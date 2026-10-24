import OTSelector.Reconstruction.OriginalLegalWeightedReserveClockBudget
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveUniformClockSlack
import OTSelector.Reconstruction.FinslerOriginalSeedMomentsBundled
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockNull

/-!
# Uniform clock budgets on the unchanged original reserve coordinate

Finite meshes of the original atomless clock law control every real threshold
of the same original reserve input, including thresholds chosen from that input.
Physical truncation and the exact reserve dilation are retained throughout.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

local instance reserveUniformClockInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance reserveUniformClockPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The two actual tail conventions remain distinct at sample thresholds. -/
def legalOriginalTailSet (closed : Bool) (a : ℝ) : Set ℝ :=
  if closed then Ici a else Ioi a

theorem measurableSet_legalOriginalTailSet (closed : Bool) (a : ℝ) :
    MeasurableSet (legalOriginalTailSet closed a) := by
  cases closed <;> simp only [legalOriginalTailSet, Bool.false_eq_true, ite_false, ite_true]
  · exact measurableSet_Ioi
  · exact measurableSet_Ici

theorem antitone_legalOriginalTailSet (closed : Bool) : Antitone (legalOriginalTailSet closed) := by
  cases closed
  · exact fun _ _ h ↦ Ioi_subset_Ioi h
  · exact fun _ _ h ↦ Ici_subset_Ici.mpr h

/-- Atomlessness identifies population masses, while the original strict and
closed empirical count sets themselves are left intact. -/
theorem legalOriginalTailSet_real_eq_total_sub_prefix
    (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (closed : Bool) (a : ℝ) :
    μ.real (legalOriginalTailSet closed a) = μ.real univ - μ.real (Iic a) := by
  cases closed
  · change μ.real (Ioi a) = _
    rw [← compl_Iic, measureReal_compl measurableSet_Iic]
  · change μ.real (Ici a) = _
    rw [← compl_Iio, measureReal_compl measurableSet_Iio]
    exact congrArg (fun r : ℝ ↦ μ.real univ - r)
      (congrArg ENNReal.toReal (measure_congr (Iio_ae_eq_Iic (μ := μ) (a := a))))

/-- A finite mesh and one total-count error control an antitone count at all
real thresholds. The two unbounded ends use only their original small tail
masses; no chosen threshold needs to be measurable. -/
theorem abs_sub_le_of_global_antitone_mesh
    {J : Type*} (F G : ℝ → ℝ) (hF : Antitone F) (hG : Antitone G)
    (ft gt D e lo hi : ℝ) (hFn : ∀ a, 0 ≤ F a) (hGn : ∀ a, 0 ≤ G a)
    (hFt : ∀ a, F a ≤ ft) (hGt : ∀ a, G a ≤ gt)
    (hlo : |F lo - G lo| ≤ D) (hhi : |F hi - G hi| ≤ D)
    (htotal : |ft - gt| ≤ D) (hlow : gt - G lo ≤ e) (hhigh : G hi ≤ e)
    (L H : J → ℝ)
    (hcover : ∀ a ∈ Icc lo hi, ∃ j, L j ≤ a ∧ a ≤ H j)
    (hL : ∀ j, |F (L j) - G (L j)| ≤ D)
    (hH : ∀ j, |F (H j) - G (H j)| ≤ D)
    (hgap : ∀ j, G (L j) - G (H j) ≤ e) :
    ∀ a : ℝ, |F a - G a| ≤ D + e := by
  intro a
  by_cases hla : lo ≤ a
  · by_cases hah : a ≤ hi
    · have h := abs_sub_le_of_monotone_mesh (fun a ↦ -F a) (fun a ↦ -G a)
        (fun _ _ h ↦ neg_le_neg (hF h)) (fun _ _ h ↦ neg_le_neg (hG h))
        L H (Icc lo hi) D e hcover
        (fun j ↦ by simpa only [neg_sub_neg, abs_sub_comm] using hL j)
        (fun j ↦ by simpa only [neg_sub_neg, abs_sub_comm] using hH j)
        (fun j ↦ by simpa only [neg_sub_neg] using hgap j) a ⟨hla, hah⟩
      simpa only [neg_sub_neg, abs_sub_comm] using h
    · have hfa := hF (le_of_not_ge hah)
      have hga := hG (le_of_not_ge hah)
      have hh := abs_le.mp hhi
      exact abs_le.mpr ⟨by linarith [hFn a, hGn a], by linarith [hFn a, hGn a]⟩
  · have hfa := hF (le_of_not_ge hla)
    have hga := hG (le_of_not_ge hla)
    have hl := abs_le.mp hlo
    have ht := abs_le.mp htotal
    exact abs_le.mpr ⟨by linarith [hFt a, hGt a], by linarith [hFt a, hGt a]⟩

/-- The original finite clock law supplies deterministic finite end cutoffs
with arbitrarily small two-sided original mass outside them. -/
theorem exists_originalClock_end_tail_bounds
    (γ : Measure ℝ) [IsFiniteMeasure γ] {ε : ℝ} (hε : 0 < ε) :
    ∃ L > 0, γ.real (Iic (-L)) ≤ ε ∧ γ.real (Ici L) ≤ ε := by
  obtain ⟨K, hK, htail⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := γ)) (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨L, hL, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  have hm : γ.real Kᶜ ≤ ε := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail γ (mem_singleton γ))
    simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using hh
  refine ⟨L, hL, (measureReal_mono ?_).trans hm, (measureReal_mono ?_).trans hm⟩
  · intro x hx hxK
    have hb := hbound x hxK
    rw [Real.norm_eq_abs] at hb
    have := (abs_lt.mp hb).1
    exact (not_le_of_gt this) hx
  · intro x hx hxK
    have hb := hbound x hxK
    rw [Real.norm_eq_abs] at hb
    exact (not_lt_of_ge hx) (abs_lt.mp hb).2

/-- Literal clock-set count in a physically dilated original input window. -/
def legalOriginalReserveInputClockCount (q : ℕ) (d : ℝ) (hd : d ≠ 0)
    (V : Set (Fin q → ℝ)) (A T : Set ℝ) (color : Fin 2)
    (s : LegalMarkedOptimalInputScene q) : ℝ :=
  legalOriginalWindowCount q ((V ×ˢ A) ∩ (univ ×ˢ T)) color
    (legalMarkedInputSceneDilation q d hd s)

/-- The true physical reserve rate is its inverse dilation Jacobian times
the literal spatial volume of the window. -/
def legalOriginalReserveSpatialRate (q : ℕ) (d : ℝ) (V : Set (Fin q → ℝ)) : ℝ :=
  |(d ^ q)⁻¹| * (volume V).toReal

/-- Evaluation of a locally finite original input is monotone on bounded
physical windows, with its multiplicities preserved. -/
theorem legalOriginalWindowCount_mono_bounded {q : ℕ}
    (s : LegalMarkedOptimalInputScene q) (color : Fin 2)
    {B C K : Set (LegalMarkedPhysicalPoint q)}
    (hK : IsCompact K) (hBC : B ⊆ C) (hCK : C ⊆ K) :
    legalOriginalWindowCount q B color s ≤ legalOriginalWindowCount q C color s := by
  apply ENNReal.toReal_mono
    (((measure_mono (Set.prod_mono hCK (Subset.refl _))).trans_lt
      (hK.prod isCompact_singleton).measure_lt_top).ne)
  exact measure_mono (Set.prod_mono hBC (Subset.refl _))

/-- The deterministic original clock-set mean of the same physical window. -/
theorem legalOriginalReserveInputClockCount_mean
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (d : ℝ) (V : Set (Fin q → ℝ)) (A : Set ℝ)
    {T : Set ℝ} (hT : MeasurableSet T) (color : Fin 2) :
    legalOriginalDilatedWindowMean q α β d ((V ×ˢ A) ∩ (univ ×ˢ T)) color =
      legalOriginalReserveSpatialRate q d V *
        ((legalOriginalColorClock α β color).restrict A).real T := by
  rw [legalOriginalDilatedWindowMean_prod_inter_clock α β d, legalOriginalReserveSpatialRate,
    Measure.real, Measure.restrict_apply hT, inter_comm]

/-- Genuine clock-set count deviations have a square-root spatial-volume
budget uniformly in the physical clock truncation. -/
theorem LegalWeightedStationaryPoissonMatching.reserveInputClockCount_deviation_integrable_bound
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0) {V : Set (Fin q → ℝ)} (hV : IsCompact V)
    {A T : Set ℝ} (hA : IsCompact A) (hT : MeasurableSet T) (color : Fin 2) :
    let r := legalOriginalReserveSpatialRate q d V
    let μ := (legalOriginalColorClock α β color).restrict A
    Integrable (fun s ↦ |legalOriginalReserveInputClockCount q d hd V A T color s - r * μ.real T|)
      (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, |legalOriginalReserveInputClockCount q d hd V A T color s - r * μ.real T|
      ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) ≤ Real.sqrt r := by
  dsimp only
  have hB := (hV.measurableSet.prod hA.measurableSet).inter (MeasurableSet.univ.prod hT)
  obtain ⟨hI, hb⟩ := N.dilated_windowCount_deviation_integrable_bound d hd hB
    (hV.prod hA) inter_subset_left color
  have hm := legalOriginalReserveInputClockCount_mean α β d V A hT color
  dsimp only [legalOriginalDilatedWindowMean] at hm
  have hbound := legalOriginalDilatedWindowMean_le_spatialVolume α β d hV.measurableSet
    hV.measure_lt_top.ne
    (inter_subset_left.trans (Set.prod_mono (Subset.refl _) (subset_univ _)) :
      (V ×ˢ A) ∩ (univ ×ˢ T) ⊆ V ×ˢ univ) color
  refine ⟨?_, ?_⟩
  · simpa only [legalOriginalReserveInputClockCount, hm] using hI
  · have hh := hb.trans (Real.sqrt_le_sqrt hbound)
    simpa only [legalOriginalReserveInputClockCount, hm, legalOriginalReserveSpatialRate] using hh

/-- The actual endpoint statistic used by the deterministic clock mesh. -/
def legalOriginalReserveWindowFiniteError {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) (d : ℝ) (hd : d ≠ 0)
    (V : Set (Fin q → ℝ)) (A : Set ℝ) (T : J → Set ℝ) (color : Fin 2)
    (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∑ j, |legalOriginalReserveInputClockCount q d hd V A (T j) color s -
    legalOriginalReserveSpatialRate q d V *
      ((legalOriginalColorClock α β color).restrict A).real (T j)|

/-- The finite mesh endpoints are bounded using their genuine original
Poisson count laws, without an iid law for any ordered reserve subarray. -/
theorem LegalWeightedStationaryPoissonMatching.reserveWindowFiniteError_integrable_bound
    {J : Type*} [Fintype J] {q : ℕ} {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0) {V : Set (Fin q → ℝ)} (hV : IsCompact V)
    {A : Set ℝ} (hA : IsCompact A) (T : J → Set ℝ)
    (hT : ∀ j, MeasurableSet (T j)) (color : Fin 2) :
    Integrable (legalOriginalReserveWindowFiniteError q α β d hd V A T color)
      (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, legalOriginalReserveWindowFiniteError q α β d hd V A T color s
        ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        (Fintype.card J : ℝ) * Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  have h (j : J) := N.reserveInputClockCount_deviation_integrable_bound d hd hV hA (hT j) color
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (h j).1), ?_⟩
  unfold legalOriginalReserveWindowFiniteError
  rw [integral_finsetSum _ (fun j _ ↦ (h j).1)]
  exact (Finset.sum_le_sum (fun j _ ↦ (h j).2)).trans_eq (by simp)

/-- The endpoint error statistic is measurable on the same original scene. -/
theorem measurable_legalOriginalReserveWindowFiniteError
    {J : Type*} [Fintype J] (q : ℕ) (α β : Measure ℝ) (d : ℝ) (hd : d ≠ 0)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V) {A : Set ℝ} (hA : MeasurableSet A)
    (T : J → Set ℝ) (hT : ∀ j, MeasurableSet (T j)) (color : Fin 2) :
    Measurable (legalOriginalReserveWindowFiniteError q α β d hd V A T color) := by
  apply Finset.measurable_sum
  intro j _
  exact (((measurable_legalOriginalWindowCount q
    ((hV.prod hA).inter (MeasurableSet.univ.prod (hT j))) color).comp
      (continuous_legalMarkedInputSceneDilation q d hd).measurable).sub measurable_const).abs

/-- A bad event tests every real clock threshold of the same actual input.
No measurability or independence of a later chosen threshold is required. -/
def legalOriginalReserveUniformClockBad (q : ℕ) (α β : Measure ℝ)
    (d : ℝ) (hd : d ≠ 0) (V : Set (Fin q → ℝ)) (A : Set ℝ)
    (closed : Bool) (color : Fin 2) (ε : ℝ) : Set (LegalMarkedOptimalInputScene q) :=
  {s | ∃ a : ℝ, legalOriginalReserveSpatialRate q d V * ε <
    |legalOriginalReserveInputClockCount q d hd V A (legalOriginalTailSet closed a) color s -
      legalOriginalReserveSpatialRate q d V *
        ((legalOriginalColorClock α β color).restrict A).real (legalOriginalTailSet closed a)|}

/-- A mesh of the unchanged atomless clock law supplies a measurable
exceptional event controlling ALL real thresholds of the actual reserve.
Its constant is independent of spatial volume, dilation, and clock truncation. -/
theorem LegalWeightedStationaryPoissonMatching.exists_reserveUniformClockBad_measurable_cover
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (closed : Bool) (color : Fin 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (hd : d ≠ 0)
      (V : Set (Fin q → ℝ)) (_hV : IsCompact V) (A : Set ℝ) (_hA : IsCompact A),
      0 < legalOriginalReserveSpatialRate q d V →
      ∃ E : Set (LegalMarkedOptimalInputScene q), MeasurableSet E ∧
        legalOriginalReserveUniformClockBad q α β d hd V A closed color ε ⊆ E ∧
        (N.law : Measure (LegalMarkedOptimalInputScene q)).real E ≤
          C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  let γ := legalOriginalColorClock α β color
  have : IsProbabilityMeasure γ := by
    fin_cases color <;> dsimp [γ, legalOriginalColorClock] <;> infer_instance
  have : NullSingletonClass γ := by
    fin_cases color <;> dsimp [γ, legalOriginalColorClock] <;> infer_instance
  have heps : 0 < ε / 4 := by positivity
  obtain ⟨L, hL, hleft, hright⟩ := exists_originalClock_end_tail_bounds γ heps
  obtain ⟨t, lo, hi, horder, hcover, hstrip⟩ :=
    exists_finite_clockPrefixMesh γ (Icc (-L) L) isCompact_Icc heps
  let labels := Option (t × Bool)
  let T : labels → Set ℝ := fun j ↦ match j with
    | none => univ
    | some (k, b) => legalOriginalTailSet closed (if b then hi k else lo k)
  have hT (j : labels) : MeasurableSet (T j) := by
    cases j with
    | none => exact MeasurableSet.univ
    | some p => exact measurableSet_legalOriginalTailSet _ _
  refine ⟨(Fintype.card labels : ℝ) / (ε / 2), by positivity, ?_⟩
  intro d hd V hV A hA hr
  let r := legalOriginalReserveSpatialRate q d V
  let μ := γ.restrict A
  let D := legalOriginalReserveWindowFiniteError q α β d hd V A T color
  have hDn (s) : 0 ≤ D s := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hD := measurable_legalOriginalReserveWindowFiniteError q α β d hd
    hV.measurableSet hA.measurableSet T hT color
  let E : Set (LegalMarkedOptimalInputScene q) := {s | r * (ε / 2) ≤ D s}
  refine ⟨E, measurableSet_le measurable_const hD, ?_, ?_⟩
  · intro s hs
    have hendpoint (j : labels) :
        |legalOriginalReserveInputClockCount q d hd V A (T j) color s - r * μ.real (T j)| ≤ D s :=
      Finset.single_le_sum
        (f := fun j : labels ↦ |legalOriginalReserveInputClockCount q d hd V A (T j) color s -
          r * μ.real (T j)|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
    let F := fun a ↦ legalOriginalReserveInputClockCount q d hd V A
      (legalOriginalTailSet closed a) color s
    let G := fun a ↦ r * μ.real (legalOriginalTailSet closed a)
    let ft := legalOriginalReserveInputClockCount q d hd V A univ color s
    let gt := r * μ.real univ
    have hF : Antitone F := by
      intro a b hab
      apply legalOriginalWindowCount_mono_bounded _ color (hV.prod hA) _ inter_subset_left
      exact Set.inter_subset_inter_right _
        (Set.prod_mono (Subset.refl _) (antitone_legalOriginalTailSet closed hab))
    have hG : Antitone G := by
      intro a b hab
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono (antitone_legalOriginalTailSet closed hab)) hr.le
    have hFt (a) : F a ≤ ft := by
      apply legalOriginalWindowCount_mono_bounded _ color (hV.prod hA) _ inter_subset_left
      exact Set.inter_subset_inter_right _ (Set.prod_mono (Subset.refl _) (subset_univ _))
    have hGt (a) : G a ≤ gt :=
      mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ _)) hr.le
    have hm (B : Set ℝ) : μ.real B ≤ γ.real B :=
      ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_le_self B)
    have hgap (j : t) : G (lo j) - G (hi j) ≤ r * (ε / 4) := by
      have heq : μ.real (Iic (hi j)) - μ.real (Iic (lo j)) = μ.real (Ioc (lo j) (hi j)) := by
        rw [← Iic_sdiff_Iic]
        exact (measureReal_sdiff (Iic_subset_Iic.mpr (horder j j.2)) measurableSet_Iic).symm
      have hg : G (lo j) - G (hi j) = r * μ.real (Ioc (lo j) (hi j)) := by
        dsimp only [G]
        rw [legalOriginalTailSet_real_eq_total_sub_prefix,
          legalOriginalTailSet_real_eq_total_sub_prefix]
        rw [← heq]
        ring
      rw [hg]
      exact mul_le_mul_of_nonneg_left ((hm _).trans (hstrip j j.2)) hr.le
    have hlow : gt - G (-L) ≤ r * (ε / 4) := by
      have heq : gt - G (-L) = r * μ.real (Iic (-L)) := by
        dsimp only [gt, G]
        rw [legalOriginalTailSet_real_eq_total_sub_prefix]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left ((hm _).trans hleft) hr.le
    have hhigh : G L ≤ r * (ε / 4) := by
      have hs : legalOriginalTailSet closed L ⊆ Ici L := by
        cases closed
        · exact Ioi_subset_Ici_self
        · exact Subset.refl _
      exact mul_le_mul_of_nonneg_left
        ((hm _).trans ((measureReal_mono hs).trans hright)) hr.le
    have hlo (j : t) : |F (lo j) - G (lo j)| ≤ D s := by
      simpa only [T, Bool.false_eq_true, ite_false] using hendpoint (some (j, false))
    have hhi (j : t) : |F (hi j) - G (hi j)| ≤ D s := by
      simpa only [T, ite_true] using hendpoint (some (j, true))
    have hcov : ∀ a ∈ Icc (-L) L, ∃ j : t, lo j ≤ a ∧ a ≤ hi j := by
      intro a ha
      obtain ⟨j, hj, hl, hh⟩ := hcover a ha
      exact ⟨⟨j, hj⟩, hl, hh⟩
    have hlocal : ∀ a ∈ Icc (-L) L, |F a - G a| ≤ D s + r * (ε / 4) := by
      have hh := abs_sub_le_of_monotone_mesh (fun a ↦ -F a) (fun a ↦ -G a)
        (fun _ _ h ↦ neg_le_neg (hF h)) (fun _ _ h ↦ neg_le_neg (hG h))
        (fun j : t ↦ lo j) (fun j : t ↦ hi j) (Icc (-L) L) (D s) (r * (ε / 4)) hcov
        (fun j ↦ by simpa only [neg_sub_neg, abs_sub_comm] using hlo j)
        (fun j ↦ by simpa only [neg_sub_neg, abs_sub_comm] using hhi j)
        (fun j ↦ by simpa only [neg_sub_neg] using hgap j)
      simpa only [neg_sub_neg, abs_sub_comm] using hh
    have hnonneg : 0 ≤ r * (ε / 4) := mul_nonneg hr.le heps.le
    have hglobal := abs_sub_le_of_global_antitone_mesh F G hF hG ft gt
      (D s + r * (ε / 4)) (r * (ε / 4)) (-L) L
      (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ mul_nonneg hr.le ENNReal.toReal_nonneg)
      hFt hGt
      (hlocal (-L) ⟨le_rfl, by linarith⟩) (hlocal L ⟨by linarith, le_rfl⟩)
      ((hendpoint none).trans (le_add_of_nonneg_right hnonneg)) hlow hhigh
      (fun j : t ↦ lo j) (fun j : t ↦ hi j) hcov
      (fun j ↦ (hlo j).trans (le_add_of_nonneg_right hnonneg))
      (fun j ↦ (hhi j).trans (le_add_of_nonneg_right hnonneg)) hgap
    obtain ⟨a, ha⟩ := hs
    have hb := hglobal a
    change r * (ε / 2) ≤ D s
    change r * ε < |F a - G a| at ha
    linarith
  · obtain ⟨hI, hb⟩ := N.reserveWindowFiniteError_integrable_bound d hd hV hA T hT color
    have hm := mul_meas_ge_le_integral_of_nonneg (.of_forall hDn) hI (r * (ε / 2))
    have hraw : (N.law : Measure (LegalMarkedOptimalInputScene q)).real E ≤
        (Fintype.card labels : ℝ) * Real.sqrt r / (r * (ε / 2)) := by
      apply (le_div_iff₀ (mul_pos hr (half_pos hε))).mpr
      calc
        _ ≤ ∫ s, D s ∂(N.law : Measure (LegalMarkedOptimalInputScene q)) := by
          simpa only [E, r, mul_comm] using hm
        _ ≤ _ := hb
    apply hraw.trans_eq
    calc
      _ = ((Fintype.card labels : ℝ) / (ε / 2)) * (Real.sqrt r / r) := by ring
      _ = _ := by rw [Real.sqrt_div_self]; rfl

/-- Both original tail conventions have one measurable exceptional event
controlling every real threshold, uniformly in the physical clock cutoff. -/
theorem LegalWeightedStationaryPoissonMatching.exists_reserveUniformBothClocks_measurable_cover
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (hd : d ≠ 0)
      (V : Set (Fin q → ℝ)) (_hV : IsCompact V) (A : Set ℝ) (_hA : IsCompact A),
      0 < legalOriginalReserveSpatialRate q d V →
      ∃ E : Set (LegalMarkedOptimalInputScene q), MeasurableSet E ∧
        (legalOriginalReserveUniformClockBad q α β d hd V A true 0 ε ∪
          legalOriginalReserveUniformClockBad q α β d hd V A false 1 ε) ⊆ E ∧
        (N.law : Measure (LegalMarkedOptimalInputScene q)).real E ≤
          C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  obtain ⟨Cs, hCs, hs⟩ := N.exists_reserveUniformClockBad_measurable_cover true 0 hε
  obtain ⟨Ct, hCt, ht⟩ := N.exists_reserveUniformClockBad_measurable_cover false 1 hε
  refine ⟨Cs + Ct, add_nonneg hCs hCt, ?_⟩
  intro d hd V hV A hA hr
  obtain ⟨Es, hEs, hss, hbs⟩ := hs d hd V hV A hA hr
  obtain ⟨Et, hEt, htt, hbt⟩ := ht d hd V hV A hA hr
  refine ⟨Es ∪ Et, hEs.union hEt, Set.union_subset_union hss htt, ?_⟩
  exact (measureReal_union_le _ _).trans ((add_le_add hbs hbt).trans_eq (add_div _ _ _).symm)

/-- Genuine all-real reserve shortage is small, including thresholds chosen
after seeing the SAME original reserve array. The only deterministic loss is
the omitted original target-clock mass. -/
theorem LegalWeightedStationaryPoissonMatching.exists_reserveUniformClockShortage_measurable_cover
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (hd : d ≠ 0)
      (V : Set (Fin q → ℝ)) (_hV : IsCompact V) (A : Set ℝ) (_hA : IsCompact A),
      0 < legalOriginalReserveSpatialRate q d V →
      ∃ E : Set (LegalMarkedOptimalInputScene q), MeasurableSet E ∧
        {s | ∃ a : ℝ,
          legalOriginalReserveSpatialRate q d V * ((β Aᶜ).toReal + 2 * ε) <
            legalOriginalReserveInputClockCount q d hd V A (Ici a) 0 s -
              legalOriginalReserveInputClockCount q d hd V A (Ioi a) 1 s} ⊆ E ∧
        (N.law : Measure (LegalMarkedOptimalInputScene q)).real E ≤
          C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  obtain ⟨C, hC, hh⟩ := N.exists_reserveUniformBothClocks_measurable_cover hε
  refine ⟨C, hC, ?_⟩
  intro d hd V hV A hA hr
  obtain ⟨E, hE, hsub, hb⟩ := hh d hd V hV A hA hr
  refine ⟨E, hE, ?_, hb⟩
  rintro s ⟨a, ha⟩
  by_cases hs : s ∈ legalOriginalReserveUniformClockBad q α β d hd V A true 0 ε
  · exact hsub (Or.inl hs)
  by_cases ht : s ∈ legalOriginalReserveUniformClockBad q α β d hd V A false 1 ε
  · exact hsub (Or.inr ht)
  have hsc :
      |legalOriginalReserveInputClockCount q d hd V A (Ici a) 0 s -
        legalOriginalReserveSpatialRate q d V * (α.restrict A).real (Ici a)| ≤
          legalOriginalReserveSpatialRate q d V * ε := by
    exact le_of_not_gt (fun h ↦ hs ⟨a, h⟩)
  have htc :
      |legalOriginalReserveInputClockCount q d hd V A (Ioi a) 1 s -
        legalOriginalReserveSpatialRate q d V * (β.restrict A).real (Ioi a)| ≤
          legalOriginalReserveSpatialRate q d V * ε := by
    exact le_of_not_gt (fun h ↦ ht ⟨a, h⟩)
  have hclock := N.truncatedClock_source_excess_le_target_tail hA.measurableSet a
  have hm : legalOriginalReserveSpatialRate q d V * (α.restrict A).real (Ici a) ≤
      legalOriginalReserveSpatialRate q d V * (β.restrict A).real (Ioi a) +
        legalOriginalReserveSpatialRate q d V * (β Aᶜ).toReal := by
    have hh := mul_le_mul_of_nonneg_left hclock hr.le
    simpa only [Measure.real, Measure.restrict_apply measurableSet_Ici,
      Measure.restrict_apply measurableSet_Ioi, inter_comm, mul_add] using hh
  obtain ⟨hsl, hsu⟩ := abs_le.mp hsc
  obtain ⟨htl, htu⟩ := abs_le.mp htc
  exfalso
  nlinarith

/-- The actual population tail surplus retains the source closed tail and
the target strict tail used by the finite legal Hall condition. -/
def legalOriginalClockSurplus (α β : Measure ℝ) (a : ℝ) : ℝ :=
  β.real (Ioi a) - α.real (Ici a)

/-- For the original atomless probability clocks, the exact strict/closed
surplus is their original continuous prefix-mass difference. -/
theorem LegalWeightedStationaryPoissonMatching.clockSurplus_eq_prefix_difference
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) (a : ℝ) :
    legalOriginalClockSurplus α β a = α.real (Iic a) - β.real (Iic a) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  change β.real (legalOriginalTailSet false a) - α.real (legalOriginalTailSet true a) = _
  rw [legalOriginalTailSet_real_eq_total_sub_prefix,
    legalOriginalTailSet_real_eq_total_sub_prefix, probReal_univ, probReal_univ]
  ring

/-- Continuity belongs to the unchanged original clock surplus. -/
theorem LegalWeightedStationaryPoissonMatching.continuous_originalClockSurplus
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) :
    Continuous (legalOriginalClockSurplus α β) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have heq : legalOriginalClockSurplus α β = fun a ↦ α.real (Iic a) - β.real (Iic a) :=
    funext N.clockSurplus_eq_prefix_difference
  rw [heq]
  exact (continuous_clockPrefixMass α).sub (continuous_clockPrefixMass β)

/-- The SAME genuine strictly forward Palm has a cut with positive original
surplus. This does not assert positive surplus on an arbitrary fixed carrier. -/
theorem LegalWeightedStationaryPoissonMatching.exists_pos_originalClockSurplus
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∃ a : ℝ, 0 < legalOriginalClockSurplus α β a := by
  let η := legalMarkedJointPalm q N.law
  let : IsProbabilityMeasure η := N.palm_probability
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have hpos : ∃ a : ℚ, 0 < η {m | m.1.1 ≤ (a : ℝ) ∧ (a : ℝ) < m.1.2} := by
    by_contra! hzero
    have hz (a : ℚ) : η {m | m.1.1 ≤ (a : ℝ) ∧ (a : ℝ) < m.1.2} = 0 :=
      le_antisymm (hzero a) bot_le
    have hcov : {m : PhysicalPairPalmMark (Fin q) | m.1.1 < m.1.2} ⊆
        ⋃ a : ℚ, {m | m.1.1 ≤ (a : ℝ) ∧ (a : ℝ) < m.1.2} := by
      intro m hm
      change m.1.1 < m.1.2 at hm
      obtain ⟨a, hma, ham⟩ := exists_rat_btwn hm
      exact mem_iUnion.mpr ⟨a, hma.le, ham⟩
    have hn := measure_mono_null hcov (measure_iUnion_null hz)
    have hf : η {m : PhysicalPairPalmMark (Fin q) | m.1.1 < m.1.2} = 1 := by
      calc
        _ = η univ := measure_congr (by
          filter_upwards [N.ae_palm_forward] with m hm
          change (m.1.1 < m.1.2) = True
          exact propext ⟨fun _ ↦ True.intro, fun _ ↦ hm⟩)
        _ = 1 := measure_univ
    rw [hf] at hn
    exact one_ne_zero hn
  obtain ⟨a, ha⟩ := hpos
  have hcross := measure_forward_clock_crossing_add_target_prefix q η α β
    N.source_clock N.target_clock (N.ae_palm_forward.mono fun _ h ↦ h.le) (a : ℝ)
  have hr := congrArg ENNReal.toReal hcross
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hr
  refine ⟨a, ?_⟩
  rw [N.clockSurplus_eq_prefix_difference]
  have hposR := ENNReal.toReal_pos ha.ne' (measure_ne_top η _)
  change _ + β.real (Iic (a : ℝ)) = α.real (Iic (a : ℝ)) at hr
  linarith

/-- The valid positive-gap carrier is constructed from the original law,
with its gap asserted only on its own genuine closed superlevel set. -/
def legalOriginalClockGapCarrier (α β : Measure ℝ) (D : Set ℝ) (η : ℝ) : Set ℝ :=
  D ∩ {a | η ≤ legalOriginalClockSurplus α β a}

/-- Every genuine atomless matching has a nonempty compact carrier and a
positive original gap chosen from its OWN law. -/
theorem LegalWeightedStationaryPoissonMatching.exists_compact_originalClockGapCarrier
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∃ η > 0, ∃ D : Set ℝ, IsCompact D ∧
      (legalOriginalClockGapCarrier α β D η).Nonempty ∧
      IsCompact (legalOriginalClockGapCarrier α β D η) ∧
      ∀ a ∈ legalOriginalClockGapCarrier α β D η,
        α.real (Ici a) + η ≤ β.real (Ioi a) := by
  obtain ⟨a, ha⟩ := N.exists_pos_originalClockSurplus
  let η := legalOriginalClockSurplus α β a / 2
  let D := Icc (a - 1) (a + 1)
  have hc : IsCompact (legalOriginalClockGapCarrier α β D η) :=
    isCompact_Icc.inter_right
      (isClosed_le continuous_const N.continuous_originalClockSurplus)
  refine ⟨η, half_pos ha, D, isCompact_Icc, ⟨a, ?_⟩, hc, ?_⟩
  · exact ⟨⟨by linarith, by linarith⟩, by dsimp [η]; linarith⟩
  · intro b hb
    have hh := hb.2
    change η ≤ β.real (Ioi b) - α.real (Ici b) at hh
    linarith

/-- Truncation subtracts only the omitted original target-clock mass from
the original population surplus; all original source clocks are retained in
the comparison direction used by Hall's condition. -/
theorem LegalWeightedStationaryPoissonMatching.truncatedClock_surplus_lower_bound
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set ℝ) (a : ℝ) :
    legalOriginalClockSurplus α β a - (β Aᶜ).toReal ≤
      (β.restrict A).real (Ioi a) - (α.restrict A).real (Ici a) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have hs : (α.restrict A).real (Ici a) ≤ α.real (Ici a) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_le_self _)
  have hset : Ioi a ⊆ (Ioi a ∩ A) ∪ Aᶜ := by
    intro x hx
    by_cases h : x ∈ A
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  have hraw : β (Ioi a) ≤ β (Ioi a ∩ A) + β Aᶜ :=
    (measure_mono hset).trans (measure_union_le _ _)
  have ht : β.real (Ioi a) ≤ (β.restrict A).real (Ioi a) + (β Aᶜ).toReal := by
    have hh := ENNReal.toReal_mono (by finiteness) hraw
    simpa only [Measure.real, Measure.restrict_apply measurableSet_Ioi,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] using hh
  unfold legalOriginalClockSurplus
  linarith

/-- The actual strict Hall reserve slack on its original-law gap carrier. -/
def legalOriginalReserveUniformClockSlackEvent (q : ℕ) (d : ℝ) (hd : d ≠ 0)
    (V : Set (Fin q → ℝ)) (A K : Set ℝ) (η : ℝ) : Set (LegalMarkedOptimalInputScene q) :=
  {s | ∀ a ∈ K, legalOriginalReserveSpatialRate q d V * η / 2 ≤
    legalOriginalReserveInputClockCount q d hd V A (Ioi a) 1 s -
      legalOriginalReserveInputClockCount q d hd V A (Ici a) 0 s}

/-- Original reserve inputs produce uniform strict Hall slack on the carrier
constructed from the original population gap. No arbitrary fixed carrier is
assumed to have a positive gap. -/
theorem LegalWeightedStationaryPoissonMatching.exists_reserveUniformClockSlack_measurable_cover
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (hd : d ≠ 0)
      (V : Set (Fin q → ℝ)) (_hV : IsCompact V) (A : Set ℝ) (_hA : IsCompact A),
      0 < legalOriginalReserveSpatialRate q d V → (β Aᶜ).toReal ≤ η / 4 →
      ∀ D : Set ℝ, ∃ E : Set (LegalMarkedOptimalInputScene q), MeasurableSet E ∧
        (legalOriginalReserveUniformClockSlackEvent q d hd V A
          (legalOriginalClockGapCarrier α β D η) η)ᶜ ⊆ E ∧
        (N.law : Measure (LegalMarkedOptimalInputScene q)).real E ≤
          C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  have heps : 0 < η / 8 := by positivity
  obtain ⟨C, hC, hh⟩ := N.exists_reserveUniformBothClocks_measurable_cover heps
  refine ⟨C, hC, ?_⟩
  intro d hd V hV A hA hr htail D
  obtain ⟨E, hE, hsub, hb⟩ := hh d hd V hV A hA hr
  refine ⟨E, hE, ?_, hb⟩
  intro s hs
  obtain ⟨a, ha⟩ := not_forall.mp hs
  obtain ⟨ha, hfail⟩ := not_imp.mp ha
  by_cases hsc : s ∈ legalOriginalReserveUniformClockBad q α β d hd V A true 0 (η / 8)
  · exact hsub (Or.inl hsc)
  by_cases htc : s ∈ legalOriginalReserveUniformClockBad q α β d hd V A false 1 (η / 8)
  · exact hsub (Or.inr htc)
  have hsource :
      |legalOriginalReserveInputClockCount q d hd V A (Ici a) 0 s -
        legalOriginalReserveSpatialRate q d V * (α.restrict A).real (Ici a)| ≤
          legalOriginalReserveSpatialRate q d V * (η / 8) :=
    le_of_not_gt (fun h ↦ hsc ⟨a, h⟩)
  have htarget :
      |legalOriginalReserveInputClockCount q d hd V A (Ioi a) 1 s -
        legalOriginalReserveSpatialRate q d V * (β.restrict A).real (Ioi a)| ≤
          legalOriginalReserveSpatialRate q d V * (η / 8) :=
    le_of_not_gt (fun h ↦ htc ⟨a, h⟩)
  have hgap : η ≤ legalOriginalClockSurplus α β a := ha.2
  have hpopulation := N.truncatedClock_surplus_lower_bound A a
  have hp := mul_le_mul_of_nonneg_left hpopulation hr.le
  have hg := mul_le_mul_of_nonneg_left hgap hr.le
  have ht := mul_le_mul_of_nonneg_left htail hr.le
  have hse := (abs_le.mp hsource).2
  have hte := (abs_le.mp htarget).1
  exfalso
  apply hfail
  nlinarith

/-- The original target clock law itself chooses a compact physical clock
window with the required small truncation loss. -/
theorem LegalWeightedStationaryPoissonMatching.exists_compact_clock_truncation
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set ℝ, IsCompact A ∧ (β Aᶜ).toReal ≤ δ := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  obtain ⟨A, hA, htail⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := β)) (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  refine ⟨A, hA, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail β (mem_singleton β))
  simpa only [ENNReal.toReal_ofReal hδ.le] using hh

/-- Both the positive-gap carrier and the needed clock truncation are
produced internally from the SAME original law before spatial volume grows. -/
theorem LegalWeightedStationaryPoissonMatching.exists_original_law_uniformClockSlack
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∃ η > 0, ∃ D A : Set ℝ, IsCompact D ∧ IsCompact A ∧
      (legalOriginalClockGapCarrier α β D η).Nonempty ∧
      IsCompact (legalOriginalClockGapCarrier α β D η) ∧
      (β Aᶜ).toReal ≤ η / 4 ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (hd : d ≠ 0)
        (V : Set (Fin q → ℝ)) (_hV : IsCompact V),
        0 < legalOriginalReserveSpatialRate q d V →
        ∃ E : Set (LegalMarkedOptimalInputScene q), MeasurableSet E ∧
          (legalOriginalReserveUniformClockSlackEvent q d hd V A
            (legalOriginalClockGapCarrier α β D η) η)ᶜ ⊆ E ∧
          (N.law : Measure (LegalMarkedOptimalInputScene q)).real E ≤
            C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  obtain ⟨η, hη, D, hD, hne, hc⟩ := N.exists_compact_originalClockGapCarrier
  obtain ⟨A, hA, htail⟩ := N.exists_compact_clock_truncation (by positivity : 0 < η / 4)
  obtain ⟨C, hC, hh⟩ := N.exists_reserveUniformClockSlack_measurable_cover hη
  exact ⟨η, hη, D, A, hD, hA, hne, hc.1, htail, C, hC,
    fun d hd V hV hr ↦ hh d hd V hV A hA hr htail D⟩

/-- The original retained/reserve coordinate carrier together with the SAME
literal finite source and target arrays used by the retained core. -/
abbrev LegalOriginalReserveWindowExperiment (q : ℕ) :=
  (LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
    (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))

/-- The reserve coordinate of the labelled window joining retains its exact
original law, before either color's origin-index array is ordered. -/
theorem original_labelled_reserve_coordinate_map_eq
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure (LegalOriginalReserveWindowExperiment q))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q))) :
    P.map (fun p ↦ p.1.2) = (N.law : Measure (LegalMarkedOptimalInputScene q)) := by
  rw [show (fun p : LegalOriginalReserveWindowExperiment q ↦ p.1.2) =
    Prod.snd ∘ Prod.fst from rfl, ← Measure.map_map measurable_snd measurable_fst, hP]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]

/-- Measurable exceptional events transfer exactly through the actual N
coordinate while retaining all same-core and original-array correlations. -/
theorem original_labelled_reserve_coordinate_real_preimage
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure (LegalOriginalReserveWindowExperiment q))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q)))
    {E : Set (LegalMarkedOptimalInputScene q)} (hE : MeasurableSet E) :
    P.real ((fun p ↦ p.1.2) ⁻¹' E) =
      (N.law : Measure (LegalMarkedOptimalInputScene q)).real E := by
  have hmeas : Measurable (fun p : LegalOriginalReserveWindowExperiment q ↦ p.1.2) :=
    measurable_snd.comp measurable_fst
  have hh := Measure.map_apply (μ := P) hmeas hE
  rw [original_labelled_reserve_coordinate_map_eq M N P hP] at hh
  exact congrArg ENNReal.toReal hh.symm

/-- Uniform ALL-threshold source and target clock budgets hold in the SAME
original product/Poisson-array joining and SAME actual retained core. -/
theorem exists_original_labelled_reserve_windowCore_with_uniformClockBudget
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0),
      |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1 →
      ∀ (V : Set (Fin q → ℝ)) (_hV : IsCompact V) (A : Set ℝ) (_hA : IsCompact A),
      0 < legalOriginalReserveSpatialRate q d V → ∀ cost : LegalMarkedPhysicalEdge q → ℝ,
      ∃ S > 0, ∃ P : ProbabilityMeasure (LegalOriginalReserveWindowExperiment q),
      ∃ E : Set (LegalMarkedOptimalInputScene q),
        (P : Measure (LegalOriginalReserveWindowExperiment q)).map Prod.fst =
          (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
            (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
        (P : Measure (LegalOriginalReserveWindowExperiment q)).map Prod.snd =
          legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
        (∀ᵐ p ∂(P : Measure (LegalOriginalReserveWindowExperiment q)),
          IsOriginalReserveWindowCore q (V ×ˢ A) cost
            (legalMarkedInputSceneDilation q c hc p.1.1)
            (legalMarkedInputSceneDilation q d hd p.1.2) p.2) ∧
        MeasurableSet E ∧
        (legalOriginalReserveUniformClockBad q α β d hd V A true 0 ε ∪
          legalOriginalReserveUniformClockBad q α β d hd V A false 1 ε) ⊆ E ∧
        (P : Measure (LegalOriginalReserveWindowExperiment q)).real
          ((fun p ↦ p.1.2) ⁻¹' E) ≤ C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  obtain ⟨C, hC, hh⟩ := N.exists_reserveUniformBothClocks_measurable_cover hε
  refine ⟨C, hC, ?_⟩
  intro c d hc hd hunit V hV A hA hr cost
  obtain ⟨S, hS, P, hl, ht, hcore⟩ := exists_original_labelled_reserve_windowCore
    M N hq c d hc hd hunit (hV.prod hA) cost
  obtain ⟨E, hE, hsub, hb⟩ := hh d hd V hV A hA hr
  refine ⟨S, hS, P, E, hl, ht, hcore, hE, hsub, ?_⟩
  rw [original_labelled_reserve_coordinate_real_preimage M N _ hl hE]
  exact hb

/-- The SAME original product/finite-array experiment has uniform strict
Hall slack on a nonempty compact gap carrier generated by the original law.
Its positive gap and its physical clock cutoff are both constructed here. -/
theorem exists_original_labelled_reserve_windowCore_with_lawGenerated_uniformClockSlack
    {q : ℕ} {α β : Measure ℝ} [NullSingletonClass α] [NullSingletonClass β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 0 < q) :
    ∃ η > 0, ∃ D A : Set ℝ, IsCompact D ∧ IsCompact A ∧
      (legalOriginalClockGapCarrier α β D η).Nonempty ∧
      IsCompact (legalOriginalClockGapCarrier α β D η) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0),
        |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1 →
        ∀ (V : Set (Fin q → ℝ)) (_hV : IsCompact V),
        0 < legalOriginalReserveSpatialRate q d V → ∀ cost : LegalMarkedPhysicalEdge q → ℝ,
        ∃ S > 0, ∃ P : ProbabilityMeasure (LegalOriginalReserveWindowExperiment q),
        ∃ E : Set (LegalMarkedOptimalInputScene q),
          (P : Measure (LegalOriginalReserveWindowExperiment q)).map Prod.fst =
            (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
              (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
          (P : Measure (LegalOriginalReserveWindowExperiment q)).map Prod.snd =
            legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
          (∀ᵐ p ∂(P : Measure (LegalOriginalReserveWindowExperiment q)),
            IsOriginalReserveWindowCore q (V ×ˢ A) cost
              (legalMarkedInputSceneDilation q c hc p.1.1)
              (legalMarkedInputSceneDilation q d hd p.1.2) p.2) ∧
          MeasurableSet E ∧
          (legalOriginalReserveUniformClockSlackEvent q d hd V A
            (legalOriginalClockGapCarrier α β D η) η)ᶜ ⊆ E ∧
          (P : Measure (LegalOriginalReserveWindowExperiment q)).real
            ((fun p ↦ p.1.2) ⁻¹' E) ≤ C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  obtain ⟨η, hη, D, A, hD, hA, hne, hK, htail, C, hC, hh⟩ :=
    N.exists_original_law_uniformClockSlack
  refine ⟨η, hη, D, A, hD, hA, hne, hK, C, hC, ?_⟩
  intro c d hc hd hunit V hV hr cost
  obtain ⟨S, hS, P, hl, ht, hcore⟩ := exists_original_labelled_reserve_windowCore
    M N hq c d hc hd hunit (hV.prod hA) cost
  obtain ⟨E, hE, hsub, hb⟩ := hh d hd V hV hr
  refine ⟨S, hS, P, E, hl, ht, hcore, hE, hsub, ?_⟩
  rw [original_labelled_reserve_coordinate_real_preimage M N _ hl hE]
  exact hb

section OriginalFinslerConditionalClocks

open Manifold OTSelector.Geometry
open scoped ContDiff

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The final original conditional Finsler clocks consume the existing
geometric atomlessness producer at the SAME label. No new atomlessness or
positive-gap hypothesis is added to the original geometric packet. -/
theorem ae_originalConditionalClock_uniformHallSlack_of_windowLaws
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ρs ρt : M → ℝ} {vs vt : ℕ → E → ℝ}
    (hs : PopulationConditionalWindowLaw P a κ lambda μ ρs vs)
    (ht : PopulationConditionalWindowLaw P a κ lambda ν ρt vt)
    (ha : Measurable a)
    (hu : let _instOriginalUniformClockMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {As At : Set M} (hAs : IsCompact As) (hAt : IsCompact At)
    (hμ : ∀ᵐ x ∂μ, x ∈ As) (hν : ∀ᵐ x ∂ν, x ∈ At)
    (q : ℕ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) :
    ∀ᵐ z ∂lambda,
      ∀ N : LegalWeightedStationaryPoissonMatching q (condDistrib u a μ z)
        (condDistrib u a ν z) kin g,
      ∃ η > 0, ∃ D A : Set ℝ, IsCompact D ∧ IsCompact A ∧
        (legalOriginalClockGapCarrier (condDistrib u a μ z) (condDistrib u a ν z) D η).Nonempty ∧
        IsCompact (legalOriginalClockGapCarrier (condDistrib u a μ z) (condDistrib u a ν z) D η) ∧
        ((condDistrib u a ν z) Aᶜ).toReal ≤ η / 4 ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ) (hd : d ≠ 0)
          (V : Set (Fin q → ℝ)) (_hV : IsCompact V),
          0 < legalOriginalReserveSpatialRate q d V →
          ∃ B : Set (LegalMarkedOptimalInputScene q), MeasurableSet B ∧
            (legalOriginalReserveUniformClockSlackEvent q d hd V A
              (legalOriginalClockGapCarrier (condDistrib u a μ z) (condDistrib u a ν z) D η) η)ᶜ ⊆ B ∧
            (N.law : Measure (LegalMarkedOptimalInputScene q)).real B ≤
              C / Real.sqrt (legalOriginalReserveSpatialRate q d V) := by
  filter_upwards [ae_atomless_clock_of_windowLaw hs ha hu hAs hμ,
    ae_atomless_clock_of_windowLaw ht ha hu hAt hν] with z hsz htz
  let : NullSingletonClass (condDistrib u a μ z) := hsz.1
  let : NullSingletonClass (condDistrib u a ν z) := htz.1
  intro N
  exact N.exists_original_law_uniformClockSlack

end OriginalFinslerConditionalClocks

end OTSelector.Reconstruction
