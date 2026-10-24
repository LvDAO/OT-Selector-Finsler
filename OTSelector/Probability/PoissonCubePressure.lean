import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Poisson.Basic
import OTSelector.MeasureTheory.CubeBlockDecomposition
import OTSelector.Probability.CloudPressureRegularity
import OTSelector.Probability.CloudValueMeasurable
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
# Poissonized cloud pressure on the unit cube

We model a Poisson cloud on the unit `q`-cube as a Poisson count together with an
infinite sequence of independent uniform cube points; only the first count many
points are used.  This product representation avoids dependent sigma-types while
retaining the exact law of the used points.  Two independent clouds give the
two-sample pressure

`t ↦ ∫ maxCardValue (r^{2/q} |x_i - y_j|^2 + t g(x_i,y_j))`.

The edge cost is clamped by `min (·) 1` in every coordinate so that every edge is
globally bounded; on the unit cube the clamp is the identity, and we prove the
clamped and true values agree almost surely.  The module records the model, its
probability structure, the a.e. identification of the clamped model, and the
measurability/integrability of the tilted value.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

/-! ## The cloud model -/

/-- The iid uniform sequence law on the unit `q`-cube. -/
noncomputable def cubeSeqLaw (q : ℕ) : Measure (ℕ → (Fin q → ℝ)) :=
  letI : ∀ _ : ℕ, IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)
  Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) 1)

instance isProbabilityMeasure_cubeSeqLaw (q : ℕ) : IsProbabilityMeasure (cubeSeqLaw q) := by
  haveI : ∀ _ : ℕ, IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) 1))
  infer_instance

/-- One Poissonized cloud: a Poisson count and an infinite iid position sequence. -/
abbrev PoissonCloudSpace (q : ℕ) := ℕ × (ℕ → (Fin q → ℝ))

/-- The Poissonized cloud law of mean count `r`. -/
noncomputable def poissonCubeLaw (q : ℕ) (r : ℝ≥0) : Measure (PoissonCloudSpace q) :=
  (poissonMeasure r).prod (cubeSeqLaw q)

instance isProbabilityMeasure_poissonCubeLaw (q : ℕ) (r : ℝ≥0) :
    IsProbabilityMeasure (poissonCubeLaw q r) := by
  unfold poissonCubeLaw
  infer_instance

/-- Two independent Poissonized clouds. -/
abbrev TwoCloudSpace (q : ℕ) := PoissonCloudSpace q × PoissonCloudSpace q

/-- The law of two independent Poissonized clouds with common mean count `r`. -/
noncomputable def twoCloudLaw (q : ℕ) (r : ℝ≥0) : Measure (TwoCloudSpace q) :=
  (poissonCubeLaw q r).prod (poissonCubeLaw q r)

instance isProbabilityMeasure_twoCloudLaw (q : ℕ) (r : ℝ≥0) :
    IsProbabilityMeasure (twoCloudLaw q r) := by
  unfold twoCloudLaw
  infer_instance

/-- The source count of a two-cloud sample. -/
def sourceCount {q : ℕ} (ω : TwoCloudSpace q) : ℕ := ω.1.1

/-- The target count of a two-cloud sample. -/
def targetCount {q : ℕ} (ω : TwoCloudSpace q) : ℕ := ω.2.1

/-- The source position sequence. -/
def sourcePoint {q : ℕ} (ω : TwoCloudSpace q) (i : ℕ) : Fin q → ℝ := ω.1.2 i

/-- The target position sequence. -/
def targetPoint {q : ℕ} (ω : TwoCloudSpace q) (j : ℕ) : Fin q → ℝ := ω.2.2 j

theorem measurable_sourceCount (q : ℕ) : Measurable (sourceCount : TwoCloudSpace q → ℕ) := by
  unfold sourceCount
  fun_prop

theorem measurable_targetCount (q : ℕ) : Measurable (targetCount : TwoCloudSpace q → ℕ) := by
  unfold targetCount
  fun_prop

theorem measurable_sourcePoint (q : ℕ) (i : ℕ) :
    Measurable fun ω : TwoCloudSpace q => sourcePoint ω i := by
  unfold sourcePoint
  fun_prop

theorem measurable_targetPoint (q : ℕ) (j : ℕ) :
    Measurable fun ω : TwoCloudSpace q => targetPoint ω j := by
  unfold targetPoint
  fun_prop

theorem measurable_sourceCoord (q : ℕ) (i : ℕ) (l : Fin q) :
    Measurable fun ω : TwoCloudSpace q => sourcePoint ω i l := by
  unfold sourcePoint
  fun_prop

theorem measurable_targetCoord (q : ℕ) (j : ℕ) (l : Fin q) :
    Measurable fun ω : TwoCloudSpace q => targetPoint ω j l := by
  unfold targetPoint
  fun_prop

/-! ## Costs -/

/-- Squared Euclidean distance on coordinate space. -/
def sqDist {q : ℕ} (x y : Fin q → ℝ) : ℝ := ∑ l, (x l - y l) ^ 2

/-- The coordinatewise clamped squared distance, globally bounded by `q`. -/
def sqDistClamped {q : ℕ} (x y : Fin q → ℝ) : ℝ :=
  ∑ l, min ((x l - y l) ^ 2) 1

theorem sqDistClamped_nonneg {q : ℕ} (x y : Fin q → ℝ) : 0 ≤ sqDistClamped x y :=
  Finset.sum_nonneg fun _ _ => le_min (sq_nonneg _) zero_le_one

theorem sqDistClamped_le_card {q : ℕ} (x y : Fin q → ℝ) :
    sqDistClamped x y ≤ (q : ℝ) := by
  unfold sqDistClamped
  calc ∑ l, min ((x l - y l) ^ 2) 1 ≤ ∑ _l : Fin q, (1 : ℝ) :=
        Finset.sum_le_sum fun l _ => min_le_right _ _
    _ = (q : ℝ) := by simp

theorem sqDistClamped_eq_sqDist {q : ℕ} {x y : Fin q → ℝ}
    (hx : x ∈ (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) 1)))
    (hy : y ∈ (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) 1))) :
    sqDistClamped x y = sqDist x y := by
  unfold sqDistClamped sqDist
  apply Finset.sum_congr rfl
  intro l _
  have hxl : x l ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_pi.mp hx l (Set.mem_univ l)
  have hyl : y l ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_pi.mp hy l (Set.mem_univ l)
  have h_abs : |x l - y l| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hxl.1, hxl.2, hyl.1, hyl.2]
  have h_sq : (x l - y l) ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (x l - y l), sq_abs (x l - y l), sq_nonneg (x l - y l)]
  rw [min_eq_left h_sq]

/-- The clamped quadratic edge cost at mean count scale `r`. -/
noncomputable def poissonCubeCost (q : ℕ) (r : ℝ) (ω : TwoCloudSpace q) (i j : ℕ) : ℝ :=
  r ^ (2 / (q : ℝ)) * sqDistClamped (sourcePoint ω i) (targetPoint ω j)

/-- The true quadratic edge cost, used for the dyadic comparison. -/
noncomputable def poissonCubeCostTrue (q : ℕ) (r : ℝ) (ω : TwoCloudSpace q) (i j : ℕ) : ℝ :=
  r ^ (2 / (q : ℝ)) * sqDist (sourcePoint ω i) (targetPoint ω j)

/-- The bounded probe evaluated at the two positions. -/
def poissonCubeProbe {q : ℕ} (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ)
    (ω : TwoCloudSpace q) (i j : ℕ) : ℝ :=
  g (sourcePoint ω i) (targetPoint ω j)

/-- The tilted maximum-cardinality value of the two-cloud sample, with the
clamped cost. -/
noncomputable def poissonCubeTilted (q : ℕ) (r : ℝ)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ) (ω : TwoCloudSpace q) : ℝ :=
  tiltedCloudValue (poissonCubeCost q r) (poissonCubeProbe g) t ω
    (sourceCount ω) (targetCount ω)

/-- The tilted maximum-cardinality value with the true quadratic cost. -/
noncomputable def poissonCubeTiltedTrue (q : ℕ) (r : ℝ)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ) (ω : TwoCloudSpace q) : ℝ :=
  tiltedCloudValue (poissonCubeCostTrue q r) (poissonCubeProbe g) t ω
    (sourceCount ω) (targetCount ω)

/-- The Poissonized two-sample pressure. -/
noncomputable def poissonCubePressure (q : ℕ) (r : ℝ≥0)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, poissonCubeTilted q (r : ℝ) g t ω ∂(twoCloudLaw q r)

/-- The unit cube as a subset of coordinate space. -/
def unitCube (q : ℕ) : Set (Fin q → ℝ) :=
  Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) 1)

theorem measurableSet_unitCube (q : ℕ) : MeasurableSet (unitCube q) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

/-- The uniform cube measure gives the whole cube mass one. -/
theorem cubeMeasure_unitCube (q : ℕ) : cubeMeasure (Fin q) 1 (unitCube q) = 1 := by
  have hS : Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) 1) = unitCube q := rfl
  have hvol : volume (Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) 1)) = 1 := by
    rw [volume_pi_pi, Finset.prod_const]
    simp [Real.volume_Ioo]
  rw [cubeMeasure_eq_normalized_volume q (by norm_num), Measure.smul_apply,
    Measure.restrict_apply (measurableSet_unitCube q), ← hS, Set.inter_self, hvol]
  simp

/-- Almost every coordinate of the cube sequence lies in the unit cube. -/
theorem ae_mem_unitCube_cubeSeqLaw (q : ℕ) :
    ∀ᵐ x ∂cubeSeqLaw q, x ∈ Set.pi Set.univ (fun _ : ℕ => unitCube q) := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  rw [ae_all_iff]
  intro i
  have hmp := measurePreserving_eval_infinitePi
    (μ := fun _ : ℕ => cubeMeasure (Fin q) 1)
    (hμ := fun _ => isProbabilityMeasure_cubeMeasure (by norm_num)) i
  have hcube : ∀ᵐ y ∂(cubeMeasure (Fin q) 1), y ∈ unitCube q := by
    haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
      isProbabilityMeasure_cubeMeasure (by norm_num)
    rw [ae_iff]
    change (cubeMeasure (Fin q) 1) (unitCube q)ᶜ = 0
    rw [measure_compl (measurableSet_unitCube q)]
    · rw [cubeMeasure_unitCube, measure_univ]
      simp
    · rw [cubeMeasure_unitCube]
      exact ENNReal.one_ne_top
  exact hmp.quasiMeasurePreserving.ae hcube

/-- Almost every point used by a Poisson cloud lies in the unit cube. -/
theorem ae_mem_unitCube_poissonCubeLaw (q : ℕ) (r : ℝ≥0) :
    ∀ᵐ ω ∂(poissonCubeLaw q r), (fun i => ω.2 i) ∈
      Set.pi Set.univ (fun _ : ℕ => unitCube q) := by
  unfold poissonCubeLaw
  exact Measure.quasiMeasurePreserving_snd.ae (ae_mem_unitCube_cubeSeqLaw q)

/-- Almost every used source and target point lies in the unit cube. -/
theorem ae_points_mem_unitCube_twoCloudLaw (q : ℕ) (r : ℝ≥0) :
    ∀ᵐ ω ∂(twoCloudLaw q r),
      (∀ i, sourcePoint ω i ∈ unitCube q) ∧ (∀ j, targetPoint ω j ∈ unitCube q) := by
  unfold twoCloudLaw
  have hsrc : ∀ᵐ ω ∂((poissonCubeLaw q r).prod (poissonCubeLaw q r)),
      (fun i => ω.1.2 i) ∈ Set.pi Set.univ (fun _ : ℕ => unitCube q) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_mem_unitCube_poissonCubeLaw q r)
  have htgt : ∀ᵐ ω ∂((poissonCubeLaw q r).prod (poissonCubeLaw q r)),
      (fun j => ω.2.2 j) ∈ Set.pi Set.univ (fun _ : ℕ => unitCube q) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_unitCube_poissonCubeLaw q r)
  filter_upwards [hsrc, htgt] with ω h1 h2
  exact ⟨fun i => Set.mem_pi.mp h1 i (Set.mem_univ i),
    fun j => Set.mem_pi.mp h2 j (Set.mem_univ j)⟩

/-- On the unit cube the clamped and true tilted values agree. -/
theorem poissonCubeTilted_eq_true_ae (q : ℕ) (r : ℝ≥0)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ) :
    ∀ᵐ ω ∂(twoCloudLaw q r),
      poissonCubeTilted q (r : ℝ) g t ω = poissonCubeTiltedTrue q (r : ℝ) g t ω := by
  filter_upwards [ae_points_mem_unitCube_twoCloudLaw q r] with ω hω
  unfold poissonCubeTilted poissonCubeTiltedTrue tiltedCloudValue poissonCubeCost
    poissonCubeCostTrue
  congr 2
  funext i j
  rw [sqDistClamped_eq_sqDist (hω.1 i) (hω.2 j)]

/-! ## Integrability and regularity in the tilt -/

/-- The edge function used in the matching, extended by zero outside the two clouds. -/
noncomputable def poissonCubeEdge (q : ℕ) (r : ℝ)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ)
    (ω : TwoCloudSpace q) (i j : ℕ) : ℝ :=
  if i < sourceCount ω ∧ j < targetCount ω then
    poissonCubeCost q r ω i j + t * poissonCubeProbe g ω i j
  else 0

/-- The cloud value with the clamped cost is exactly the tilted value. -/
theorem cloudValueNat_poissonCubeEdge (q : ℕ) (r : ℝ)
    (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (t : ℝ) (ω : TwoCloudSpace q) :
    cloudValueNat (poissonCubeEdge q r g t) (sourceCount) (targetCount) ω =
      poissonCubeTilted q r g t ω := by
  unfold cloudValueNat poissonCubeTilted tiltedCloudValue poissonCubeEdge
  congr 1
  funext i j
  exact dif_pos ⟨i.isLt, j.isLt⟩

/-- Coordinate measurability of the clamped Poisson cube edge function. -/
theorem measurable_poissonCubeEdge (q : ℕ) (r : ℝ)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hg : Measurable (Function.uncurry g))
    (t : ℝ) (i j : ℕ) :
    Measurable fun ω : TwoCloudSpace q => poissonCubeEdge q r g t ω i j := by
  unfold poissonCubeEdge poissonCubeCost poissonCubeProbe
  apply Measurable.ite
  · exact measurableSet_setOf.mpr
      ((measurable_const.lt (measurable_sourceCount q)).and
        (measurable_const.lt (measurable_targetCount q)))
  · apply Measurable.add
    · apply Measurable.mul
      · exact measurable_const
      · unfold sqDistClamped
        apply Finset.measurable_sum
        intro l _
        apply Measurable.min
        · apply Measurable.pow
          · apply Measurable.sub
            · exact measurable_sourceCoord q i l
            · exact measurable_targetCoord q j l
          · exact measurable_const
        · exact measurable_const
    · apply Measurable.mul
      · exact measurable_const
      · exact hg.comp ((measurable_sourcePoint q i).prodMk (measurable_targetPoint q j))
  · exact measurable_const

/-- A uniform upper bound for every edge value on the clamped model. -/
theorem poissonCubeEdge_le_bound (q : ℕ) {r : ℝ} (hr : 0 ≤ r) {G : ℝ} (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hgb : ∀ x y, |g x y| ≤ G)
    (t : ℝ) (ω : TwoCloudSpace q) (i j : ℕ) :
    poissonCubeEdge q r g t ω i j ≤ r ^ (2 / (q : ℝ)) * (q : ℝ) + |t| * G := by
  unfold poissonCubeEdge
  by_cases h : i < sourceCount ω ∧ j < targetCount ω
  · rw [if_pos h]
    have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have hcost : poissonCubeCost q r ω i j ≤ r ^ (2 / (q : ℝ)) * (q : ℝ) := by
      unfold poissonCubeCost
      exact mul_le_mul_of_nonneg_left (sqDistClamped_le_card _ _) hrpow
    have hprobe : t * poissonCubeProbe g ω i j ≤ |t| * G := by
      calc t * poissonCubeProbe g ω i j ≤ |t * poissonCubeProbe g ω i j| := le_abs_self _
        _ = |t| * |poissonCubeProbe g ω i j| := abs_mul _ _
        _ ≤ |t| * G := mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg _)
    linarith
  · rw [if_neg h]
    have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have : 0 ≤ |t| * G := mul_nonneg (abs_nonneg _) hG0
    nlinarith [mul_nonneg hrpow hq]

/-- Measurability of the tilted clamped value. -/
theorem measurable_poissonCubeTilted (q : ℕ) {r : ℝ} (hr : 0 ≤ r) {G : ℝ} (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Measurable (poissonCubeTilted q r g t) := by
  have hfun : poissonCubeTilted q r g t =
      cloudValueNat (poissonCubeEdge q r g t) (sourceCount) (targetCount) :=
    funext fun ω => (cloudValueNat_poissonCubeEdge q r g t ω).symm
  rw [hfun]
  refine measurable_cloudValueNat
    (B := fun _ : TwoCloudSpace q => r ^ (2 / (q : ℝ)) * (q : ℝ) + |t| * G)
    (fun i j => measurable_poissonCubeEdge q r hg t i j)
    (measurable_sourceCount q) (measurable_targetCount q) measurable_const ?_
  intro ω i j
  exact poissonCubeEdge_le_bound q hr hG0 hgb t ω i j

/-- The Poisson source count is integrable. -/
theorem integrable_sourceCount (q : ℕ) (r : ℝ≥0) :
    Integrable (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ)) (twoCloudLaw q r) := by
  have h1 : Integrable (fun z : PoissonCloudSpace q => (z.1 : ℝ)) (poissonCubeLaw q r) := by
    unfold poissonCubeLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  have hne : poissonCubeLaw q r ≠ 0 := by
    intro h0
    have h1' : poissonCubeLaw q r Set.univ = 1 := measure_univ
    rw [h0] at h1'
    simp at h1'
  unfold twoCloudLaw sourceCount
  exact (Integrable.comp_fst_iff (ν := poissonCubeLaw q r) hne).mpr h1

/-- Integrability of the tilted clamped value. -/
theorem integrable_poissonCubeTilted (q : ℕ) (r : ℝ≥0) {G : ℝ} (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    Integrable (poissonCubeTilted q (r : ℝ) g t) (twoCloudLaw q r) := by
  have hr : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  have hmeas : Measurable (poissonCubeTilted q (r : ℝ) g t) :=
    measurable_poissonCubeTilted q hr hG0 hg hgb t
  have hNint := integrable_sourceCount q r
  let C : ℝ := (r : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ) + |t| * G
  have hC0 : 0 ≤ C := by
    have hrpow : 0 ≤ (r : ℝ) ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have htG : 0 ≤ |t| * G := mul_nonneg (abs_nonneg _) hG0
    dsimp [C]
    nlinarith [mul_nonneg hrpow hq]
  have hdom : Integrable (fun ω : TwoCloudSpace q => ((sourceCount ω : ℕ) : ℝ) * C)
      (twoCloudLaw q r) := hNint.mul_const C
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_points_mem_unitCube_twoCloudLaw q r] with ω hω
  have hBc0 : 0 ≤ (r : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ) := by
    have hrpow : 0 ≤ (r : ℝ) ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    exact mul_nonneg hrpow hq
  have hcost (i : ℕ) (j : ℕ) :
      |poissonCubeCost q (r : ℝ) ω i j| ≤ (r : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ) := by
    unfold poissonCubeCost
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _), abs_of_nonneg (sqDistClamped_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (sqDistClamped_le_card _ _) (Real.rpow_nonneg hr _)
  have hprobe : ∀ i j, |poissonCubeProbe g ω i j| ≤ G := fun i j => hgb _ _
  have hval := PartialMatching.abs_maxCardValue_perturbed_le
    (fun i : Fin (sourceCount ω) => fun j : Fin (targetCount ω) =>
      poissonCubeCost q (r : ℝ) ω i j)
    (fun i : Fin (sourceCount ω) => fun j : Fin (targetCount ω) =>
      poissonCubeProbe g ω i j)
    (Bc := (r : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ)) (G := G) (t := t)
    (fun i j => hcost i j) hBc0 (fun i j => hgb _ _) hG0
  have hval' : |poissonCubeTilted q (r : ℝ) g t ω| ≤
      ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) * C := by
    simpa only [poissonCubeTilted, tiltedCloudValue, C] using hval
  have hmin : ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) ≤ (sourceCount ω : ℝ) := by
    exact_mod_cast min_le_left _ _
  calc ‖poissonCubeTilted q (r : ℝ) g t ω‖
      = |poissonCubeTilted q (r : ℝ) g t ω| := Real.norm_eq_abs _
    _ ≤ ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) * C := hval'
    _ ≤ (sourceCount ω : ℝ) * C := mul_le_mul_of_nonneg_right hmin hC0

/-- The minimum of the two Poisson counts is integrable. -/
theorem integrable_min_counts (q : ℕ) (r : ℝ≥0) :
    Integrable (fun ω : TwoCloudSpace q =>
      ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ)) (twoCloudLaw q r) := by
  have hmeas : Measurable fun ω : TwoCloudSpace q =>
      ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) :=
    Measurable.comp measurable_from_nat
      ((measurable_sourceCount q).min (measurable_targetCount q))
  refine Integrable.mono' (integrable_sourceCount q r) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast min_le_left _ _

/-- The Poisson pressure is concave in the tilt. -/
theorem concaveOn_poissonCubePressure (q : ℕ) (r : ℝ≥0) {G : ℝ} (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) :
    ConcaveOn ℝ Set.univ (fun t => poissonCubePressure q r g t) := by
  have h := concaveOn_integral_tiltedCloudValue (twoCloudLaw q r)
    (poissonCubeCost q (r : ℝ)) (poissonCubeProbe g) (sourceCount) (targetCount)
    (fun t => poissonCubeTilted q (r : ℝ) g t) (fun t => rfl)
    (fun t => integrable_poissonCubeTilted q r hG0 hg hgb t)
  simpa only [poissonCubePressure] using h

/-- The Poisson pressure is Lipschitz in the tilt. -/
theorem abs_poissonCubePressure_sub_le (q : ℕ) (r : ℝ≥0) {G : ℝ} (hG0 : 0 ≤ G)
    {g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (t u : ℝ) :
    |poissonCubePressure q r g t - poissonCubePressure q r g u| ≤
      (∫ ω, ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) ∂(twoCloudLaw q r)) *
        (G * |t - u|) := by
  have h := abs_integral_tiltedCloudValue_sub_le (twoCloudLaw q r)
    (poissonCubeCost q (r : ℝ)) (poissonCubeProbe g) (sourceCount) (targetCount)
    (fun t => poissonCubeTilted q (r : ℝ) g t) (fun t => rfl) hG0
    (fun ω i j => hgb _ _)
    (fun t => integrable_poissonCubeTilted q r hG0 hg hgb t)
    (integrable_min_counts q r) t u
  simpa only [poissonCubePressure] using h

end OTSelector.Probability
