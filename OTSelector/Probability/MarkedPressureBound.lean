import OTSelector.Finite.MaxCardValueScaling
import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.PoissonCubePressureBound
import OTSelector.Limit.DyadicSeriesBound

/-!
# A uniform-in-intensity bound for the marked Poissonized cube pressure

This module proves the marked analogue of `exists_poissonCubePressure_bound`.
The marked model has two independent Poissonized clouds of marked cube points,
and the kinetic edge cost depends on the mark pair through a function `kin` of
the transverse displacement.  Assuming `kin` is nonnegative and dominated by
`C` times the squared displacement, the marked pressure is at most
`Cq (C + |t| G) r`, uniformly in the intensity `r ≥ 1`.

The proof follows the unmarked dyadic scheme.  The marks do not affect the cell
decomposition, so the position projection of a marked cloud has the law of the
unmarked Poisson cloud.  In particular the expected dyadic cell-count
discrepancy of the marked clouds obeys the same `min (2r) (sqrt (2 r 2^(kq)))`
bound.  The kinetic edge is bounded by `C` times the squared truncated
displacement, hence by `C` times the dyadic partition expression; shifting the
edge by `|t| G` makes it nonnegative and lets the integrated hierarchical
estimate of `HierarchicalMatchingExpectation` apply.  The remaining real
analysis is the dyadic geometric series bound of `DyadicSeriesBound`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open OTSelector
open OTSelector.Reconstruction

noncomputable section
namespace OTSelector.Probability

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## Forgetting the marks -/

/-- Forget the mark of one marked cloud. -/
def markedPosition {q : ℕ} (z : MarkedCloudSpace q A) : PoissonCloudSpace q :=
  (z.1, fun i => (z.2 i).1)

/-- Forget the marks of both clouds. -/
def markedPosCloud {q : ℕ} (ω : TwoMarkedCloudSpace q A B) : TwoCloudSpace q :=
  (markedPosition ω.1, markedPosition ω.2)

theorem measurable_markedPosition (q : ℕ) :
    Measurable (markedPosition (q := q) (A := A)) := by
  unfold markedPosition
  refine Measurable.prodMk measurable_fst ?_
  apply measurable_pi_lambda
  intro i
  exact measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)

theorem measurable_markedPosCloud (q : ℕ) :
    Measurable (markedPosCloud (q := q) (A := A) (B := B)) := by
  unfold markedPosCloud
  exact ((measurable_markedPosition (q := q) (A := A)).comp measurable_fst).prodMk
    ((measurable_markedPosition (q := q) (A := B)).comp measurable_snd)

/-- The count of a marked cloud is the count of its position projection. -/
theorem mSourceCount_eq_sourceCount (q : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    mSourceCount ω = sourceCount (markedPosCloud (q := q) ω) := rfl

/-- The target count of a marked cloud is the count of its position projection. -/
theorem mTargetCount_eq_targetCount (q : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    mTargetCount ω = targetCount (markedPosCloud (q := q) ω) := rfl

/-- The position sequence of a marked cloud is that of its position projection. -/
theorem mSourcePoint_eq_sourcePoint (q : ℕ) (ω : TwoMarkedCloudSpace q A B) (i : ℕ) :
    mSourcePoint ω i = sourcePoint (markedPosCloud (q := q) ω) i := rfl

/-- The target position sequence of a marked cloud is that of its position projection. -/
theorem mTargetPoint_eq_targetPoint (q : ℕ) (ω : TwoMarkedCloudSpace q A B) (j : ℕ) :
    mTargetPoint ω j = targetPoint (markedPosCloud (q := q) ω) j := rfl

/-! ## The law of the position projection -/

/-- Projecting the iid marked sequence to its positions gives the unmarked iid
sequence law. -/
theorem map_markedSeqLaw_fst (q : ℕ) (α : Measure A) [IsProbabilityMeasure α] :
    (markedSeqLaw (q := q) A α).map
      (fun x : ℕ → (Fin q → ℝ) × A => fun i => (x i).1) = cubeSeqLaw q := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  unfold markedSeqLaw cubeSeqLaw
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => (cubeMeasure (Fin q) 1).prod α)
    (f := fun (_ : ℕ) => (Prod.fst : (Fin q → ℝ) × A → (Fin q → ℝ)))
    (fun _ => measurable_fst)]
  congr 1
  funext i
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The position projection pushes the marked Poisson cloud law to the unmarked
Poisson cloud law. -/
theorem map_markedPosition_markedPoissonLaw (q : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (r : ℝ≥0) :
    (markedPoissonLaw (q := q) A α r).map (markedPosition (q := q) (A := A)) =
      poissonCubeLaw q r := by
  unfold markedPoissonLaw poissonCubeLaw markedPosition
  rw [show (fun z : MarkedCloudSpace q A => (z.1, fun i => (z.2 i).1)) =
      Prod.map (id : ℕ → ℕ)
        (fun x : ℕ → (Fin q → ℝ) × A => fun i => (x i).1) from rfl]
  rw [← Measure.map_prod_map (poissonMeasure r)
      (markedSeqLaw (q := q) A α) measurable_id (by fun_prop),
    Measure.map_id, map_markedSeqLaw_fst (q := q) α]

/-- The position projection of both clouds pushes the two-cloud marked law to
the unmarked two-cloud law. -/
theorem map_markedPosCloud_twoMarkedCloudLaw (q : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    (twoMarkedCloudLaw (q := q) A B α β r).map
        (markedPosCloud (q := q) (A := A) (B := B)) = twoCloudLaw q r := by
  unfold twoMarkedCloudLaw twoCloudLaw markedPosCloud
  rw [show (fun ω : MarkedCloudSpace q A × MarkedCloudSpace q B =>
        (markedPosition ω.1, markedPosition ω.2)) =
      Prod.map (markedPosition (q := q) (A := A)) (markedPosition (q := q) (A := B))
      from rfl]
  rw [← Measure.map_prod_map (markedPoissonLaw (q := q) A α r)
      (markedPoissonLaw (q := q) B β r)
      (measurable_markedPosition (q := q) (A := A))
      (measurable_markedPosition (q := q) (A := B)),
    map_markedPosition_markedPoissonLaw (q := q) (A := A) α r,
    map_markedPosition_markedPoissonLaw (q := q) (A := B) β r]

/-! ## Almost every marked point lies in the unit cube -/

/-- Almost every position of a marked iid sequence lies in the unit cube. -/
theorem ae_mem_unitCube_markedSeqLaw (q : ℕ) (α : Measure A) [IsProbabilityMeasure α] :
    ∀ᵐ x ∂(markedSeqLaw (q := q) A α),
      (fun i => (x i).1) ∈ Set.pi Set.univ (fun _ : ℕ => unitCube q) := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  rw [ae_all_iff]
  intro i
  have hmp := measurePreserving_eval_infinitePi
    (μ := fun _ : ℕ => (cubeMeasure (Fin q) 1).prod α) (hμ := by infer_instance) i
  have hcube : ∀ᵐ y ∂((cubeMeasure (Fin q) 1).prod α), y.1 ∈ unitCube q := by
    have h1 : ∀ᵐ y ∂(cubeMeasure (Fin q) 1), y ∈ unitCube q := by
      rw [ae_iff]
      rw [show {y : Fin q → ℝ | ¬ y ∈ unitCube q} = (unitCube q)ᶜ from rfl]
      rw [measure_compl (measurableSet_unitCube q) ?_]
      · rw [cubeMeasure_unitCube, measure_univ]
        simp
      · rw [cubeMeasure_unitCube]
        exact ENNReal.one_ne_top
    exact Measure.quasiMeasurePreserving_fst.ae h1
  unfold markedSeqLaw
  exact hmp.quasiMeasurePreserving.ae hcube

/-- Almost every point of a marked Poisson cloud lies in the unit cube. -/
theorem ae_mem_unitCube_markedPoissonLaw (q : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (r : ℝ≥0) :
    ∀ᵐ z ∂(markedPoissonLaw (q := q) A α r),
      (fun i => (z.2 i).1) ∈ Set.pi Set.univ (fun _ : ℕ => unitCube q) := by
  unfold markedPoissonLaw
  exact Measure.quasiMeasurePreserving_snd.ae (ae_mem_unitCube_markedSeqLaw q α)

/-- Almost every used source and target point of two marked clouds lies in the
unit cube. -/
theorem ae_points_mem_unitCube_twoMarkedCloudLaw (q : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β r),
      (∀ i, mSourcePoint ω i ∈ unitCube q) ∧
        (∀ j, mTargetPoint ω j ∈ unitCube q) := by
  unfold twoMarkedCloudLaw
  filter_upwards [
    Measure.quasiMeasurePreserving_fst.ae
      (ae_mem_unitCube_markedPoissonLaw (q := q) (A := A) α r),
    Measure.quasiMeasurePreserving_snd.ae
      (ae_mem_unitCube_markedPoissonLaw (q := q) (A := B) β r)] with ω h1 h2
  exact ⟨fun i => Set.mem_pi.mp h1 i (Set.mem_univ i),
    fun j => Set.mem_pi.mp h2 j (Set.mem_univ j)⟩

/-! ## Marked cell counts and discrepancies -/

/-- The level-`k` dyadic cell count of a marked cloud, ignoring the marks. -/
noncomputable def markedCellCount (q k : ℕ) (z : MarkedCloudSpace q A)
    (c : Fin q → Fin (2 ^ k)) : ℕ :=
  (Finset.univ.filter (fun i : Fin z.1 => dyadicCell q k (z.2 i).1 = c)).card

/-- The marked cell count is the unmarked cell count of the position projection. -/
theorem markedCellCount_eq_cloudCellCount (q k : ℕ) (z : MarkedCloudSpace q A)
    (c : Fin q → Fin (2 ^ k)) :
    markedCellCount q k z c = cloudCellCount q k (markedPosition z) c := rfl

/-- The level-`k` dyadic cell-count discrepancy of two marked clouds. -/
noncomputable def markedCellDiscrepancy (q k : ℕ) (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  ∑ c : Fin q → Fin (2 ^ k),
    |(markedCellCount q k ω.1 c : ℝ) - (markedCellCount q k ω.2 c : ℝ)|

/-- The marked discrepancy is the unmarked discrepancy of the position
projection. -/
theorem markedCellDiscrepancy_eq_cloudCellDiscrepancy (q k : ℕ)
    (ω : TwoMarkedCloudSpace q A B) :
    markedCellDiscrepancy q k ω = cloudCellDiscrepancy q k (markedPosCloud ω) := by
  unfold markedCellDiscrepancy cloudCellDiscrepancy markedPosCloud
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [markedCellCount_eq_cloudCellCount (q := q) (k := k) (A := A),
    markedCellCount_eq_cloudCellCount (q := q) (k := k) (A := B)]

/-- The truncated position cloud of a marked sample. -/
noncomputable def markedTruncCloud (q : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    TwoCloudSpace q :=
  ((mSourceCount ω, fun i => cubeTruncPoint (mSourcePoint ω i)),
   (mTargetCount ω, fun j => cubeTruncPoint (mTargetPoint ω j)))

theorem measurable_markedTruncCloud (q : ℕ) :
    Measurable (markedTruncCloud (q := q) (A := A) (B := B)) := by
  unfold markedTruncCloud
  refine Measurable.prodMk
    (Measurable.prodMk (measurable_mSourceCount q) ?_)
    (Measurable.prodMk (measurable_mTargetCount q) ?_)
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro l
    exact (measurable_cubeTruncPoint_apply q l).comp (measurable_mSourcePoint q i)
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro l
    exact (measurable_cubeTruncPoint_apply q l).comp (measurable_mTargetPoint q i)

/-- The truncated marked cell discrepancy, in the form used by the integrated
hierarchical estimate. -/
noncomputable def markedTruncCellDiscrepancy (q k : ℕ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  ∑ c : Fin q → Fin (2 ^ k),
    |(partitionCount ((dyadicCell q k) ∘
        (fun i : Fin (mSourceCount ω) => cubeTruncPoint (mSourcePoint ω (i : ℕ)))) c : ℝ) -
      (partitionCount ((dyadicCell q k) ∘
        (fun j : Fin (mTargetCount ω) => cubeTruncPoint (mTargetPoint ω (j : ℕ)))) c : ℝ)|

/-- Unfolding lemma for the truncated marked discrepancy. -/
theorem markedTruncCellDiscrepancy_apply (q k : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    markedTruncCellDiscrepancy q k ω =
      ∑ c : Fin q → Fin (2 ^ k),
        |(partitionCount ((dyadicCell q k) ∘
            (fun i : Fin (mSourceCount ω) =>
              cubeTruncPoint (mSourcePoint ω (i : ℕ)))) c : ℝ) -
          (partitionCount ((dyadicCell q k) ∘
            (fun j : Fin (mTargetCount ω) =>
              cubeTruncPoint (mTargetPoint ω (j : ℕ)))) c : ℝ)| := rfl

/-- The truncated marked discrepancy is the unmarked discrepancy of the
truncated position cloud. -/
theorem markedTruncCellDiscrepancy_eq_cloudCellDiscrepancy (q k : ℕ)
    (ω : TwoMarkedCloudSpace q A B) :
    markedTruncCellDiscrepancy q k ω =
      cloudCellDiscrepancy q k (markedTruncCloud q ω) := by
  unfold markedTruncCellDiscrepancy cloudCellDiscrepancy markedTruncCloud
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [partitionCount_eq_card_filter, partitionCount_eq_card_filter]
  rfl

/-- On the unit cube truncation is the identity, so the truncated and untruncated
position clouds agree almost surely. -/
theorem markedTruncCloud_eq_markedPosCloud_ae (q : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    markedTruncCloud (q := q) (A := A) (B := B)
      =ᵐ[twoMarkedCloudLaw (q := q) A B α β r]
    markedPosCloud (q := q) (A := A) (B := B) := by
  filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw (q := q) α β r] with ω hω
  unfold markedTruncCloud markedPosCloud markedPosition
  congr 1
  · congr 1
    funext i
    exact cubeTruncPoint_eq_of_mem (hω.1 i)
  · congr 1
    funext j
    exact cubeTruncPoint_eq_of_mem (hω.2 j)

/-- The truncated and untruncated marked discrepancies agree almost surely. -/
theorem markedTruncCellDiscrepancy_eq_markedCellDiscrepancy_ae (q k : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) :
    markedTruncCellDiscrepancy (q := q) (k := k) (A := A) (B := B)
      =ᵐ[twoMarkedCloudLaw (q := q) A B α β r]
    markedCellDiscrepancy (q := q) (k := k) (A := A) (B := B) := by
  filter_upwards [markedTruncCloud_eq_markedPosCloud_ae (q := q) α β r] with ω h
  rw [markedTruncCellDiscrepancy_eq_cloudCellDiscrepancy (q := q) (k := k),
    markedCellDiscrepancy_eq_cloudCellDiscrepancy (q := q) (k := k), h]

theorem markedTruncCellDiscrepancy_nonneg (q k : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    0 ≤ markedTruncCellDiscrepancy q k ω :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem markedTruncCellDiscrepancy_le_counts (q k : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    markedTruncCellDiscrepancy q k ω ≤
      ((mSourceCount ω : ℕ) : ℝ) + ((mTargetCount ω : ℕ) : ℝ) := by
  rw [markedTruncCellDiscrepancy_eq_cloudCellDiscrepancy (q := q) (k := k)]
  have h := cloudCellDiscrepancy_le_counts q k (markedTruncCloud q ω)
  simpa only [markedTruncCloud, sourceCount, targetCount] using h

theorem measurable_markedTruncCellDiscrepancy (q k : ℕ) :
    Measurable (markedTruncCellDiscrepancy (q := q) (k := k) (A := A) (B := B)) := by
  have hfun : markedTruncCellDiscrepancy (q := q) (k := k) (A := A) (B := B) =
      cloudCellDiscrepancy q k ∘
        markedTruncCloud (q := q) (A := A) (B := B) := by
    funext ω
    exact markedTruncCellDiscrepancy_eq_cloudCellDiscrepancy q k ω
  rw [hfun]
  exact (measurable_cloudCellDiscrepancy q k).comp (measurable_markedTruncCloud q)

theorem integrable_markedTruncCellDiscrepancy (q k : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (markedTruncCellDiscrepancy (q := q) (k := k) (A := A) (B := B))
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have hdom := (integrable_mSourceCount (q := q) α β r).add
    (integrable_mTargetCount (q := q) α β r)
  refine Integrable.mono' hdom
    (measurable_markedTruncCellDiscrepancy q k).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (markedTruncCellDiscrepancy_nonneg q k ω)]
  exact markedTruncCellDiscrepancy_le_counts q k ω

/-- The integral of the truncated marked discrepancy is the integral of the
unmarked discrepancy under the unmarked two-cloud law. -/
theorem integral_markedTruncCellDiscrepancy_eq (q k : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω, markedTruncCellDiscrepancy q k ω ∂(twoMarkedCloudLaw (q := q) A B α β r) =
      ∫ y, cloudCellDiscrepancy q k y ∂(twoCloudLaw q r) := by
  calc ∫ ω, markedTruncCellDiscrepancy q k ω
        ∂(twoMarkedCloudLaw (q := q) A B α β r)
      = ∫ ω, markedCellDiscrepancy q k ω
          ∂(twoMarkedCloudLaw (q := q) A B α β r) :=
        integral_congr_ae
          (markedTruncCellDiscrepancy_eq_markedCellDiscrepancy_ae q k α β r)
    _ = ∫ ω, cloudCellDiscrepancy q k (markedPosCloud ω)
          ∂(twoMarkedCloudLaw (q := q) A B α β r) :=
        integral_congr_ae (Filter.Eventually.of_forall
          (fun ω => markedCellDiscrepancy_eq_cloudCellDiscrepancy q k ω))
    _ = ∫ y, cloudCellDiscrepancy q k y
          ∂((twoMarkedCloudLaw (q := q) A B α β r).map
            (markedPosCloud (q := q) (A := A) (B := B))) :=
        (integral_map (measurable_markedPosCloud q).aemeasurable
          (measurable_cloudCellDiscrepancy q k).aestronglyMeasurable).symm
    _ = ∫ y, cloudCellDiscrepancy q k y ∂(twoCloudLaw q r) := by
        rw [map_markedPosCloud_twoMarkedCloudLaw (q := q) α β r]

/-- The expected truncated marked discrepancy obeys the trivial `2 r` bound and
the square-root histogram bound. -/
theorem integral_markedTruncCellDiscrepancy_le (q k : ℕ) (α : Measure A)
    [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω, markedTruncCellDiscrepancy q k ω ∂(twoMarkedCloudLaw (q := q) A B α β r) ≤
      min (2 * (r : ℝ)) (Real.sqrt (2 * (r : ℝ) * (2 : ℝ) ^ (k * q))) := by
  rw [integral_markedTruncCellDiscrepancy_eq (q := q) (k := k) α β r]
  exact le_min (integral_cloudCellDiscrepancy_le_trivial q k r)
    (integral_cloudCellDiscrepancy_le q k r)

/-! ## Count integrals via the position projection -/

theorem integral_mSourceCount_eq (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω, ((mSourceCount ω : ℕ) : ℝ) ∂(twoMarkedCloudLaw (q := q) A B α β r) =
      (r : ℝ) := by
  have hcomp : (fun ω : TwoMarkedCloudSpace q A B => ((mSourceCount ω : ℕ) : ℝ)) =
      (fun y : TwoCloudSpace q => ((sourceCount y : ℕ) : ℝ)) ∘
        (markedPosCloud (q := q) (A := A) (B := B)) := rfl
  calc ∫ ω, ((mSourceCount ω : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)
      = ∫ y, ((sourceCount y : ℕ) : ℝ)
          ∂((twoMarkedCloudLaw (q := q) A B α β r).map
            (markedPosCloud (q := q) (A := A) (B := B))) := by
        rw [hcomp]
        exact (integral_map (measurable_markedPosCloud q).aemeasurable
          (Measurable.comp measurable_from_nat (measurable_sourceCount q)).aestronglyMeasurable).symm
    _ = ∫ y, ((sourceCount y : ℕ) : ℝ) ∂(twoCloudLaw q r) := by
        rw [map_markedPosCloud_twoMarkedCloudLaw (q := q) α β r]
    _ = (r : ℝ) := integral_sourceCount q r

theorem integral_mTargetCount_eq (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω, ((mTargetCount ω : ℕ) : ℝ) ∂(twoMarkedCloudLaw (q := q) A B α β r) =
      (r : ℝ) := by
  have hcomp : (fun ω : TwoMarkedCloudSpace q A B => ((mTargetCount ω : ℕ) : ℝ)) =
      (fun y : TwoCloudSpace q => ((targetCount y : ℕ) : ℝ)) ∘
        (markedPosCloud (q := q) (A := A) (B := B)) := rfl
  calc ∫ ω, ((mTargetCount ω : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)
      = ∫ y, ((targetCount y : ℕ) : ℝ)
          ∂((twoMarkedCloudLaw (q := q) A B α β r).map
            (markedPosCloud (q := q) (A := A) (B := B))) := by
        rw [hcomp]
        exact (integral_map (measurable_markedPosCloud q).aemeasurable
          (Measurable.comp measurable_from_nat (measurable_targetCount q)).aestronglyMeasurable).symm
    _ = ∫ y, ((targetCount y : ℕ) : ℝ) ∂(twoCloudLaw q r) := by
        rw [map_markedPosCloud_twoMarkedCloudLaw (q := q) α β r]
    _ = (r : ℝ) := integral_targetCount q r

theorem integrable_mMaxCounts (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((max (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ))
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have hmeas : Measurable fun ω : TwoMarkedCloudSpace q A B =>
      ((max (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) :=
    Measurable.comp measurable_from_nat
      ((measurable_mSourceCount q).max (measurable_mTargetCount q))
  refine Integrable.mono' ((integrable_mSourceCount (q := q) α β r).add
    (integrable_mTargetCount (q := q) α β r)) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : max (mSourceCount ω) (mTargetCount ω) ≤ mSourceCount ω + mTargetCount ω :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  calc ((max (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
      ≤ ((mSourceCount ω + mTargetCount ω : ℕ) : ℝ) := by exact_mod_cast h
    _ = (mSourceCount ω : ℝ) + (mTargetCount ω : ℝ) := by push_cast; ring

theorem integral_mMaxCounts_le (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω, ((max (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r) ≤ 2 * (r : ℝ) := by
  have hcomp : (fun ω : TwoMarkedCloudSpace q A B =>
        ((max (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)) =
      (fun y : TwoCloudSpace q => ((max (sourceCount y) (targetCount y) : ℕ) : ℝ)) ∘
        (markedPosCloud (q := q) (A := A) (B := B)) := rfl
  have hmeas2 : Measurable fun y : TwoCloudSpace q =>
      ((max (sourceCount y) (targetCount y) : ℕ) : ℝ) :=
    Measurable.comp measurable_from_nat
      ((measurable_sourceCount q).max (measurable_targetCount q))
  calc ∫ ω, ((max (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)
      = ∫ y, ((max (sourceCount y) (targetCount y) : ℕ) : ℝ)
          ∂((twoMarkedCloudLaw (q := q) A B α β r).map
            (markedPosCloud (q := q) (A := A) (B := B))) := by
        rw [hcomp]
        exact (integral_map (measurable_markedPosCloud q).aemeasurable
          hmeas2.aestronglyMeasurable).symm
    _ = ∫ y, ((max (sourceCount y) (targetCount y) : ℕ) : ℝ)
          ∂(twoCloudLaw q r) := by
        rw [map_markedPosCloud_twoMarkedCloudLaw (q := q) α β r]
    _ ≤ 2 * (r : ℝ) := integral_max_counts_le q r

theorem integrable_mAbsCountsSub (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      |(mSourceCount ω : ℝ) - (mTargetCount ω : ℝ)|)
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have hmeas : Measurable fun ω : TwoMarkedCloudSpace q A B =>
      |(mSourceCount ω : ℝ) - (mTargetCount ω : ℝ)| :=
    continuous_abs.measurable.comp
      ((Measurable.comp measurable_from_nat (measurable_mSourceCount q)).sub
        (Measurable.comp measurable_from_nat (measurable_mTargetCount q)))
  refine Integrable.mono' ((integrable_mSourceCount (q := q) α β r).add
    (integrable_mTargetCount (q := q) α β r)) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_abs]
  simp only [Pi.add_apply]
  have h1 : (0 : ℝ) ≤ (mSourceCount ω : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (mTargetCount ω : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem integral_mAbsCountsSub_le (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω, |(mSourceCount ω : ℝ) - (mTargetCount ω : ℝ)|
        ∂(twoMarkedCloudLaw (q := q) A B α β r) ≤ Real.sqrt (2 * (r : ℝ)) := by
  have hcomp : (fun ω : TwoMarkedCloudSpace q A B =>
        |(mSourceCount ω : ℝ) - (mTargetCount ω : ℝ)|) =
      (fun y : TwoCloudSpace q => |(sourceCount y : ℝ) - (targetCount y : ℝ)|) ∘
        (markedPosCloud (q := q) (A := A) (B := B)) := rfl
  have hmeas2 : Measurable fun y : TwoCloudSpace q =>
      |(sourceCount y : ℝ) - (targetCount y : ℝ)| :=
    continuous_abs.measurable.comp
      ((Measurable.comp measurable_from_nat (measurable_sourceCount q)).sub
        (Measurable.comp measurable_from_nat (measurable_targetCount q)))
  calc ∫ ω, |(mSourceCount ω : ℝ) - (mTargetCount ω : ℝ)|
        ∂(twoMarkedCloudLaw (q := q) A B α β r)
      = ∫ y, |(sourceCount y : ℝ) - (targetCount y : ℝ)|
          ∂((twoMarkedCloudLaw (q := q) A B α β r).map
            (markedPosCloud (q := q) (A := A) (B := B))) := by
        rw [hcomp]
        exact (integral_map (measurable_markedPosCloud q).aemeasurable
          hmeas2.aestronglyMeasurable).symm
    _ = ∫ y, |(sourceCount y : ℝ) - (targetCount y : ℝ)| ∂(twoCloudLaw q r) := by
        rw [map_markedPosCloud_twoMarkedCloudLaw (q := q) α β r]
    _ ≤ Real.sqrt (2 * (r : ℝ)) := integral_abs_counts_sub_le q r

/-! ## The kinetic edge is bounded by the squared displacement -/

/-- The squared kinetic displacement is the truncated squared distance. -/
theorem mDisplacement_sq_sum_eq_sqDist (q : ℕ) (x y : Fin q → ℝ) :
    ∑ l, (mDisplacement x y l) ^ 2 = sqDist (cubeTruncPoint x) (cubeTruncPoint y) := by
  unfold mDisplacement sqDist
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-- The shifted marked edge cost is nonnegative when the kinetic cost is
nonnegative. -/
theorem shiftedMarkedEdge_nonneg (q : ℕ) {r t G : ℝ} (hr : 0 ≤ r) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    {g : A → B → ℝ} (hgb : ∀ a b, |g a b| ≤ G)
    (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    0 ≤ mKineticCost q r kin ω i j + t * mProbe g ω i j + |t| * G := by
  have hkin0 : 0 ≤ mKineticCost q r kin ω i j := by
    unfold mKineticCost
    exact mul_nonneg (Real.rpow_nonneg hr _) (hkin_nonneg _ _ _)
  have hprobe : -(|t| * G) ≤ t * mProbe g ω i j := by
    have habs : |mProbe g ω i j| ≤ G := hgb _ _
    have hmul : |t| * |mProbe g ω i j| ≤ |t| * G :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    have h6 : -( |t * mProbe g ω i j|) ≤ t * mProbe g ω i j := neg_abs_le _
    rw [abs_mul] at h6
    linarith
  linarith

/-- Pointwise dyadic bound for the shifted marked edge cost. -/
theorem markedShiftedEdge_le_hier (q : ℕ) {r C G t : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hgb : ∀ a b, |g a b| ≤ G)
    {K : ℕ} (hK : 0 < K) (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    mKineticCost q r kin ω i j + t * mProbe g ω i j + |t| * G ≤
      (C * (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K)) + 2 * (|t| * G)) +
        ∑ k : Fin K,
          (C * (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)))) *
            partitionDistance
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mSourcePoint ω i)))
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mTargetPoint ω j))) := by
  have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  have hkin_le : mKineticCost q r kin ω i j ≤
      C * (r ^ (2 / (q : ℝ)) * sqDist (cubeTruncPoint (mSourcePoint ω i))
        (cubeTruncPoint (mTargetPoint ω j))) := by
    have h1 : mKineticCost q r kin ω i j ≤
        r ^ (2 / (q : ℝ)) * (C * ∑ l,
          (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) l ^ 2) := by
      unfold mKineticCost
      calc r ^ (2 / (q : ℝ)) * kin (mSourceMark ω i) (mTargetMark ω j)
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))
          ≤ r ^ (2 / (q : ℝ)) * |kin (mSourceMark ω i) (mTargetMark ω j)
              (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hrpow
        _ ≤ r ^ (2 / (q : ℝ)) * (C * ∑ l,
              (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) l ^ 2) :=
            mul_le_mul_of_nonneg_left (hkin_bound _ _ _) hrpow
    calc mKineticCost q r kin ω i j
        ≤ r ^ (2 / (q : ℝ)) * (C * ∑ l,
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) l ^ 2) := h1
      _ = C * (r ^ (2 / (q : ℝ)) * sqDist (cubeTruncPoint (mSourcePoint ω i))
            (cubeTruncPoint (mTargetPoint ω j))) := by
          rw [mDisplacement_sq_sum_eq_sqDist]
          ring
  have hprobe_le : t * mProbe g ω i j ≤ |t| * G := by
    calc t * mProbe g ω i j ≤ |t * mProbe g ω i j| := le_abs_self _
      _ = |t| * |mProbe g ω i j| := abs_mul _ _
      _ ≤ |t| * G := mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg _)
  have hgeo := dyadicEdgeCost_le (q := q) (r := r) (t := 0) (G := 0) hr le_rfl
    (g := fun _ _ => (0 : ℝ)) (fun _ _ => by simp) hK
    (markedPosCloud (q := q) (A := A) (B := B) ω) i j
  have hgeo' : r ^ (2 / (q : ℝ)) * sqDist (cubeTruncPoint (mSourcePoint ω i))
        (cubeTruncPoint (mTargetPoint ω j)) ≤
      r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        ∑ k : Fin K,
          (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
            partitionDistance
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mSourcePoint ω i)))
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mTargetPoint ω j))) := by
    simpa only [markedPosCloud, markedPosition, sourcePoint, targetPoint, mSourcePoint,
      mTargetPoint, zero_mul, mul_zero, abs_zero, add_zero, zero_add] using hgeo
  have hCgeo := mul_le_mul_of_nonneg_left hgeo' hC0
  have hdist : C * (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        ∑ k : Fin K,
          (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
            partitionDistance
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mSourcePoint ω i)))
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mTargetPoint ω j)))) =
      (C * (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K))) +
        ∑ k : Fin K,
          (C * (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)))) *
            partitionDistance
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mSourcePoint ω i)))
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mTargetPoint ω j))) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  linarith [hkin_le, hprobe_le, hCgeo.trans_eq hdist]

/-! ## The shifted marked cloud value -/

/-- The shifted marked edge cost, extended by zero outside the used prefixes. -/
noncomputable def mMarkedShiftedEdge (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t G : ℝ)
    (ω : TwoMarkedCloudSpace q A B) (i j : ℕ) : ℝ :=
  if i < mSourceCount ω ∧ j < mTargetCount ω then
    mKineticCost q r kin ω i j + t * mProbe g ω i j + |t| * G
  else 0

/-- The shifted marked cloud value is the marked tilted value plus the shift on
the matched cardinality. -/
theorem cloudValueNat_mMarkedShiftedEdge (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t G : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    cloudValueNat (mMarkedShiftedEdge (A := A) (B := B) q r kin g t G)
        (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω =
      markedTilted (q := q) (r := r) kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * (|t| * G) := by
  unfold cloudValueNat markedTilted tiltedCloudValue mMarkedShiftedEdge
  have hmat : (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
        (if (i : ℕ) < mSourceCount ω ∧ (j : ℕ) < mTargetCount ω then
          mKineticCost q r kin ω (i : ℕ) (j : ℕ) +
            t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G
        else 0)) =
      (fun i : Fin (mSourceCount ω) => fun j : Fin (mTargetCount ω) =>
        (mKineticCost q r kin ω (i : ℕ) (j : ℕ) +
          t * mProbe g ω (i : ℕ) (j : ℕ)) + |t| * G) := by
    funext i j
    rw [if_pos ⟨i.isLt, j.isLt⟩]
  rw [hmat, PartialMatching.maxCardValue_add_const, Nat.cast_min]

/-- Integrability of the shifted marked cloud value. -/
theorem integrable_mMarkedShiftedValue (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) {C G : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      cloudValueNat (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
        (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω)
      (twoMarkedCloudLaw (q := q) A B α β r) := by
  have htil := integrable_markedTilted (q := q) α β r (C := C) (G := G)
    r.coe_nonneg hC0 hG0 hkin hkin_bound hg hgb t
  have hmin := integrable_mMinCount (q := q) α β r
  have hae : (fun ω : TwoMarkedCloudSpace q A B =>
        cloudValueNat (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
          (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω)
      =ᵐ[twoMarkedCloudLaw (q := q) A B α β r]
      fun ω => markedTilted (q := q) (r := (r : ℝ)) kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * (|t| * G) :=
    Filter.Eventually.of_forall
      (fun ω => cloudValueNat_mMarkedShiftedEdge q (r : ℝ) kin g t G ω)
  exact (htil.add (hmin.mul_const _)).congr hae.symm

/-! ## The real-analytic base estimate -/

/-- The scaled base term of the marked hierarchical bound. -/
theorem marked_base_discrepancy_bound (q K : ℕ) {r C B : ℝ} (hq : 0 < q) (hr1 : 1 ≤ r)
    (hC0 : 0 ≤ C) (hrK : r ≤ (K : ℝ)) :
    (C * (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K)) + 2 * B) *
        (2 * r) ≤
      C * (8 * (q : ℝ) * r) + 4 * B * r := by
  have hX := base_discrepancy_bound q K hq hr1 hrK (B := 0)
  have hX' : (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K)) * (2 * r) ≤
      8 * (q : ℝ) * r := by
    simpa using hX
  calc (C * (r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K)) + 2 * B) *
        (2 * r)
      = C * ((r ^ (2 / (q : ℝ)) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K)) * (2 * r)) +
          4 * B * r := by ring
    _ ≤ C * (8 * (q : ℝ) * r) + 4 * B * r := by
        have h := mul_le_mul_of_nonneg_left hX' hC0
        linarith

/-! ## The uniform marked pressure bound -/

set_option maxHeartbeats 0 in
/-- **Uniform-in-`r` marked Poisson cube pressure bound.**  For `q > 4` there is
a constant `Cq ≥ 0` such that for every `C, G, t` with `C, G ≥ 0`, every
nonnegative measurable kinetic cost dominated by `C` times the squared
displacement, and every measurable probe bounded by `G`, the marked Poissonized
pressure is at most `Cq (C + |t| G) r` for every intensity `r ≥ 1`. -/
theorem exists_markedPressure_bound (q : ℕ) (hq : 4 < q)
    (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β] :
    ∃ Cq : ℝ, 0 ≤ Cq ∧
      ∀ (C G t : ℝ), 0 ≤ C → 0 ≤ G →
      ∀ (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ),
        Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)) →
        Measurable (Function.uncurry g) →
        (∀ a b v, 0 ≤ kin a b v) →
        (∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2) →
        (∀ a b, |g a b| ≤ G) →
        ∀ r : ℝ≥0, 1 ≤ r →
          markedPressure q A B α β r kin g t ≤ Cq * (C + |t| * G) * (r : ℝ) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_dyadic_series_bound q hq
  refine ⟨8 * (q : ℝ) + 4 + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2, ?_, ?_⟩
  · have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have h1 : (0 : ℝ) ≤ 8 * (q : ℝ) + 4 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * C₀ := by linarith
    have h3 : (0 : ℝ) ≤ (16 / 3) * (q : ℝ) * Real.sqrt 2 := by positivity
    linarith
  · intro C G t hC0 hG0 kin g hkin hg hkin_nonneg hkin_bound hgb r hr1
    have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr1'
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := hrpos.le
    have hqpos_nat : 0 < q := by omega
    have hKpos : 0 < Nat.ceil (r : ℝ) := Nat.ceil_pos.mpr hrpos
    have hrK : (r : ℝ) ≤ ((Nat.ceil (r : ℝ) : ℕ) : ℝ) := Nat.le_ceil _
    have hK_lt : ((Nat.ceil (r : ℝ) : ℕ) : ℝ) < (r : ℝ) + 1 :=
      Nat.ceil_lt_add_one hr0
    have hK1 : (1 : ℝ) ≤ ((Nat.ceil (r : ℝ) : ℕ) : ℝ) := hr1'.trans hrK
    have hK_2r : ((Nat.ceil (r : ℝ) : ℕ) : ℝ) ≤ 2 * (r : ℝ) := by linarith
    let Bs : ℝ := |t| * G
    have hBs0 : 0 ≤ Bs := by dsimp [Bs]; positivity
    let D : Fin (Nat.ceil (r : ℝ)) → ℝ := fun k =>
      min (2 * (r : ℝ)) (Real.sqrt (2 * (r : ℝ) * (2 : ℝ) ^ ((k : ℕ) * q)))
    let cell : (k : Fin (Nat.ceil (r : ℝ))) → (Fin q → ℝ) → (Fin q → Fin (2 ^ (k : ℕ))) :=
      fun k => dyadicCell q (k : ℕ)
    let base : ℝ :=
      C * (r ^ (2 / (q : ℝ)) *
        ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ (Nat.ceil (r : ℝ)))) + 2 * Bs
    let weight : Fin (Nat.ceil (r : ℝ)) → ℝ := fun k =>
      C * (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)))
    have hbase0 : 0 ≤ base := by
      have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr0 _
      have hquarter : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (Nat.ceil (r : ℝ)) := by positivity
      have hX : 0 ≤ r ^ (2 / (q : ℝ)) *
          ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ (Nat.ceil (r : ℝ))) :=
        mul_nonneg hrpow (mul_nonneg (by positivity) hquarter)
      have hCX : 0 ≤ C * (r ^ (2 / (q : ℝ)) *
          ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ (Nat.ceil (r : ℝ)))) :=
        mul_nonneg hC0 hX
      dsimp [base]
      linarith
    have hweight0 : ∀ k, 0 ≤ weight k := by
      intro k
      have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr0 _
      have hquarter : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (k : ℕ) := by positivity
      have hX : 0 ≤ r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ)) :=
        mul_nonneg hrpow (mul_nonneg (by positivity) hquarter)
      dsimp [weight]
      exact mul_nonneg hC0 hX
    have hDint : ∀ k : Fin (Nat.ceil (r : ℝ)),
        Integrable (markedTruncCellDiscrepancy (q := q) (k := (k : ℕ))
          (A := A) (B := B)) (twoMarkedCloudLaw (q := q) A B α β r) := by
      intro k
      exact integrable_markedTruncCellDiscrepancy (q := q) (k := (k : ℕ)) α β r
    have hDbound : ∀ k : Fin (Nat.ceil (r : ℝ)),
        ∫ ω, markedTruncCellDiscrepancy q (k : ℕ) ω
          ∂(twoMarkedCloudLaw (q := q) A B α β r) ≤ D k := by
      intro k
      simpa only [D] using
        integral_markedTruncCellDiscrepancy_le (q := q) (k := (k : ℕ)) α β r
    have hcost : ∀ ω : TwoMarkedCloudSpace q A B,
        ∀ i : Fin (mSourceCount ω), ∀ j : Fin (mTargetCount ω),
        mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
            t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G ≤
          base + ∑ k : Fin (Nat.ceil (r : ℝ)), weight k *
            partitionDistance
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mSourcePoint ω (i : ℕ))))
              (dyadicCell q (k : ℕ) (cubeTruncPoint (mTargetPoint ω (j : ℕ)))) := by
      intro ω i j
      have h := markedShiftedEdge_le_hier (q := q) (r := (r : ℝ)) (C := C) (G := G)
        (t := t) hr0 hC0 hG0 hkin_nonneg hkin_bound hgb hKpos ω (i : ℕ) (j : ℕ)
      simpa only [base, weight, Bs] using h
    have hnonneg : ∀ ω : TwoMarkedCloudSpace q A B,
        ∀ i : Fin (mSourceCount ω), ∀ j : Fin (mTargetCount ω),
        0 ≤ mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
          t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G := by
      intro ω i j
      exact shiftedMarkedEdge_nonneg (q := q) hr0 hG0 hkin_nonneg hgb ω (i : ℕ) (j : ℕ)
    have hV : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        PartialMatching.maxCardValue (fun i : Fin (mSourceCount ω) =>
          fun j : Fin (mTargetCount ω) =>
            mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
              t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G))
        (twoMarkedCloudLaw (q := q) A B α β r) := by
      have hshift := integrable_mMarkedShiftedValue (q := q) (α := α) (β := β) r
        (C := C) (G := G) hC0 hG0 hkin hkin_bound hg hgb t
      refine hshift.congr ?_
      filter_upwards with ω
      unfold cloudValueNat
      congr 1
      funext i j
      rw [mMarkedShiftedEdge, if_pos ⟨i.isLt, j.isLt⟩]
    have hmax := integrable_mMaxCounts (q := q) α β r
    have hdiff := integrable_mAbsCountsSub (q := q) α β r
    have hnested : ∀ (k l : Fin (Nat.ceil (r : ℝ))), k ≤ l → ∀ x y : Fin q → ℝ,
        dyadicCell q (l : ℕ) x = dyadicCell q (l : ℕ) y →
          dyadicCell q (k : ℕ) x = dyadicCell q (k : ℕ) y := by
      intro k l hkl x y h
      exact dyadicCell_nested_global (by exact_mod_cast hkl) h
    have hmain := integral_maxCardValue_le_of_counts
      (P := twoMarkedCloudLaw (q := q) A B α β r)
      (K := Nat.ceil (r : ℝ))
      (cell := cell) hnested
      (base := base) hbase0 (weight := weight) hweight0
      (N := mSourceCount (A := A) (B := B))
      (M := mTargetCount (A := A) (B := B))
      (x := fun ω (i : Fin (mSourceCount ω)) =>
        cubeTruncPoint (mSourcePoint ω (i : ℕ)))
      (y := fun ω (j : Fin (mTargetCount ω)) =>
        cubeTruncPoint (mTargetPoint ω (j : ℕ)))
      (cost := fun ω (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)) =>
        mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
          t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G)
      hcost hnonneg hV hmax hDint hdiff (2 * (r : ℝ))
      (integral_mMaxCounts_le (q := q) α β r)
      D hDbound (Real.sqrt (2 * (r : ℝ)))
      (integral_mAbsCountsSub_le (q := q) α β r)
    have hpoint_le : ∀ ω : TwoMarkedCloudSpace q A B,
        markedTilted (q := q) (r := (r : ℝ)) kin g t ω ≤
        PartialMatching.maxCardValue (fun i : Fin (mSourceCount ω) =>
          fun j : Fin (mTargetCount ω) =>
            mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
              t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G) := by
      intro ω
      unfold markedTilted tiltedCloudValue
      rw [PartialMatching.maxCardValue_add_const]
      have hshift_nonneg : 0 ≤
          min ((mSourceCount ω : ℝ)) ((mTargetCount ω : ℝ)) * (|t| * G) :=
        mul_nonneg (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (mul_nonneg (abs_nonneg t) hG0)
      linarith
    have hpressure_le : markedPressure q A B α β r kin g t ≤
        ∫ ω, PartialMatching.maxCardValue (fun i : Fin (mSourceCount ω) =>
          fun j : Fin (mTargetCount ω) =>
            mKineticCost q (r : ℝ) kin ω (i : ℕ) (j : ℕ) +
              t * mProbe g ω (i : ℕ) (j : ℕ) + |t| * G)
          ∂(twoMarkedCloudLaw (q := q) A B α β r) := by
      unfold markedPressure
      exact integral_mono
        (integrable_markedTilted (q := q) α β r (C := C) (G := G)
          r.coe_nonneg hC0 hG0 hkin hkin_bound hg hgb t)
        hV hpoint_le
    have hmid : markedPressure q A B α β r kin g t ≤
        base * (2 * (r : ℝ)) +
          (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
            weight k * (D k + Real.sqrt (2 * (r : ℝ))) :=
      hpressure_le.trans hmain
    have hbase_bound := marked_base_discrepancy_bound q (Nat.ceil (r : ℝ))
      hqpos_nat hr1' hC0 hrK (C := C) (B := Bs)
    have hseries1 : (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
        (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) * D k ≤
          2 * C₀ * (r : ℝ) := by
      have h := series_min_part_le q (Nat.ceil (r : ℝ)) hq hr1' hK1 hrK hK_2r
        hC₀ hC₀0
      simpa only [D] using h
    have hseries2 : (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
        (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
          Real.sqrt (2 * (r : ℝ)) ≤
          (16 / 3) * (q : ℝ) * Real.sqrt 2 * (r : ℝ) :=
      series_sqrt_part_le q (Nat.ceil (r : ℝ)) hq hr1'
    have hsplit : (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
          weight k * (D k + Real.sqrt (2 * (r : ℝ))) =
        C * ((1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
              (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) * D k
            + (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
              (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
                Real.sqrt (2 * (r : ℝ))) := by
      have h1 : (∑ k : Fin (Nat.ceil (r : ℝ)),
            weight k * (D k + Real.sqrt (2 * (r : ℝ)))) =
          C * ((∑ k : Fin (Nat.ceil (r : ℝ)),
                (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) * D k)
              + (∑ k : Fin (Nat.ceil (r : ℝ)),
                (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
                  Real.sqrt (2 * (r : ℝ)))) := by
        conv_rhs => rw [mul_add]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [weight]
        ring
      rw [h1]
      ring
    have hseries : C * ((1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
              (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) * D k
            + (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
              (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
                Real.sqrt (2 * (r : ℝ))) ≤
        C * (2 * C₀ * (r : ℝ) +
          (16 / 3) * (q : ℝ) * Real.sqrt 2 * (r : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      linarith [hseries1, hseries2]
    have hK1_nonneg : 0 ≤ 8 * (q : ℝ) + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2 := by
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      have h1 : (0 : ℝ) ≤ 8 * (q : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ 2 * C₀ := by linarith
      have h3 : (0 : ℝ) ≤ (16 / 3) * (q : ℝ) * Real.sqrt 2 := by positivity
      linarith
    calc markedPressure q A B α β r kin g t
        ≤ base * (2 * (r : ℝ)) +
            (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
              weight k * (D k + Real.sqrt (2 * (r : ℝ))) := hmid
      _ = (C * (r ^ (2 / (q : ℝ)) *
              ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ (Nat.ceil (r : ℝ)))) + 2 * Bs) *
              (2 * (r : ℝ)) +
            C * ((1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
                (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) * D k
              + (1 / 2) * ∑ k : Fin (Nat.ceil (r : ℝ)),
                (r ^ (2 / (q : ℝ)) * ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ (k : ℕ))) *
                  Real.sqrt (2 * (r : ℝ))) := by
          rw [hsplit]
      _ ≤ (C * (8 * (q : ℝ) * (r : ℝ)) + 4 * Bs * (r : ℝ)) +
            C * (2 * C₀ * (r : ℝ) +
              (16 / 3) * (q : ℝ) * Real.sqrt 2 * (r : ℝ)) :=
          add_le_add hbase_bound hseries
      _ = (8 * (q : ℝ) + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2) * C * (r : ℝ)
            + 4 * Bs * (r : ℝ) := by ring
      _ ≤ (8 * (q : ℝ) + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2) *
              (C + Bs) * (r : ℝ) + 4 * (C + Bs) * (r : ℝ) := by
          have hCB : 0 ≤ C + Bs := add_nonneg hC0 hBs0
          have h1 : (8 * (q : ℝ) + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2) *
                C * (r : ℝ) ≤
              (8 * (q : ℝ) + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2) *
                (C + Bs) * (r : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hr0
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBs0) hK1_nonneg
          have h2 : 4 * Bs * (r : ℝ) ≤ 4 * (C + Bs) * (r : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hr0
            linarith
          linarith
      _ = (8 * (q : ℝ) + 4 + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2) *
            (C + Bs) * (r : ℝ) := by ring
      _ = (8 * (q : ℝ) + 4 + 2 * C₀ + (16 / 3) * (q : ℝ) * Real.sqrt 2) *
            (C + |t| * G) * (r : ℝ) := by
          dsimp only [Bs]

end OTSelector.Probability
