import OTSelector.Reconstruction.FinslerOriginalAmbientBlockExpectation
import OTSelector.Probability.MarkedGridDiscrepancy
import OTSelector.Probability.MarkedPressureBlockComparison
import OTSelector.Probability.MarkedPressureBlockSubadditivity

/-!
# Kernel-law transfers for the intensity-level block comparison

This module closes the three transfers isolated in
FinslerOriginalAmbientBlockExpectation.lean.  The kernel-marked cloud laws differ
from the constant-mark cloud laws only in the mark component; the positions are
still iid cube-uniform and the counts are still Poisson.  We therefore prove:

* the almost-everywhere unit-cube membership of kernel-marked clouds;
* the raw/encoded block-cloud agreement and the raw/encoded block-value
  agreement for kernel-marked clouds;
* the position-projection law of a kernel-marked cloud, which is the unmarked
  Poisson cloud law;
* the grid-discrepancy a.e. identification, integrability and expected bound for
  kernel-marked two-cloud laws.

The second part of the file integrates the deterministic grid block comparison
against the kernel-marked two-cloud law, using the leaf-block expectation
identity of FinslerOriginalAmbientBlockExpectation.lean, and obtains the
intensity-level comparison

  kernelMarkedPressure R <= blockKernelPressureSum (R / m ^ q) + repair,

with the intensity-dependent repair error carried explicitly.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open OTSelector OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## Almost-everywhere unit-cube membership -/

/-- Almost every position of a kernel-marked iid sequence lies in the unit cube.
The position marginal of the kernel-marked point law is the cube measure, so
this is the same statement as for the constant-mark sequence. -/
theorem ae_mem_unitCube_kernelMarkedSeqLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] :
    ∀ᵐ x ∂(kernelMarkedSeqLaw q A K), ∀ i, (x i).1 ∈ unitCube q := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    OTSelector.Probability.isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1) ⊗ₘ K) :=
    fun _ => inferInstance
  have hcube : ∀ᵐ y ∂((cubeMeasure (Fin q) 1) ⊗ₘ K), y.1 ∈ unitCube q := by
    have hmap : ((cubeMeasure (Fin q) 1) ⊗ₘ K).map Prod.fst = cubeMeasure (Fin q) 1 := by
      simpa only [Measure.fst] using Measure.fst_compProd (cubeMeasure (Fin q) 1) K
    have h1 : ∀ᵐ x ∂((cubeMeasure (Fin q) 1) ⊗ₘ K).map Prod.fst, x ∈ unitCube q := by
      rw [hmap]
      exact ae_mem_unitCubeSet_cubeMeasure q
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_unitCube q)).mp h1
  unfold kernelMarkedSeqLaw
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval_infinitePi
    (μ := fun _ : ℕ => (cubeMeasure (Fin q) 1) ⊗ₘ K) i).quasiMeasurePreserving.ae hcube

/-- Almost every point of a kernel-marked Poisson cloud lies in the unit cube. -/
theorem ae_mem_unitCube_kernelMarkedCloudLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] (r : ℝ≥0) :
    ∀ᵐ z ∂(kernelMarkedCloudLaw q A K r), ∀ i, (z.2 i).1 ∈ unitCube q := by
  haveI : IsProbabilityMeasure (kernelMarkedSeqLaw q A K) := inferInstance
  unfold kernelMarkedCloudLaw
  exact Measure.quasiMeasurePreserving_snd.ae (ae_mem_unitCube_kernelMarkedSeqLaw q A K)

/-- Almost every used source and target point of two kernel-marked clouds lies in
the unit cube. -/
theorem ae_points_mem_unitCube_twoKernelMarkedCloudLaw (q : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    ∀ᵐ ω ∂(twoKernelMarkedCloudLaw q A B Ks Kt r),
      (∀ i, mSourcePoint ω i ∈ unitCube q) ∧
        (∀ j, mTargetPoint ω j ∈ unitCube q) := by
  unfold twoKernelMarkedCloudLaw
  filter_upwards [
    Measure.quasiMeasurePreserving_fst.ae
      (ae_mem_unitCube_kernelMarkedCloudLaw (q := q) (A := A) Ks r),
    Measure.quasiMeasurePreserving_snd.ae
      (ae_mem_unitCube_kernelMarkedCloudLaw (q := q) (A := B) Kt r)] with ω h1 h2
  exact ⟨fun i => h1 i, fun j => h2 j⟩

/-! ## Raw and encoded block clouds -/

/-- On the unit cube, the raw block cloud and the encoded block cloud agree. -/
theorem blockLocalCloud_eq_encoded_of_mem_unitCubeSet (q m : ℕ) [NeZero m] (hm : 0 < m)
    (b : Fin q → Fin m) (z : MarkedCloudSpace q A)
    (hz : ∀ i, (z.2 i).1 ∈ unitCubeSet q) :
    blockLocalCloud (A := A) q m b z = blockLocalCloudEncoded (A := A) q m b z := by
  classical
  have hfil : (Finset.univ.filter (fun i : Fin z.1 =>
      ∀ l, blockIndex ((m : ℝ)⁻¹) ((z.2 i).1 l) = (b l).val)) =
      Finset.univ.filter (fun i : Fin z.1 =>
        markedLabelCode q m z i = finFunctionFinEquiv b) := by
    apply Finset.filter_congr
    intro i _
    exact (blockLabelCode_eq_finFunctionFinEquiv_iff (m := m) (hz i) b).symm
  unfold blockLocalCloud blockLocalCloudEncoded prefixBlockData
  exact sigma_orderIsoOfFin_congr hfil
    (fun i => (fun l => (m : ℝ) * localCoord ((m : ℝ)⁻¹) ((z.2 i).1 l), (z.2 i).2))

/-- Almost surely, the raw and encoded block clouds of a kernel-marked cloud agree. -/
theorem blockLocalCloud_ae_eq_encoded_kernel (q m : ℕ) [NeZero m] (hm : 0 < m)
    (r : ℝ≥0) (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] (b : Fin q → Fin m) :
    ∀ᵐ z ∂(kernelMarkedCloudLaw q A K r),
      blockLocalCloud (A := A) q m b z = blockLocalCloudEncoded (A := A) q m b z := by
  filter_upwards [ae_mem_unitCube_kernelMarkedCloudLaw (q := q) (A := A) K r] with z hz
  exact blockLocalCloud_eq_encoded_of_mem_unitCubeSet q m hm b z hz

/-- Almost surely, the raw and encoded block clouds of a kernel-marked cloud agree
simultaneously for all leaf blocks. -/
theorem blockLocalCloud_ae_eq_encoded_kernel_all (q m : ℕ) [NeZero m] (hm : 0 < m)
    (r : ℝ≥0) (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] :
    ∀ᵐ z ∂(kernelMarkedCloudLaw q A K r), ∀ b : Fin q → Fin m,
      blockLocalCloud (A := A) q m b z = blockLocalCloudEncoded (A := A) q m b z := by
  filter_upwards [ae_mem_unitCube_kernelMarkedCloudLaw (q := q) (A := A) K r] with z hz b
  exact blockLocalCloud_eq_encoded_of_mem_unitCubeSet q m hm b z hz

/-! ## The position marginal of the kernel-marked cloud law -/

/-- Projecting the kernel-marked iid sequence to its positions gives the
unmarked iid cube sequence law: the marks do not affect the positions. -/
theorem map_kernelMarkedSeqLaw_fst (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] :
    (kernelMarkedSeqLaw q A K).map
      (fun x : ℕ → (Fin q → ℝ) × A => fun i => (x i).1) = cubeSeqLaw q := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    OTSelector.Probability.isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1) ⊗ₘ K) :=
    fun _ => inferInstance
  unfold kernelMarkedSeqLaw cubeSeqLaw
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => (cubeMeasure (Fin q) 1) ⊗ₘ K)
    (f := fun (_ : ℕ) => (Prod.fst : (Fin q → ℝ) × A → (Fin q → ℝ)))
    (fun _ => measurable_fst)]
  congr 1
  funext i
  have hmap : ((cubeMeasure (Fin q) 1) ⊗ₘ K).map Prod.fst = cubeMeasure (Fin q) 1 := by
    simpa only [Measure.fst] using Measure.fst_compProd (cubeMeasure (Fin q) 1) K
  exact hmap

/-- The position projection of a kernel-marked Poisson cloud is the unmarked
Poisson cloud law. -/
theorem map_markedPosition_kernelMarkedCloudLaw (q : ℕ) (A : Type*) [MeasurableSpace A]
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] (r : ℝ≥0) :
    (kernelMarkedCloudLaw q A K r).map (markedPosition (q := q) (A := A)) =
      poissonCubeLaw q r := by
  unfold kernelMarkedCloudLaw poissonCubeLaw markedPosition
  rw [show (fun z : MarkedCloudSpace q A => (z.1, fun i => (z.2 i).1)) =
      Prod.map (id : ℕ → ℕ)
        (fun x : ℕ → (Fin q → ℝ) × A => fun i => (x i).1) from rfl]
  rw [← Measure.map_prod_map (poissonMeasure r) (kernelMarkedSeqLaw q A K)
      measurable_id (by fun_prop),
    Measure.map_id, map_kernelMarkedSeqLaw_fst (q := q) A K]

/-- The position projection of both clouds of the kernel-marked two-cloud law is
the unmarked two-cloud law. -/
theorem map_markedPosCloud_twoKernelMarkedCloudLaw (q : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (r : ℝ≥0) :
    (twoKernelMarkedCloudLaw q A B Ks Kt r).map
        (markedPosCloud (q := q) (A := A) (B := B)) = twoCloudLaw q r := by
  unfold twoKernelMarkedCloudLaw twoCloudLaw markedPosCloud
  rw [show (fun ω : MarkedCloudSpace q A × MarkedCloudSpace q B =>
        (markedPosition ω.1, markedPosition ω.2)) =
      Prod.map (markedPosition (q := q) (A := A)) (markedPosition (q := q) (A := B))
      from rfl]
  rw [← Measure.map_prod_map (kernelMarkedCloudLaw q A Ks r)
      (kernelMarkedCloudLaw q B Kt r)
      (measurable_markedPosition (q := q) (A := A))
      (measurable_markedPosition (q := q) (A := B)),
    map_markedPosition_kernelMarkedCloudLaw (q := q) (A := A) Ks r,
    map_markedPosition_kernelMarkedCloudLaw (q := q) (A := B) Kt r]

/-! ## The grid discrepancy under the kernel-marked law -/

/-- The expected grid discrepancy of the two-cloud marked law is the expected
grid discrepancy of the unmarked two-cloud law. -/
theorem integral_gridDiscMarkedDiscrepancy_eq_cloud (q m J k : ℕ) [NeZero m]
    (hm : 0 < m) (hJ : m ≤ 2 ^ J) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (R : ℝ≥0) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
          (hm := hm) (hJ := hJ) (A := A) (B := B) ω
        ∂(twoMarkedCloudLaw (q := q) A B α β R)
      = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R) := by
  calc
    ∫ ω, gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
          (hm := hm) (hJ := hJ) (A := A) (B := B) ω
        ∂(twoMarkedCloudLaw (q := q) A B α β R)
        = ∫ ω, gridDiscCloudDiscrepancy q m J k hm hJ
              (markedPosCloud (q := q) (A := A) (B := B) ω)
            ∂(twoMarkedCloudLaw (q := q) A B α β R) := by
          exact integral_congr_ae (gridDiscMarkedDiscrepancy_eq_cloud_ae q m J k hm hJ A B α β R)
      _ = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z
            ∂((twoMarkedCloudLaw (q := q) A B α β R).map
              (markedPosCloud (q := q) (A := A) (B := B))) := by
          exact (integral_map (measurable_markedPosCloud q).aemeasurable
            (measurable_gridDiscCloudDiscrepancy q m J k hm hJ).aestronglyMeasurable).symm
      _ = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R) := by
          rw [map_markedPosCloud_twoMarkedCloudLaw (q := q) α β R]

/-- Almost everywhere, the marked truncated discrepancy of a kernel-marked
two-cloud sample is the discrepancy of its position projection. -/
theorem gridDiscMarkedDiscrepancy_eq_cloud_ae_kernel (q m J k : ℕ) [NeZero m]
    (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (R : ℝ≥0) :
    (fun ω => gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
        (hm := hm) (hJ := hJ) (A := A) (B := B) ω)
      =ᵐ[twoKernelMarkedCloudLaw q A B Ks Kt R]
    (fun ω => gridDiscCloudDiscrepancy q m J k hm hJ
      (markedPosCloud (q := q) (A := A) (B := B) ω)) := by
  filter_upwards [ae_points_mem_unitCube_twoKernelMarkedCloudLaw (q := q) Ks Kt R] with ω hω
  unfold gridDiscMarkedDiscrepancy gridDiscCloudDiscrepancy
  have hsrc : markedTruncSource q ω =
      fun i : Fin (mSourceCount ω) => mSourcePoint ω (i : ℕ) := by
    funext i
    exact cubeTruncPoint_eq_of_mem (hω.1 (i : ℕ))
  have htgt : markedTruncTarget q ω =
      fun j : Fin (mTargetCount ω) => mTargetPoint ω (j : ℕ) := by
    funext j
    exact cubeTruncPoint_eq_of_mem (hω.2 (j : ℕ))
  simp only [hsrc, htgt, markedPosCloud, markedPosition, mSourcePoint, mTargetPoint]
  rfl

/-- The grid discrepancy is integrable under the kernel-marked two-cloud law. -/
theorem integrable_markedGridDiscrepancy_kernel (q m J k : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (R : ℝ≥0) :
    Integrable (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ)
      (twoKernelMarkedCloudLaw q A B Ks Kt R) := by
  classical
  have hsrc := integrable_mSourceCount_kernel q Ks Kt R
  have htgt := integrable_mTargetCount_kernel q Ks Kt R
  refine (hsrc.add htgt).mono'
    (measurable_markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ).aestronglyMeasurable ?_
  filter_upwards with ω
  have h := cellDiscrepancy_le_card (gridCellLabel q m J k hm hJ)
    (markedTruncSource q ω) (markedTruncTarget q ω)
  simpa only [Pi.add_apply, markedGridDiscrepancy, Real.norm_eq_abs, abs_of_nonneg
    (cellDiscrepancy_nonneg _ _ _)] using h

/-- The expected level-`k` grid discrepancy under the kernel-marked two-cloud law
obeys the same uniform bound as in the constant-mark lane. -/
theorem integral_markedGridDiscrepancy_bound_kernel (q m J k : ℕ) [NeZero m]
    (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (R : ℝ≥0) :
    ∫ ω, markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt R)
      ≤ Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
  classical
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure (Ks (fun _ : Fin q => 0))
  haveI : Nonempty B := nonempty_of_isProbabilityMeasure (Kt (fun _ : Fin q => 0))
  have hfun : markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ =
      gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
        (hm := hm) (hJ := hJ) (A := A) (B := B) := rfl
  rw [hfun]
  have hker : ∫ ω : TwoMarkedCloudSpace q A B,
        gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
          (hm := hm) (hJ := hJ) (A := A) (B := B) ω
        ∂(twoKernelMarkedCloudLaw q A B Ks Kt R)
      = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R) := by
    calc
      ∫ ω, gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
          (hm := hm) (hJ := hJ) (A := A) (B := B) ω
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt R)
          = ∫ ω, gridDiscCloudDiscrepancy q m J k hm hJ
                (markedPosCloud (q := q) (A := A) (B := B) ω)
              ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) := by
            exact integral_congr_ae (gridDiscMarkedDiscrepancy_eq_cloud_ae_kernel q m J k hm hJ Ks Kt R)
        _ = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z
              ∂((twoKernelMarkedCloudLaw q A B Ks Kt R).map
                (markedPosCloud (q := q) (A := A) (B := B))) := by
            exact (integral_map (measurable_markedPosCloud q).aemeasurable
              (measurable_gridDiscCloudDiscrepancy q m J k hm hJ).aestronglyMeasurable).symm
        _ = ∫ z, gridDiscCloudDiscrepancy q m J k hm hJ z ∂(twoCloudLaw q R) := by
            rw [map_markedPosCloud_twoKernelMarkedCloudLaw (q := q) Ks Kt R]
  rw [hker]
  rw [← integral_gridDiscMarkedDiscrepancy_eq_cloud (q := q) (m := m) (J := J) (k := k)
    hm hJ (Ks (fun _ : Fin q => 0)) (Kt (fun _ : Fin q => 0)) R]
  exact integral_markedGridDiscrepancy_le q m J k hm hJ A B
    (Ks (fun _ : Fin q => 0)) (Kt (fun _ : Fin q => 0)) R

/-! ## The expected repair term under the kernel-marked law -/

/-- The hierarchical grid repair term is integrable under the kernel-marked
two-cloud law. -/
theorem integrable_gridRepair_kernel (q m J : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (R : ℝ≥0) {r t C G : ℝ} :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
          (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
            markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) := by
  classical
  have hDint : ∀ k, Integrable
      (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ)
      (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    fun k => integrable_markedGridDiscrepancy_kernel q m J k hm hJ Ks Kt R
  apply integrable_finsetSum
  intro k _
  exact ((hDint k).sub (hDint (k - 1))).const_mul _

/-- The expected hierarchical repair term under the kernel-marked two-cloud law
is bounded by the sum of the sharp level discrepancies. -/
theorem integral_gridRepair_le_kernel (q m J : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (R : ℝ≥0) {r t C G : ℝ}
    (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
          (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
            markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt R)
    ≤ ∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
  classical
  let D : ℕ → TwoMarkedCloudSpace q A B → ℝ :=
    fun k => markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ
  let Bw : ℕ → ℝ := fun k => markedGridRepairBound q r C t G k
  have hDint : ∀ k, Integrable (D k) (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    fun k => integrable_markedGridDiscrepancy_kernel q m J k hm hJ Ks Kt R
  have hDnonneg : ∀ k ω, 0 ≤ D k ω := fun k ω => cellDiscrepancy_nonneg _ _ _
  have hBw : ∀ k ∈ Finset.Icc 1 J, 0 ≤ Bw k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hpow : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (k - 1) := pow_nonneg (by norm_num) _
    have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    unfold Bw markedGridRepairBound
    rw [if_neg (by omega)]
    unfold markedGridRepairWeight
    have h1 : 0 ≤ 16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) := by
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      positivity
    have h2 : 0 ≤ 2 * |t| * G := by positivity
    linarith
  have hInt1 : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 J,
      Bw k * (1 / 2 : ℝ) * (D k ω - D (k - 1) ω))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) := by
    apply integrable_finsetSum
    intro k _
    exact ((hDint k).sub (hDint (k - 1))).const_mul _
  have hInt2 : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 J,
      Bw k * (1 / 2 : ℝ) * D k ω)
      (twoKernelMarkedCloudLaw q A B Ks Kt R) := by
    apply integrable_finsetSum
    intro k _
    exact (hDint k).const_mul _
  have hle : ∀ ω, (∑ k ∈ Finset.Icc 1 J,
        Bw k * (1 / 2 : ℝ) * (D k ω - D (k - 1) ω))
      ≤ ∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) * D k ω := by
    intro ω
    apply Finset.sum_le_sum
    intro k hk
    have hb := hBw k hk
    have hprev := hDnonneg (k - 1) ω
    nlinarith
  calc ∫ ω, (∑ k ∈ Finset.Icc 1 J,
        Bw k * (1 / 2 : ℝ) * (D k ω - D (k - 1) ω))
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt R)
      ≤ ∫ ω, (∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) * D k ω)
        ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) :=
        integral_mono hInt1 hInt2 hle
    _ = ∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) *
          ∫ ω, D k ω ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k _
          rw [integral_const_mul]
        · intro k _
          exact (hDint k).const_mul _
    _ ≤ ∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left
        · exact integral_markedGridDiscrepancy_bound_kernel q m J k hm hJ Ks Kt R
        · have hb := hBw k hk
          nlinarith


/-! ## Integrability and the Fubini assembly over the leaf blocks -/

/-- Integrability of one encoded leaf-block value under the kernel-marked
two-cloud law, by domination with the source count. -/
private theorem integrable_blockTiltedValue_encoded_kernel (q m : ℕ) [NeZero m] (hm : 0 < m)
    (R : ℝ≥0) {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (b : Fin q → Fin m) :
    Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
        (blockLocalCloudEncoded (A := A) q m b ω.1)
        (blockLocalCloudEncoded (A := B) q m b ω.2))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) := by
  classical
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure (Ks (fun _ : Fin q => 0))
  haveI : Nonempty B := nonempty_of_isProbabilityMeasure (Kt (fun _ : Fin q => 0))
  let c : ℝ≥0 := R / (m ^ q : ℝ≥0)
  let rloc : ℝ := (c : ℝ)
  let PosA := (Fin q → ℝ) × A
  let PosB := (Fin q → ℝ) × B
  let encA : MarkedCloudSpace q A → BlockData PosA := blockLocalCloudEncoded (A := A) q m b
  let encB : MarkedCloudSpace q B → BlockData PosB := blockLocalCloudEncoded (A := B) q m b
  let Bnd : ℝ := rloc ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G
  have hc0 : 0 ≤ rloc := c.coe_nonneg
  have hEncMeas : Measurable fun ω : TwoMarkedCloudSpace q A B => (encA ω.1, encB ω.2) :=
    ((measurable_blockLocalCloudEncoded (A := A) q m b).comp measurable_fst).prodMk
      ((measurable_blockLocalCloudEncoded (A := B) q m b).comp measurable_snd)
  have hΦ : Measurable fun d : BlockData PosA × BlockData PosB =>
      blockTiltedValue q rloc kin g t d.1 d.2 :=
    measurable_blockTiltedValue q rloc hc0 hC0 hG0 hkin hkin_bound hg hgb t
  have hmeas : AEStronglyMeasurable (fun ω : TwoMarkedCloudSpace q A B =>
      blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    (hΦ.comp hEncMeas).aestronglyMeasurable
  have hBnd0 : 0 ≤ Bnd := by
    dsimp only [Bnd]
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg hc0 _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
      (mul_nonneg (abs_nonneg t) hG0)
  have hcount : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((mSourceCount ω : ℕ) : ℝ) * Bnd) (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    (integrable_mSourceCount_kernel q Ks Kt R).mul_const _
  change Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      blockTiltedValue q rloc kin g t (encA ω.1) (encB ω.2))
      (twoKernelMarkedCloudLaw q A B Ks Kt R)
  refine hcount.mono' hmeas ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  have hb := abs_blockTiltedValue_le q (r := rloc) (C := C) (G := G) (t := t)
    hc0 hC0 hG0 hkin_bound hgb (encA ω.1) (encB ω.2)
  have hle : ((min (encA ω.1).1 (encB ω.2).1 : ℕ) : ℝ) ≤ (mSourceCount ω : ℝ) := by
    have h1 : (encA ω.1).1 ≤ (ω.1).1 :=
      blockLocalCloudEncoded_fst_le (A := A) q m b ω.1
    have h2 : ((min (encA ω.1).1 (encB ω.2).1 : ℕ) : ℝ) ≤ ((encA ω.1).1 : ℝ) := by
      exact_mod_cast min_le_left _ _
    have h3 : ((encA ω.1).1 : ℝ) ≤ (mSourceCount ω : ℝ) := by
      exact_mod_cast h1
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hle hBnd0)

/-- **Fubini assembly over the leaf blocks.**  The expected encoded leaf-block sum
of the kernel-marked two-cloud law is the aggregate block pressure at the reduced
intensity. -/
private theorem integral_blockSum_encoded_kernel (q m : ℕ) [NeZero m] (hm : 0 < m)
    (R : ℝ≥0) {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        (∑ b : Fin q → Fin m,
          blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
            (blockLocalCloudEncoded (A := A) q m b ω.1)
            (blockLocalCloudEncoded (A := B) q m b ω.2))
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) =
      blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t := by
  classical
  rw [integral_finset_sum]
  · unfold blockKernelPressureSum
    exact Finset.sum_congr rfl fun b _ =>
      integral_blockTiltedValue_blockLocalCloudEncoded q m hm R hC0 hG0
        hkin hkin_bound hg hgb b
  · intro b _
    exact integrable_blockTiltedValue_encoded_kernel q m hm R hC0 hG0
      hkin hkin_bound hg hgb b
/-! ## The leaf-block sum expectation identity in raw form -/

/-- Almost everywhere, the raw grid block sum of a kernel-marked two-cloud sample
equals the encoded leaf-block sum at the reduced intensity. -/
theorem ae_gridBlockSum_eq_blockSum_kernel (q m J : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (hq : 0 < q)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (R : ℝ≥0)
    {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G) :
    (fun ω : TwoMarkedCloudSpace q A B =>
        ∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost
              (fun i : Fin (mSourceCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
              (fun j : Fin (mTargetCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
              (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
      =ᵐ[twoKernelMarkedCloudLaw q A B Ks Kt R]
    (fun ω : TwoMarkedCloudSpace q A B =>
        ∑ b : Fin q → Fin m,
          blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
            (blockLocalCloudEncoded (A := A) q m b ω.1)
            (blockLocalCloudEncoded (A := B) q m b ω.2)) := by
  classical
  have hrloc : (R : ℝ) / ((m : ℝ) ^ q) = ((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_div]
    push_cast
    ring
  have hrawA : ∀ᵐ ω ∂(twoKernelMarkedCloudLaw q A B Ks Kt R),
      ∀ b : Fin q → Fin m,
        blockLocalCloud (A := A) q m b ω.1 = blockLocalCloudEncoded (A := A) q m b ω.1 := by
    have h := ae_fst_of_ae (μ := kernelMarkedCloudLaw q A Ks R)
      (ν := kernelMarkedCloudLaw q B Kt R)
      (blockLocalCloud_ae_eq_encoded_kernel_all q m hm R Ks)
    simpa only [twoKernelMarkedCloudLaw] using h
  have hrawB : ∀ᵐ ω ∂(twoKernelMarkedCloudLaw q A B Ks Kt R),
      ∀ b : Fin q → Fin m,
        blockLocalCloud (A := B) q m b ω.2 = blockLocalCloudEncoded (A := B) q m b ω.2 := by
    have h := ae_snd_of_ae (μ := kernelMarkedCloudLaw q A Ks R)
      (ν := kernelMarkedCloudLaw q B Kt R)
      (blockLocalCloud_ae_eq_encoded_kernel_all q m hm R Kt)
    simpa only [twoKernelMarkedCloudLaw] using h
  filter_upwards [ae_points_mem_unitCube_twoKernelMarkedCloudLaw (q := q) Ks Kt R,
    hrawA, hrawB] with ω hω hrawA' hrawB'
  obtain ⟨hz1, hz2⟩ := hω
  change (∑ c : Fin q → Fin (2 ^ J + 1),
      markedBlockValue q m J hm hJ (R : ℝ) t kin g ω c) =
    ∑ b : Fin q → Fin m,
      blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
        (blockLocalCloudEncoded (A := A) q m b ω.1)
        (blockLocalCloudEncoded (A := B) q m b ω.2)
  rw [markedBlockValue_sum_eq_realBlocks hm hJ (R : ℝ) t (kin := kin) (g := g) ω]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [markedBlockValue_eq_blockTiltedValue hm hJ hq R.coe_nonneg hC0 hG0
    hkin_bound hkin_homog hgb b ω hz1 hz2, hrloc, hrawA' b, hrawB' b]

/-- **The leaf-block sum expectation identity in raw form.**  The expected raw
grid block sum of the ambient kernel-marked two-cloud law at intensity R is the
aggregate block pressure of the block-rescaled kernels at intensity R / m ^ q. -/
theorem integral_gridBlockSum_kernel (q m J : ℕ) [NeZero m] (hm : 0 < m)
    (hJ : m ≤ 2 ^ J) (hq : 0 < q)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt] (R : ℝ≥0)
    {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∫ ω : TwoMarkedCloudSpace q A B,
        (∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost
              (fun i : Fin (mSourceCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
              (fun j : Fin (mTargetCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
              (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) =
      blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t := by
  classical
  calc
    ∫ ω : TwoMarkedCloudSpace q A B,
        (∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost
              (fun i : Fin (mSourceCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
              (fun j : Fin (mTargetCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
              (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
      ∂(twoKernelMarkedCloudLaw q A B Ks Kt R)
        = ∫ ω : TwoMarkedCloudSpace q A B,
            (∑ b : Fin q → Fin m,
              blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
                (blockLocalCloudEncoded (A := A) q m b ω.1)
                (blockLocalCloudEncoded (A := B) q m b ω.2))
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) := by
          exact integral_congr_ae (ae_gridBlockSum_eq_blockSum_kernel q m J hm hJ hq
            Ks Kt R hC0 hG0 hkin_bound hkin_homog hgb)
    _ = blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t :=
        integral_blockSum_encoded_kernel q m hm R hC0 hG0
          hkin hkin_bound hg hgb


/-! ## The intensity-level kernel-marked block comparison -/

/-- **Kernel-marked pressure versus block-rescaled pressure.**  For every pair of
mark kernels, the kernel-marked pressure at intensity `R` is bounded by the
aggregate block-rescaled pressure at intensity `R / m ^ q` plus the
intensity-dependent hierarchical grid repair error.  The repair error is carried
explicitly: a comparison with a fixed error independent of `R` is unattainable. -/
theorem kernelMarkedPressure_le_blockScale_add_repair (q m J : ℕ) [NeZero m]
    (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (R : ℝ≥0) {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    kernelMarkedPressure q A B Ks Kt R kin g t ≤
        blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
          gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
            (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
              Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))) := by
  classical
  have hq0 : 0 < q := by omega
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure (Ks (fun _ : Fin q => 0))
  haveI : Nonempty B := nonempty_of_isProbabilityMeasure (Kt (fun _ : Fin q => 0))
  have hleaf := integral_gridBlockSum_kernel q m J hm hJ hq0 Ks Kt R
    (t := t) hC0 hG0 hkin hkin_bound hkin_homog hg hgb
  have hcongr := ae_gridBlockSum_eq_blockSum_kernel q m J hm hJ hq0 Ks Kt R
    (t := t) hC0 hG0 hkin_bound hkin_homog hgb
  have hIntEnc : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ∑ b : Fin q → Fin m,
        blockTiltedValue q (((R / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ)) kin g t
          (blockLocalCloudEncoded (A := A) q m b ω.1)
          (blockLocalCloudEncoded (A := B) q m b ω.2))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) := by
    apply integrable_finsetSum
    intro b _
    exact integrable_blockTiltedValue_encoded_kernel q m hm R hC0 hG0
      hkin hkin_bound hg hgb b
  have hIntBlock : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ∑ c : Fin q → Fin (2 ^ J + 1),
        PartialMatching.maxCardValue
          (blockCost
            (fun i : Fin (mSourceCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
            (fun j : Fin (mTargetCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
            (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    hIntEnc.congr hcongr.symm
  have hIntT : Integrable (markedTilted q (R : ℝ) kin g t)
      (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    integrable_markedTilted_kernel q Ks Kt R R.coe_nonneg hC0 hG0
      hkin hkin_bound hg hgb t
  have hIntRepair : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
          (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
            markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    integrable_gridRepair_kernel q m J hm hJ Ks Kt R (r := (R : ℝ))
  have hpt : ∀ ω : TwoMarkedCloudSpace q A B,
      markedTilted q (R : ℝ) kin g t ω ≤
        (∑ c : Fin q → Fin (2 ^ J + 1),
          PartialMatching.maxCardValue
            (blockCost
              (fun i : Fin (mSourceCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
              (fun j : Fin (mTargetCount ω) =>
                gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
              (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
        + ∑ k ∈ Finset.Icc 1 J,
            markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
              (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
                markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω) := by
    intro ω
    exact markedTilted_le_gridBlockSum_add_repair (q := q) (m := m) (J := J) hm hJ hJ2
      (r := (R : ℝ)) (t := t) (C := C) (G := G) R.coe_nonneg hC0 hG0
      hkin_nonneg hkin_bound hgb ω
  have hIntSum : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      (∑ c : Fin q → Fin (2 ^ J + 1),
        PartialMatching.maxCardValue
          (blockCost
            (fun i : Fin (mSourceCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
            (fun j : Fin (mTargetCount ω) =>
              gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
            (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
        + ∑ k ∈ Finset.Icc 1 J,
            markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
              (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
                markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
      (twoKernelMarkedCloudLaw q A B Ks Kt R) :=
    hIntBlock.add hIntRepair
  have hmono : kernelMarkedPressure q A B Ks Kt R kin g t ≤
      blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
        ∫ ω, (∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
              markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) := by
    calc kernelMarkedPressure q A B Ks Kt R kin g t
        = ∫ ω, markedTilted q (R : ℝ) kin g t ω
            ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) := rfl
      _ ≤ ∫ ω, ((∑ c : Fin q → Fin (2 ^ J + 1),
            PartialMatching.maxCardValue
              (blockCost
                (fun i : Fin (mSourceCount ω) =>
                  gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
                (fun j : Fin (mTargetCount ω) =>
                  gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
                (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
            + ∑ k ∈ Finset.Icc 1 J,
                markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
                  (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
                    markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) :=
          integral_mono hIntT hIntSum hpt
      _ = ∫ ω, (∑ c : Fin q → Fin (2 ^ J + 1),
            PartialMatching.maxCardValue
              (blockCost
                (fun i : Fin (mSourceCount ω) =>
                  gridCellLabel q m J J hm hJ (markedTruncSource q ω i))
                (fun j : Fin (mTargetCount ω) =>
                  gridCellLabel q m J J hm hJ (markedTruncTarget q ω j))
                (fun i j => markedEdgeCost q ((R : ℝ)) kin g t ω (i : ℕ) (j : ℕ)) c))
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) +
          ∫ ω, (∑ k ∈ Finset.Icc 1 J,
            markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
              (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
                markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
            ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) :=
          integral_add hIntBlock hIntRepair
      _ = blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
          ∫ ω, (∑ k ∈ Finset.Icc 1 J,
            markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
              (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
                markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
            ∂(twoKernelMarkedCloudLaw q A B Ks Kt R) := by
          rw [hleaf]
  have hrep := integral_gridRepair_le_kernel q m J hm hJ Ks Kt R
    (r := (R : ℝ)) (t := t) (C := C) (G := G) R.coe_nonneg hC0 hG0
  obtain ⟨_hKq0, hKq⟩ := grid_repair_sum_le q J hq m hm hJ2
    (R := (R : ℝ)) (C := C) (G := G) (t := t) R.coe_nonneg hC0 hG0
  have hsum_eq : (∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q ((R : ℝ)) C t G k * (1 / 2 : ℝ) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ))) =
      (1 / 2) * (∑ k ∈ Finset.Icc 1 J,
        (16 * ((R : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    unfold markedGridRepairBound markedGridRepairWeight
    rw [if_neg (by omega : k ≠ 0)]
    ring
  refine hmono.trans ?_
  calc blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
        ∫ ω, (∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
              markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
          ∂(twoKernelMarkedCloudLaw q A B Ks Kt R)
      ≤ blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
        ∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
            Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
        linarith [hrep]
    _ = blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
        (1 / 2) * (∑ k ∈ Finset.Icc 1 J,
          (16 * ((R : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
              2 * |t| * G) *
            Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ))) := by
        rw [hsum_eq]
    _ ≤ blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
        gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
          (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
            Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))) := by
        linarith [hKq]

end OTSelector.Reconstruction