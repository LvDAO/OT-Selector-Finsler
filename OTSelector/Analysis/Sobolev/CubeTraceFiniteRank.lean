import OTSelector.Analysis.Sobolev.BoxTraceCompactness
import OTSelector.Analysis.Sobolev.ProductBoxPoincare
import OTSelector.MeasureTheory.Integral.BoxPartitionCells
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeTraceCompactnessFiniteRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeTraceCompactnessFiniteRank`; the selected original proof blocks follow. -/
section

/-!
Conditions: C1 functions on the cube with the stated gradient energy control and the explicit finite dyadic face partition.

Objects: Finite-rank collar-mean trace approximants and a common approximation error tending to zero for the whole bounded-energy family.

Proof detail: Apply cellwise face/collar Poincaré, add the disjoint cells, dominate collar energy by unit-cube energy and choose one dyadic mesh.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Explicit finite-rank trace compactness argument. It proves the needed approximation and does not assume Rellich/trace compactness as a callback.
-/

/-! Actual finite-rank approximation of smooth cube traces by collar averages. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- The original average of a function over a literal face-cell collar. -/
def boxCollarMean {q : ℕ} (f : (Fin q → ℝ) × ℝ → ℝ) (a b : Fin q → ℝ) (h : ℝ) : ℝ :=
  (volume.real (Icc a b ×ˢ Icc (0 : ℝ) h))⁻¹ *
    (∫ p in Icc a b ×ˢ Icc (0 : ℝ) h, f p)

/-- The original coordinate gradient's squared L2 energy on a literal collar. -/
def boxCollarGradientEnergy {q : ℕ} (f : (Fin q → ℝ) × ℝ → ℝ)
    (a b : Fin q → ℝ) (h : ℝ) : ℝ :=
  (∑ i : Fin q, ∫ p in Icc a b ×ˢ Icc (0 : ℝ) h,
    (fderiv ℝ f p (Pi.single i 1, 0))^2) +
    (∫ p in Icc a b ×ˢ Icc (0 : ℝ) h, (fderiv ℝ f p (0, 1))^2)

/-- A cell's literal collar average approximates the actual face trace,
with error proportional to its side length and original gradient energy. -/
theorem smooth_box_face_trace_cell_mean_sq_le
    {q : ℕ} {a b : Fin q → ℝ} (hab : ∀ i, a i < b i)
    {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {h : ℝ} (hh : 0 < h) (hside : ∀ i, b i - a i ≤ h) :
    (∫ y in Icc a b, (f (y, 0) - boxCollarMean f a b h)^2) ≤
      ((q + 2 : ℕ) : ℝ) * h * boxCollarGradientEnergy f a b h := by
  have hp := smooth_product_box_poincare_sq_of_side_le hab hh hf hh.le hside (by simp)
  have ht := smooth_box_face_trace_sq_mul_le (a := a) (b := b)
    (hf.sub (contDiff_const (c := boxCollarMean f a b h))) hh
  simp only [fderiv_sub_const] at ht
  change h * (∫ y in Icc a b, (f (y, 0) - boxCollarMean f a b h)^2) ≤
    2 * (∫ p in Icc a b ×ˢ Icc 0 h, (f p - boxCollarMean f a b h)^2) +
      h^2 * (∫ p in Icc a b ×ˢ Icc 0 h, (fderiv ℝ f p (0, 1))^2) at ht
  change 2 * (∫ p in Icc a b ×ˢ Icc 0 h, (f p - boxCollarMean f a b h)^2) ≤
    ((q + 1 : ℕ) : ℝ) * h^2 * boxCollarGradientEnergy f a b h at hp
  have hn : (∫ p in Icc a b ×ˢ Icc 0 h, (fderiv ℝ f p (0, 1))^2) ≤
      boxCollarGradientEnergy f a b h := by
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)))
  have hn' := mul_le_mul_of_nonneg_left hn (sq_nonneg h)
  apply (mul_le_mul_iff_right₀ hh).mp
  have hc : ((q + 2 : ℕ) : ℝ) = ((q + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hc]
  nlinarith

/-- Literal dyadic collar means are the coefficients of the finite step trace. -/
def originalDyadicTraceMeans {q : ℕ} (f : (Fin q → ℝ) × ℝ → ℝ) (n : ℕ) :
    (originalDyadicFacePartition (ι := Fin q) n).boxes → ℝ :=
  fun J ↦ boxCollarMean f J.1.lower J.1.upper ((1 : ℝ) / 2^n)

/-- The finite step approximation uses only original collar averages. -/
def originalDyadicTraceApprox {q : ℕ} (f : (Fin q → ℝ) × ℝ → ℝ) (n : ℕ) :
    (Fin q → ℝ) → ℝ :=
  boxFaceStepLinear (originalDyadicFacePartition n) (originalDyadicTraceMeans f n)

/-- The entire family of actual approximants at a fixed scale lies in one
finite-dimensional range, independently of the function being approximated. -/
theorem originalDyadicTraceApprox_mem_finiteDimensional_range
    {q : ℕ} (f : (Fin q → ℝ) × ℝ → ℝ) (n : ℕ) :
    originalDyadicTraceApprox f n ∈
      (boxFaceStepLinear (originalDyadicFacePartition (ι := Fin q) n)).range :=
  ⟨originalDyadicTraceMeans f n, rfl⟩

/-- Actual dyadic cell errors sum to a full-face approximation estimate.
The true squared L2 error is O(h) in the original gradient energy. -/
theorem smooth_originalDyadicTraceApprox_error_sq_le
    {q : ℕ} {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
      (f (y, 0) - originalDyadicTraceApprox f n y)^2) ≤
      ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n) *
        boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) ((1 : ℝ) / 2^n) := by
  classical
  let π := originalDyadicFacePartition (ι := Fin q) n
  let h : ℝ := 1 / 2^n
  have hh : 0 < h := by positivity
  have hπ := isPartition_originalDyadicFacePartition (ι := Fin q) n
  have herr : (∫ y in (originalUnitFaceBox (Fin q)).Icc,
      (f (y, 0) - originalDyadicTraceApprox f n y)^2) =
      ∑ J : π.boxes, ∫ y in J.1.Icc,
        (f (y, 0) - boxCollarMean f J.1.lower J.1.upper h)^2 := by
    exact integral_boxFaceStep_error_sq_eq_sum π hπ
      (hf.continuous.comp (continuous_id.prodMk continuous_const)) (originalDyadicTraceMeans f n)
  have hdf (v : (Fin q → ℝ) × ℝ) : Continuous (fun p ↦ (fderiv ℝ f p v)^2) :=
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  have hsum : (∑ J : π.boxes, boxCollarGradientEnergy f J.1.lower J.1.upper h) =
      boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) h := by
    unfold boxCollarGradientEnergy
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      exact sum_integral_box_cell_collars_eq_integral π hπ (hdf (Pi.single i 1, 0)) h
    · exact sum_integral_box_cell_collars_eq_integral π hπ (hdf (0, 1)) h
  calc
    _ = ∑ J : π.boxes, ∫ y in J.1.Icc,
        (f (y, 0) - boxCollarMean f J.1.lower J.1.upper h)^2 := herr
    _ ≤ ∑ J : π.boxes, ((q + 2 : ℕ) : ℝ) * h *
        boxCollarGradientEnergy f J.1.lower J.1.upper h := by
      apply Finset.sum_le_sum
      intro J _
      exact smooth_box_face_trace_cell_mean_sq_le J.1.lower_lt_upper hf hh
        (fun i ↦ (originalDyadicFacePartition_side J.2 i).le)
    _ = _ := by rw [← Finset.mul_sum, hsum]

/-- The original collar energy is nonnegative without a regularity assumption. -/
theorem boxCollarGradientEnergy_nonneg
    {q : ℕ} (f : (Fin q → ℝ) × ℝ → ℝ) (a b : Fin q → ℝ) (h : ℝ) :
    0 ≤ boxCollarGradientEnergy f a b h :=
  add_nonneg (Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)))
    (integral_nonneg (fun _ ↦ sq_nonneg _))

/-- A smaller original collar carries no more gradient energy than a larger one. -/
theorem boxCollarGradientEnergy_mono
    {q : ℕ} {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (a b : Fin q → ℝ) {h k : ℝ} (hhk : h ≤ k) :
    boxCollarGradientEnergy f a b h ≤ boxCollarGradientEnergy f a b k := by
  have hdir (v : (Fin q → ℝ) × ℝ) :
      (∫ p in Icc a b ×ˢ Icc (0 : ℝ) h, (fderiv ℝ f p v)^2) ≤
        ∫ p in Icc a b ×ˢ Icc (0 : ℝ) k, (fderiv ℝ f p v)^2 := by
    have hc : Continuous (fun p ↦ (fderiv ℝ f p v)^2) :=
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
    have hint : IntegrableOn (fun p ↦ (fderiv ℝ f p v)^2)
        (Icc a b ×ˢ Icc (0 : ℝ) k) volume := by
      rw [← Icc_prod_eq (a, (0 : ℝ)) (b, k)]
      exact hc.continuousOn.integrableOn_Icc
    exact setIntegral_mono_set hint (Eventually.of_forall (fun _ ↦ sq_nonneg _))
      (Set.prod_mono subset_rfl (Icc_subset_Icc le_rfl hhk)).eventuallyLE
  exact add_le_add (Finset.sum_le_sum (fun i _ ↦ hdir (Pi.single i 1, 0))) (hdir (0, 1))

/-- The finite-rank squared trace error is bounded by the fixed original unit
cube gradient energy times the true dyadic mesh width. -/
theorem smooth_originalDyadicTraceApprox_error_sq_le_unit_energy
    {q : ℕ} {f : (Fin q → ℝ) × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
      (f (y, 0) - originalDyadicTraceApprox f n y)^2) ≤
      ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n) *
        boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 := by
  apply (smooth_originalDyadicTraceApprox_error_sq_le hf n).trans
  apply mul_le_mul_of_nonneg_left
    (boxCollarGradientEnergy_mono hf _ _ ?_) (by positivity)
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

/-- Actual collar-mean approximants give a uniform finite-dimensional
approximation for all smooth functions with unit original gradient energy.
The same finite dyadic scale works for the entire family. -/
theorem exists_originalDyadicTraceApprox_uniform_error_sq_lt
    (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ (f : (Fin q → ℝ) × ℝ → ℝ), ContDiff ℝ 1 f →
      boxCollarGradientEnergy f (fun _ ↦ 0) (fun _ ↦ 1) 1 ≤ 1 →
      (∫ y in Icc (fun _ : Fin q ↦ (0 : ℝ)) (fun _ ↦ 1),
        (f (y, 0) - originalDyadicTraceApprox f n y)^2) < ε := by
  have ht : Tendsto (fun n : ℕ ↦ ((q + 2 : ℕ) : ℝ) * ((1 : ℝ) / 2^n))
      atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    simpa only [div_pow, one_pow, mul_zero] using hp.const_mul ((q + 2 : ℕ) : ℝ)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨n, fun f hf henergy ↦ ?_⟩
  apply lt_of_le_of_lt (smooth_originalDyadicTraceApprox_error_sq_le_unit_energy hf n)
  exact lt_of_le_of_lt
    (mul_le_of_le_one_right (by positivity) henergy) hn

end OTSelector.Reconstruction

end
end
