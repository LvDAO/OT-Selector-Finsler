import OTSelector.Reconstruction.OriginalKernelUniformLower
import OTSelector.LinearAlgebra.Matrix.PositiveLegInverseQuadratic

/-!
# Positive pole plus a bounded remainder gives a genuine geometric comparison

A true positive mobility lower bound and its exact fixed positive double-pole residue
control both sides of the mobility by the same `I+s⁻²G`. No common eigenspace assumption
is used, and the actual smooth remainder may fail to commute with its residue.
-/

open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Uniform positivity and a bounded two-sided remainder internally give comparison with
the genuine positive pole plus identity, even for noncommuting remainder matrices. -/
theorem exists_positive_matrix_remainder_comparison_constants
    {κ M : ℝ} (hκ : 0<κ) (hM : 0<M) :
    ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧ ∀ (W P R : Matrix ι ι ℝ),
      P.PosSemidef → (W-κ•1).PosSemidef → (M•1-R).PosSemidef → (M•1+R).PosSemidef →
      W=P+R → (W-c•(P+1)).PosSemidef ∧ (C•(P+1)-W).PosSemidef := by
  let θ := κ/(2*(κ+M))
  have hθ : 0<θ := by dsimp [θ]; positivity
  have hθ1 : θ≤1 := by
    apply (div_le_one (by positivity : 0<2*(κ+M))).mpr
    linarith
  have hθsum : θ*(M+κ)=κ/2 := by dsimp [θ]; field_simp; ring
  let c := min θ (κ/2)
  let C := max 1 M
  have hc : 0<c := lt_min hθ (half_pos hκ)
  have hC : 0<C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨c,hc,C,hC,fun W P R hP hW hRu hRl heq ↦ ?_⟩
  constructor
  · have hsum := ((hRl.smul hθ.le).add (hW.smul (sub_nonneg.mpr hθ1))).add
      ((hP.smul (show 0≤θ-c from sub_nonneg.mpr (min_le_left θ (κ/2)))).add
        (Matrix.PosSemidef.one.smul (show 0≤κ/2-c from sub_nonneg.mpr (min_le_right θ (κ/2)))))
    have hid : θ•(M•1+R)+(1-θ)•(W-κ•1)+((θ-c)•P+(κ/2-c)•1) = W-c•(P+1) := by
      calc
        _ = W-c•P+(θ*(M+κ)-κ/2-c)•1 := by rw [heq]; module
        _ = W-c•(P+1) := by rw [hθsum]; module
    rwa [hid] at hsum
  · have hsum := (hRu.add (hP.smul (show 0≤C-1 from sub_nonneg.mpr (le_max_left 1 M)))).add
      (Matrix.PosSemidef.one.smul (show 0≤C-M from sub_nonneg.mpr (le_max_right 1 M)))
    convert hsum using 1
    rw [heq]
    module

/-- Every continuous compact matrix remainder has a scalar identity bound on both sides
at its Hermitian points, internally produced from its unchanged compact quadratic bound. -/
theorem exists_compact_remainder_scalar_bounds
    {R : ℝ→Matrix ι ι ℝ} {J : Set ℝ} (hJ : IsCompact J) (hR : ContinuousOn R J) :
    ∃ M : ℝ, M>0 ∧ ∀t∈J, (R t).IsHermitian →
      (M•1-R t).PosSemidef ∧ (M•1+R t).PosSemidef := by
  obtain ⟨C,hC,hbound⟩ := exists_compact_matrixQuadratic_sum_bound hJ hR
  let M := 2*C+1
  have hM : 0<M := by dsimp [M]; linarith
  refine ⟨M,hM,fun t ht hHerm ↦ ?_⟩
  have hquad (v : ι→ℝ) : v⬝ᵥ(R t*ᵥv)≤M*∑i,v i^2 := by
    have h := (le_abs_self (matrixQuadratic (R t) v)).trans (hbound t ht v)
    have hs := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) ↦ sq_nonneg (v i))
    dsimp only [matrixQuadratic] at h
    dsimp only [M]
    nlinarith
  have hquadNeg (v : ι→ℝ) : v⬝ᵥ((-R t)*ᵥv)≤M*∑i,v i^2 := by
    have h := (neg_le_abs (matrixQuadratic (R t) v)).trans (hbound t ht v)
    have hs := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) ↦ sq_nonneg (v i))
    simp only [Matrix.neg_mulVec,dotProduct_neg]
    dsimp only [matrixQuadratic] at h
    dsimp only [M]
    nlinarith
  exact ⟨posSemidef_scalar_identity_sub_of_quadratic_upper hM hHerm hquad,
    by simpa only [sub_neg_eq_add] using
      posSemidef_scalar_identity_sub_of_quadratic_upper hM hHerm.neg hquadNeg⟩

end OTSelector.Reconstruction
