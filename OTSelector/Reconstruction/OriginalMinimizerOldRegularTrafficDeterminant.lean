import OTSelector.Reconstruction.PositiveResidueDeterminant
import OTSelector.LinearAlgebra.Matrix.DeterminantLoewner
import OTSelector.Reconstruction.FocalPoleComplianceLegs

/-! The old-focal determinant loss has the rank of the actual residue.
This keeps zero eigendirections separate before the original endpoint density
is multiplied in; a full-dimension operator-norm estimate would lose this cancellation. -/
open Set Matrix
open scoped BigOperators Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Enlarging only the residue coefficient costs one factor in each nonzero
eigendirection, while the kernel of the same actual residue is unchanged. -/
theorem affineResidue_det_le_rank_mul {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {x y z M : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hM : 1 ≤ M) (hyz : y ≤ M * z) :
    (x • (1 : Matrix ι ι ℝ) + y • G).det ≤
      M ^ G.rank * (x • (1 : Matrix ι ι ℝ) + z • G).det := by
  classical
  let eig := hG.isHermitian.eigenvalues
  let N := {i // eig i ≠ 0}
  let Z := {i // ¬eig i ≠ 0}
  have hsplit (v : ℝ) :
      (∏ i, (x + v * eig i)) =
        x ^ Fintype.card Z * ∏ i : N, (x + v * eig i) := by
    have hzero : (∏ i : Z, (x + v * eig i)) = x ^ Fintype.card Z := by
      have hi : ∀ i : Z, eig i = 0 := fun i ↦ not_ne_iff.mp i.property
      simp [hi]
    have hs := Fintype.prod_subtype_mul_prod_subtype
      (fun i ↦ eig i ≠ 0) (fun i ↦ x + v * eig i)
    rw [← hs, hzero]
    ac_rfl
  have hprod : (∏ i : N, (x + y * eig i)) ≤
      M ^ Fintype.card N * ∏ i : N, (x + z * eig i) := by
    calc
      _ ≤ ∏ i : N, (M * (x + z * eig i)) := by
        apply Finset.prod_le_prod
        · intro i _
          exact add_nonneg hx (mul_nonneg hy (hG.eigenvalues_nonneg i))
        · intro i _
          have he := hG.eigenvalues_nonneg i
          have hmx : x ≤ M * x := le_mul_of_one_le_left hx hM
          have hmy := mul_le_mul_of_nonneg_right hyz he
          nlinarith
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hrank : G.rank = Fintype.card N := hG.isHermitian.rank_eq_card_non_zero_eigs
  rw [det_smul_one_add_smul_of_isHermitian hG.isHermitian,
    det_smul_one_add_smul_of_isHermitian hG.isHermitian, hsplit y, hsplit z, hrank]
  calc
    _ ≤ x ^ Fintype.card Z *
        (M ^ Fintype.card N * ∏ i : N, (x + z * eig i)) :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg hx _)
    _ = _ := by ring

/-- For an old source arbitrarily close to its focal endpoint, the affine
residue model loses only `(2t/a)^rank(G)` in the same genuine focal scale. -/
theorem oldFocal_affineResidue_det_le {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (hat : a ≤ 2*t) :
    (t • (1 : Matrix ι ι ℝ) + a⁻¹ • G).det ≤
      (2*t/a) ^ G.rank * (focalResidueScale G t).det := by
  apply affineResidue_det_le_rank_mul hG ht.le (inv_nonneg.mpr ha.le)
  · exact (le_div_iff₀ ha).mpr (by linarith)
  · have heq : (2*t/a)*t⁻¹ = 2*a⁻¹ := by field_simp
    rw [heq]
    linarith [inv_pos.mpr ha]

/-- The normalized full old compliance leg retains exactly the residue-rank
singularity, even though no uniform upper bound for this leg is possible. -/
theorem oldFocal_normalizedLeg_det_le_rank_power {G U : Matrix ι ι ℝ}
    (hG : G.PosSemidef) (hU : U.PosSemidef) {t a C : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hat : a ≤ 2*t) (hC : 0 ≤ C)
    (hupper : (C • (t • (1 : Matrix ι ι ℝ) + a⁻¹ • G) - U).PosSemidef) :
    let T := positiveMatrixNormalizer (focalResidueScale G t)
    (1 + T * U * Tᵀ).det ≤
      (C+2) ^ Fintype.card ι * (2*t/a) ^ G.rank := by
  let A := focalResidueScale G t
  let B := t • (1 : Matrix ι ι ℝ) + a⁻¹ • G
  let T := positiveMatrixNormalizer A
  have hA : A.PosDef := focalResidueScale_posDef hG ht
  have hT := positiveMatrixNormalizer_spec hA
  have hTA : T*A*Tᵀ=1 := hT.2
  have hcoef : 0 ≤ 2*a⁻¹-t⁻¹ := by
    have h : 1/t ≤ 2/a := (div_le_div_iff₀ ht ha).mpr (by nlinarith)
    simpa only [one_div, div_eq_mul_inv, one_mul] using sub_nonneg.mpr h
  have hBA : (2 • B - A).PosSemidef := by
    have h := (Matrix.PosSemidef.one.smul ht.le).add (hG.smul hcoef)
    convert h using 1
    dsimp [A,B,focalResidueScale]
    module
  have hdiff : ((C+2) • B - (A+U)).PosSemidef := by
    convert hupper.add hBA using 1
    dsimp [B]
    module
  have hdiffT := hdiff.mul_mul_conjTranspose_same T
  have hnormdiff : ((C+2) • (T*B*Tᵀ) - (1+T*U*Tᵀ)).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hTA] using hdiffT
  have hnormU := hU.mul_mul_conjTranspose_same T
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hnormU
  have hdet := OTSelector.Probability.det_mono_of_posDef_of_posSemidef_sub
    (Matrix.PosDef.one.add_posSemidef hnormU) hnormdiff
  have hdetA : T.det*T.det*A.det=1 := by
    have h := congrArg Matrix.det hT.2
    rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at h
    nlinarith [h]
  have hnonneg : 0 ≤ T.det*T.det := mul_self_nonneg _
  have hrank := mul_le_mul_of_nonneg_left (oldFocal_affineResidue_det_le hG ht ha hat) hnonneg
  change T.det*T.det*B.det ≤ _ at hrank
  have hrank' : T.det*T.det*B.det ≤ (2*t/a)^G.rank := by
    calc
      _ ≤ T.det*T.det*((2*t/a)^G.rank*A.det) := hrank
      _ = (2*t/a)^G.rank*(T.det*T.det*A.det) := by ring
      _ = _ := by rw [hdetA,mul_one]
  calc
    _ ≤ ((C+2) • (T*B*Tᵀ)).det := hdet
    _ = (C+2)^Fintype.card ι*(T.det*T.det*B.det) := by
      rw [Matrix.det_smul,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrank' (by positivity)

/-- Integrating the original upper pole comparison preserves its exact
reciprocal-distance coefficient, including sources arbitrarily near zero. -/
theorem intervalIntegral_positivePole_upper
    {W : ℝ→Matrix ι ι ℝ} {G : Matrix ι ι ℝ} {ε C a b : ℝ}
    (ha : 0<a) (hab : a≤b) (hb : b<ε) (hW : ContinuousOn W (Ioo 0 ε))
    (hupper : ∀s∈Ioo 0 ε, (C•((s^2)⁻¹•G+1)-W s).PosSemidef) :
    (C•((a⁻¹-b⁻¹)•G+(b-a)•1)-(∫s in a..b,W s)).PosSemidef := by
  have h := intervalIntegral_positivePole_lower (W:=fun s ↦ -W s)
    (G:=G) (c:= -C) ha hab hb hW.neg (fun s hs ↦ by
      convert hupper s hs using 1
      module)
  rw [intervalIntegral.integral_neg] at h
  convert h using 1
  module

/-- The full old compliance integral has the genuine residue-rank determinant
singularity after normalization at the observed clock scale. -/
theorem oldFocal_compliance_det_le_rank_power
    {W : ℝ→Matrix ι ι ℝ} {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    {ε C t a r : ℝ} (hC : 0≤C) (ht : 0<t) (ha : 0<a)
    (har : a≤r) (hr : r∈Icc t (2*t)) (hrε : r<ε)
    (hW : ContinuousOn W (Ioo 0 ε))
    (hWpos : ∀s∈Ioo 0 ε, (W s).PosSemidef)
    (hupper : ∀s∈Ioo 0 ε, (C•((s^2)⁻¹•G+1)-W s).PosSemidef) :
    let T := positiveMatrixNormalizer (focalResidueScale G t)
    (1 + T * (∫s in a..r,W s) * Tᵀ).det ≤
      (2*C+2) ^ Fintype.card ι * (2*t/a) ^ G.rank := by
  have hI := intervalIntegral_positivePole_upper ha har hrε hW hupper
  have hr0 : 0 < r := ht.trans_le hr.1
  have hcoeffG : 0 ≤ a⁻¹+r⁻¹ := by positivity
  have hcoeffI : 0 ≤ 2*t-r+a := by linarith [hr.2]
  have hmodel := ((hG.smul hcoeffG).add
    (Matrix.PosSemidef.one.smul hcoeffI)).smul hC
  have hbound : ((2*C) • (t • (1 : Matrix ι ι ℝ)+a⁻¹•G) -
      (∫s in a..r,W s)).PosSemidef := by
    convert hmodel.add hI using 1
    module
  have hpos := OTSelector.Geometry.posSemidef_intervalIntegral har
    (fun s hs ↦ hWpos s ⟨ha.trans_le hs.1,hs.2.trans_lt hrε⟩)
  exact oldFocal_normalizedLeg_det_le_rank_power hG hpos ht ha
    (har.trans hr.2) (by positivity) hbound

end OTSelector.Reconstruction
