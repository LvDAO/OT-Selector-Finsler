import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import OTSelector.Analysis.Calculus.OrthonormalBoxGaussGreen
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalOrthonormalPhysicalCubeEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalOrthonormalPhysicalCubeEnergy`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual orthonormal frame in finite-dimensional Euclidean space and the stated box/readout regularity.

Objects: Measure-preserving physical cube coordinates and exact invariance of summed derivative L2 energy.

Proof detail: Use orthogonality for determinant absolute value one and Parseval for the covector components, then change variables in the actual integral.

Sources: D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Terence Tao, Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57).
Relation: Orthogonal coordinate/energy adapter. The totalized normed-target integral statements do not add an unstated completeness hypothesis.
-/

/-! Actual physical orthogonal cubes preserve Lebesgue volume and original derivative energy. -/
open Set Function MeasureTheory
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The actual raw physical rotation from the chosen orthonormal basis coordinates. -/
def orthonormalPhysicalCubeMap {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    (Fin q → ℝ) ≃L[ℝ] (Fin q → ℝ) :=
  (orthonormalCubeCoordinates b).symm.trans (EuclideanSpace.equiv (Fin q) ℝ)

/-- Each raw coordinate direction is sent to the actual chosen physical basis direction. -/
theorem orthonormalPhysicalCubeMap_single {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (i : Fin q) :
    orthonormalPhysicalCubeMap b (Pi.single i 1) = EuclideanSpace.equiv (Fin q) ℝ (b i) := by
  change EuclideanSpace.equiv (Fin q) ℝ
    ((orthonormalCubeCoordinates b).symm (Pi.single i 1)) = _
  rw [orthonormalCubeCoordinates_symm_single]

/-- Real Haar volume is preserved by the actual orthonormal coordinate rotation. -/
theorem measurePreserving_orthonormalPhysicalCubeMap {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) :
    MeasurePreserving (orthonormalPhysicalCubeMap b) := by
  exact (PiLp.volume_preserving_ofLp (Fin q)).comp
    (b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin q)))

/-- The physical orthogonal box is the literal image of the raw closed coordinate box. -/
def orthonormalPhysicalCubeRegion {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (a c : Fin q → ℝ) : Set (Fin q → ℝ) := orthonormalPhysicalCubeMap b '' Icc a c

/-- Genuine image-box change of variables, for any scalar or Bochner-valued integrand. -/
theorem integral_orthonormalPhysicalCubeRegion {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (a c : Fin q → ℝ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (Fin q → ℝ) → F) :
    (∫ z in orthonormalPhysicalCubeRegion b a c, g z) =
      ∫ y in Icc a c, g (orthonormalPhysicalCubeMap b y) :=
  (measurePreserving_orthonormalPhysicalCubeMap b).setIntegral_image_emb
    (orthonormalPhysicalCubeMap b).toHomeomorph.measurableEmbedding g (Icc a c)

/-- Parseval for the original raw physical covector evaluated in the actual chosen frame. -/
theorem sum_sq_orthonormalPhysicalCubeMap_covector {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (L : (Fin q → ℝ) →L[ℝ] ℝ) :
    (∑ i : Fin q, (L (orthonormalPhysicalCubeMap b (Pi.single i 1)))^2) =
      ∑ k : Fin q, (L (Pi.single k 1))^2 := by
  let M := L.comp (EuclideanSpace.equiv (Fin q) ℝ).toContinuousLinearMap
  calc
    _ = ∑ i : Fin q, (M (b i))^2 := by
      simp only [orthonormalPhysicalCubeMap_single]
      rfl
    _ = ‖M‖^2 := (b.norm_dual M).symm
    _ = _ := by
      rw [(EuclideanSpace.basisFun (Fin q) ℝ).norm_dual M]
      simp only [EuclideanSpace.basisFun_apply]
      rfl

/-- The actual chain rule and Parseval preserve the complete original partial-gradient sum. -/
theorem sum_sq_fderiv_comp_orthonormalPhysicalCubeMap {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {φ : (Fin q → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (y : Fin q → ℝ) :
    (∑ i : Fin q, (fderiv ℝ (φ ∘ orthonormalPhysicalCubeMap b) y (Pi.single i 1))^2) =
      ∑ k : Fin q, (fderiv ℝ φ (orthonormalPhysicalCubeMap b y) (Pi.single k 1))^2 := by
  have hd := (hφ.differentiable one_ne_zero (orthonormalPhysicalCubeMap b y)).hasFDerivAt.comp y
    (orthonormalPhysicalCubeMap b).hasFDerivAt
  rw [hd.fderiv]
  exact sum_sq_orthonormalPhysicalCubeMap_covector b _

/-- Literal coordinate-box derivative energy equals the original physical derivative energy
on its actual orthogonal image box. No Jacobian or energy identity is an assumption. -/
theorem sum_integral_sq_fderiv_comp_orthonormalPhysicalCubeMap {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (a c : Fin q → ℝ) {φ : (Fin q → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∑ i : Fin q, ∫ y in Icc a c,
      (fderiv ℝ (φ ∘ orthonormalPhysicalCubeMap b) y (Pi.single i 1))^2) =
      ∑ k : Fin q, ∫ z in orthonormalPhysicalCubeRegion b a c,
        (fderiv ℝ φ z (Pi.single k 1))^2 := by
  have hcomp : ContDiff ℝ 1 (φ ∘ orthonormalPhysicalCubeMap b) :=
    hφ.comp (orthonormalPhysicalCubeMap b).contDiff
  have hi (i : Fin q) : IntegrableOn
      (fun y ↦ (fderiv ℝ (φ ∘ orthonormalPhysicalCubeMap b) y (Pi.single i 1))^2) (Icc a c) :=
    ((((hcomp.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).continuousOn).integrableOn_Icc
  have hj (k : Fin q) : IntegrableOn
      (fun y ↦ (fderiv ℝ φ (orthonormalPhysicalCubeMap b y) (Pi.single k 1))^2) (Icc a c) :=
    (((((hφ.continuous_fderiv (by norm_num)).comp
      (orthonormalPhysicalCubeMap b).continuous).clm_apply continuous_const).pow 2).continuousOn).integrableOn_Icc
  calc
    _ = ∫ y in Icc a c, ∑ i : Fin q,
        (fderiv ℝ (φ ∘ orthonormalPhysicalCubeMap b) y (Pi.single i 1))^2 :=
      (integral_finsetSum Finset.univ (fun i _ ↦ hi i)).symm
    _ = ∫ y in Icc a c, ∑ k : Fin q,
        (fderiv ℝ φ (orthonormalPhysicalCubeMap b y) (Pi.single k 1))^2 := by
      apply integral_congr_ae
      exact ae_of_all _ (sum_sq_fderiv_comp_orthonormalPhysicalCubeMap b hφ)
    _ = ∑ k : Fin q, ∫ y in Icc a c,
        (fderiv ℝ φ (orthonormalPhysicalCubeMap b y) (Pi.single k 1))^2 :=
      integral_finsetSum Finset.univ (fun k _ ↦ hj k)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact (integral_orthonormalPhysicalCubeRegion b a c
        (fun z ↦ (fderiv ℝ φ z (Pi.single k 1))^2)).symm

end OTSelector.Reconstruction

end
end
