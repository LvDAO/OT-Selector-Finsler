import OTSelector.Analysis.ODE.Flow.GraphVariationSmooth
import OTSelector.Analysis.ODE.Hamiltonian.GraphJacobiMatrix
import OTSelector.Geometry.FocalSmoothPole

/-!
# Smooth inverse poles of the actual graph position variation

The original jointly C2 graph solution family gives a parameter differential smooth in
time. Its basis matrices satisfy the actual graph Hamiltonian equations. At a center
with injective phase differential and canonical zero pairing, the positive original graph
Hessian gives the regular crossing condition. Thus the actual position matrix has an exact
simple inverse pole with smooth remainder and residue rank equal to its kernel dimension.
Neither position-matrix smoothness nor a crossing condition is supplied as a hypothesis.
-/

open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι]

/-- Fixed finite bases preserve the smoothness of both blocks of a phase differential. -/
theorem contDiffOn_phase_matrices (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {Z : ℝ → W →L[ℝ] (V × (V →L[ℝ] ℝ))} {I : Set ℝ}
    (hZ : ContDiffOn ℝ ∞ Z I) :
    ContDiffOn ℝ ∞ (fun t ↦ vectorFamilyMatrix bV (fun j ↦ (Z t (bW j)).1)) I ∧
      ContDiffOn ℝ ∞ (fun t ↦ covectorFamilyMatrix bV (fun j ↦ (Z t (bW j)).2)) I := by
  have : FiniteDimensional ℝ W := bW.finiteDimensional_of_finite
  let A : (W →L[ℝ] (V × (V →L[ℝ] ℝ))) →ₗ[ℝ]
      (Matrix ι ι ℝ × Matrix ι ι ℝ) :=
    { toFun := fun z ↦ (vectorFamilyMatrix bV (fun j ↦ (z (bW j)).1),
        covectorFamilyMatrix bV (fun j ↦ (z (bW j)).2))
      map_add' := by
        intro z z'
        ext i j <;> simp [vectorFamilyMatrix, covectorFamilyMatrix]
      map_smul' := by
        intro r z
        ext i j <;> simp [vectorFamilyMatrix, covectorFamilyMatrix] }
  have h := A.toContinuousLinearMap.contDiff.comp_contDiffOn hZ
  exact ⟨h.fst, h.snd⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- The actual graph position variation has an exact inverse pole near the selected time.
The residue rank is the actual kernel dimension, and all punctured nearby matrices are
invertible. Smoothness and regular crossing follow from the original C2 family and ODE. -/
theorem chartGraph_exists_smooth_inverse_pole (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.chartGraphLagrangian x₀))
    (hsub : g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ g.symm g.target)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field (F.chartGraphLagrangian x₀) g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ∀ s, (w₀, s) ∈ D → ((s, (Ψ (w₀, s)).1), (Ψ (w₀, s)).2) ∈ g.target)
    (hinj : Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    ∃ (U : Set ℝ) (R : Matrix ι ι ℝ) (B : ℝ → Matrix ι ι ℝ),
      IsOpen U ∧ 0 ∈ U ∧ U ⊆ {s | (w₀, t + s) ∈ D} ∧ ContDiffOn ℝ ∞ B U ∧
      (∀ s ∈ U, s ≠ 0 → (J (t + s)).det ≠ 0 ∧
        (J (t + s))⁻¹ = s⁻¹ • R + B s) ∧
      R.rank = Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ∧
      (0 < Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) → R ≠ 0) := by
  have : FiniteDimensional ℝ W := bW.finiteDimensional_of_finite
  let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
  let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
  have hs := hF.chartGraph_family_contDiffOn_slice x₀ hsub hG hD hΨ hODE w₀ hp
  have hJ : ContDiffOn ℝ ∞ J {s | (w₀, s) ∈ D} :=
    (contDiffOn_phase_matrices bW bV hs.2).1
  have hU : IsOpen {s | (w₀, t + s) ∈ D} :=
    hD.preimage (continuous_const.prodMk (continuous_const.add continuous_id))
  have hzero : (0 : ℝ) ∈ {s | (w₀, t + s) ∈ D} := by simpa using hz
  have hJs : ContDiffOn ℝ ∞ (fun s ↦ J (t + s)) {s | (w₀, t + s) ∈ D} :=
    hJ.comp (contDiffOn_const.add contDiffOn_id) (fun _ hs ↦ hs)
  obtain ⟨hdJ, _, _, _, hC, hW, hphase, _⟩ :=
    hF.chartGraph_parameter_matrices x₀ bW bV hg hsub hG hD hΨ hODE hz
      (hp t hz) hinj hpair
  have hdval : deriv J t =
      hamiltonianMatrixB bV (GraphHamiltonian.blockB (F.chartGraphLagrangian x₀) g t
        (Ψ (w₀, t))) * J t +
      hamiltonianMatrixC bV (GraphHamiltonian.blockC (F.chartGraphLagrangian x₀) g t
        (Ψ (w₀, t))) * covectorFamilyMatrix bV (fun j ↦ (Z t (bW j)).2) := by
    simpa only [J, Z] using! hdJ.deriv
  have hdJ' : HasDerivAt J (deriv J t) (t + (0 : ℝ)) := by
    simpa only [add_zero] using! hdJ.differentiableAt.hasDerivAt
  have hshift := hdJ'.scomp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add t)
  simp only [one_smul] at hshift
  have hcross : ∀ u, J (t + 0) *ᵥ u = 0 →
      deriv (fun s ↦ J (t + s)) 0 *ᵥ u ∈ LinearMap.range (J (t + 0)).mulVecLin →
      u = 0 := by
    intro u hu hr
    have hshift_eq : deriv (fun s ↦ J (t + s)) 0 = deriv J t := by
      simpa only [Function.comp_def] using! hshift.deriv
    rw [hshift_eq, hdval] at hr
    exact focal_crossing_kernel_eq_zero hW hphase hC (by simpa using hu)
      (by simpa using hr)
  obtain ⟨U, R, B, hU', h0, hsub', hB, hpole, hrank, hR⟩ :=
    exists_smooth_focal_inverse_pole hU hzero hJs hcross
  change R.rank = Module.finrank ℝ (LinearMap.ker (J (t + 0)).mulVecLin) at hrank
  change (0 < Module.finrank ℝ (LinearMap.ker (J (t + 0)).mulVecLin) → R ≠ 0) at hR
  rw [add_zero] at hrank hR
  exact ⟨U, R, B, hU', h0, hsub', hB, hpole, hrank, hR⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry
