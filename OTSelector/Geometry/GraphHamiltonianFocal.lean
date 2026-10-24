import OTSelector.Geometry.FinslerCompleteGraphFocal

/-!
# Focal structure of a smooth strictly convex graph Hamiltonian

The actual parameter derivative of a jointly C2 Hamiltonian solution family satisfies
square Jacobi equations in matching bases. A positive vertical Lagrangian Hessian,
canonical isotropy and full phase rank give regular focal crossing, exact smooth inverse
poles and two-sided determinant and inverse-norm bounds. All statements use the original
Lagrangian and the same actual Legendre branch, independently of a manifold model.
-/

open Set Filter Matrix Module
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {W V ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual graph phase parameter derivative has square Jacobi matrices in matching
parameter and spatial bases. Their joint kernel is trivial and their Wronskian vanishes;
the positive matrix C is the basis representation of the genuine inverse graph Hessian. -/
theorem graphHamiltonian_parameter_matrices (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {L : (ℝ × V) × V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    (hpos : ∀ z ∈ g.source, ∀ w : V, w ≠ 0 → 0 < GraphLegendre.verticalHessian L z w w)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field L g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target)
    (hinj : Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    let P := fun s ↦ covectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).2)
    let A := hamiltonianMatrixA bV (GraphHamiltonian.blockA L g t (Ψ (w₀, t)))
    let B := hamiltonianMatrixB bV (GraphHamiltonian.blockB L g t (Ψ (w₀, t)))
    let C := hamiltonianMatrixC bV (GraphHamiltonian.blockC L g t (Ψ (w₀, t)))
    HasDerivAt J (B * J t + C * P t) t ∧
      HasDerivAt P (-A * J t - Bᵀ * P t) t ∧ Aᵀ = A ∧ Cᵀ = C ∧ C.PosDef ∧
      (J t)ᵀ * P t = (P t)ᵀ * J t ∧
      (∀ u : ι → ℝ, J t *ᵥ u = 0 → P t *ᵥ u = 0 → u = 0) ∧
      C = hamiltonianMatrixC bV (ContinuousLinearMap.inverse
        (GraphLegendre.verticalHessian L (g.symm ((t, (Ψ (w₀, t)).1),
          (Ψ (w₀, t)).2)))) := by
  have hv (ξ : W) :=
    hasDerivAt_graphHamiltonian_parameterVariation hg hL hG hD hΨ hODE hz hp ξ
  have hm := hasDerivWithinAt_hamiltonian_family_matrices (I := univ) (t := t) bV
    (J := fun j s ↦ (fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ (bW j)).1)
    (P := fun j s ↦ (fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ (bW j)).2)
    (A := GraphHamiltonian.blockA L g t (Ψ (w₀, t)))
    (B := GraphHamiltonian.blockB L g t (Ψ (w₀, t)))
    (C := GraphHamiltonian.blockC L g t (Ψ (w₀, t)))
    (fun j ↦ (hv (bW j)).1.hasDerivWithinAt)
    (fun j ↦ (hv (bW j)).2.hasDerivWithinAt)
  have hpositive := hpos _ (g.map_target hp)
  have hA := GraphHamiltonian.blockA_symm hg hL hG hp
  have hC := GraphHamiltonian.blockC_symm hg hL hG hp
  have hCpos := fun q hq ↦ GraphHamiltonian.blockC_pos hg hL hG hp hpositive (q := q) hq
  refine ⟨hm.1.hasDerivAt (by simp), hm.2.hasDerivAt (by simp),
    hamiltonianMatrixA_transpose bV hA,
    hamiltonianMatrixC_transpose bV hC,
    hamiltonianMatrixC_posDef bV hC hCpos, ?_,
    fun u hJ hP ↦ phase_matrices_joint_kernel bW bV hinj u hJ hP, ?_⟩
  · apply sub_eq_zero.mp
    ext i j
    rw [matrix_wronskian_apply]
    exact hpair (bW i) (bW j)
  · exact congrArg (hamiltonianMatrixC bV)
      (GraphHamiltonian.blockC_eq_inverse hg hL hG hp hpositive)

/-- At each actual singular graph variation, the crossing is bijective and the
local determinant and inverse have the prescribed rates on both sides. -/
theorem graphHamiltonian_regular_focal_bounds (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {L : (ℝ × V) × V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    (hpos : ∀ z ∈ g.source, ∀ w : V, w ≠ 0 → 0 < GraphLegendre.verticalHessian L z w w)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field L g z.2 (Ψ z)) z.2)
    {w₀ : W} {t : ℝ} (hz : (w₀, t) ∈ D)
    (hp : ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target)
    (hinj : Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀
    let J := fun s ↦ vectorFamilyMatrix bV (fun j ↦ (Z s (bW j)).1)
    Function.Bijective (focalCrossingMap (J t) (deriv J t)) ∧
      (0 < Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) →
        ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ∃ cdet Cdet cinv Cinv : ℝ,
          0 < cdet ∧ 0 < Cdet ∧ 0 < cinv ∧ 0 < Cinv ∧
          ∀ᶠ s in 𝓝[>] (0 : ℝ),
            cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ≤
                |(J (t + ε * s)).det| ∧
              |(J (t + ε * s)).det| ≤
                Cdet * |s| ^ Module.finrank ℝ (LinearMap.ker (J t).mulVecLin) ∧
              cinv / |s| ≤ ‖(J (t + ε * s))⁻¹‖ ∧
              ‖(J (t + ε * s))⁻¹‖ ≤ Cinv / |s|) := by
  dsimp only
  obtain ⟨hJ, _, _, _, hC, hW, hphase, _⟩ :=
    graphHamiltonian_parameter_matrices bW bV hg hL hG hpos hD hΨ hODE hz hp hinj hpair
  constructor
  · convert focalCrossingMap_bijective
      (B := hamiltonianMatrixB bV
        (GraphHamiltonian.blockB L g t (Ψ (w₀, t))))
      hW hphase hC using 1
    congr 1
    exact congrArg (focalCrossingMap _) hJ.deriv
  · intro hk ε hε
    rcases hε with rfl | rfl
    · simpa only [one_mul] using
        regular_focal_bounds_left_endpoint hJ.hasDerivWithinAt
          (fun u hu hr ↦ focal_crossing_kernel_eq_zero hW hphase hC hu hr) hk
    · simpa only [neg_mul, one_mul, sub_eq_add_neg] using
        regular_focal_bounds_right_endpoint hJ.hasDerivWithinAt
          (fun u hu hr ↦ focal_crossing_kernel_eq_zero hW hphase hC hu hr) hk

/-- The actual graph position variation has an exact inverse pole near the selected time.
The residue rank is the actual kernel dimension, and all punctured nearby matrices are
invertible. Smoothness and regular crossing follow from the original C2 family and ODE. -/
theorem graphHamiltonian_exists_smooth_inverse_pole (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {L : (ℝ × V) × V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    (hpos : ∀ z ∈ g.source, ∀ w : V, w ≠ 0 → 0 < GraphLegendre.verticalHessian L z w w)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field L g z.2 (Ψ z)) z.2)
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
  have hs := contDiffOn_graphHamiltonianFamily_slice hL hG hD hΨ hODE w₀ hp
  have hJ : ContDiffOn ℝ ∞ J {s | (w₀, s) ∈ D} :=
    (contDiffOn_phase_matrices bW bV hs.2).1
  have hU : IsOpen {s | (w₀, t + s) ∈ D} :=
    hD.preimage (continuous_const.prodMk (continuous_const.add continuous_id))
  have hzero : (0 : ℝ) ∈ {s | (w₀, t + s) ∈ D} := by simpa using hz
  have hJs : ContDiffOn ℝ ∞ (fun s ↦ J (t + s)) {s | (w₀, t + s) ∈ D} :=
    hJ.comp (contDiffOn_const.add contDiffOn_id) (fun _ hs ↦ hs)
  obtain ⟨hdJ, _, _, _, hC, hW, hphase, _⟩ :=
    graphHamiltonian_parameter_matrices bW bV hg hL hG hpos hD hΨ hODE hz
      (hp t hz) hinj hpair
  have hdval : deriv J t =
      hamiltonianMatrixB bV (GraphHamiltonian.blockB L g t
        (Ψ (w₀, t))) * J t +
      hamiltonianMatrixC bV (GraphHamiltonian.blockC L g t
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

/-- Each central slice has the focal expansion of the same actual solution family.
The only phase conditions are full parameter rank and canonical zero pairing. -/
theorem hasGraphFocalExpansion_of_graphHamiltonian
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {L : (ℝ × V) × V → ℝ}
    {g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hg : (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L g.source) (hG : ContDiffOn ℝ ∞ g.symm g.target)
    (hpos : ∀ z ∈ g.source, ∀ w : V, w ≠ 0 → 0 < GraphLegendre.verticalHessian L z w w)
    {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hODE : ∀ z ∈ D, HasDerivAt (fun s ↦ Ψ (z.1, s))
      (GraphHamiltonian.field L g z.2 (Ψ z)) z.2)
    {w₀ : W}
    (hp : ∀ t, (w₀, t) ∈ D → ((t, (Ψ (w₀, t)).1), (Ψ (w₀, t)).2) ∈ g.target)
    (hinj : ∀ t, (w₀, t) ∈ D →
      Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀))
    (hpair : ∀ t, (w₀, t) ∈ D → ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ Ψ (w, t)) w₀ v) = 0) :
    HasGraphFocalExpansion bW bV Ψ D w₀ := by
  intro t ht
  have hcross := graphHamiltonian_regular_focal_bounds bW bV hg hL hG hpos
    hD hΨ hODE ht (hp t ht) (hinj t ht) (hpair t ht)
  have hpole := graphHamiltonian_exists_smooth_inverse_pole bW bV hg hL hG hpos
    hD hΨ hODE ht hp (hinj t ht) (hpair t ht)
  exact ⟨hcross.1, hpole, hcross.2⟩

end OTSelector.Geometry
