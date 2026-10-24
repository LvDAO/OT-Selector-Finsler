import OTSelector.Analysis.Calculus.SecondJetPolynomial
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.NormedSpace.CovectorSplitting
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ParameterizedSecondJetLevel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ParameterizedSecondJetLevel`; the selected original proof blocks follow. -/
section

/-!
Conditions: Independent value, covector and bilinear jet parameters, a nonzero transverse coordinate derivative and the stated smooth polynomial model.

Objects: A parameter-preserving level-coordinate inverse and product chart.

Proof detail: Build the explicit quadratic polynomial in the state coordinate and apply the block implicit/inverse function theorem retaining every jet parameter.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Jiří Lebl, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57 (https://www.jirka.org/ra/realanal2.pdf#page=51); Hassler Whitney, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2).
Relation: Locally constructed jet-parameter chart. Symmetry of the bilinear parameter is not added when the signature does not require it.
-/

/-!
# Joint level coordinates for explicit second-jet polynomials

The independent value, covector and bilinear coefficients form one parameter space.
The actual polynomial level-coordinate map preserves these parameters and has an
invertible vertical derivative at its reference center, without symmetry of the
bilinear coefficient. Its constructed local inverse is smooth on its whole target.
-/

open Set
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

/-- A center, scalar value, covector and bilinear coefficient in a fixed model space. -/
abbrev ScalarSecondJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ)

/-- The actual explicit polynomial associated to the independent second-jet parameters. -/
def scalarSecondJetPolynomial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (j : ScalarSecondJet E) : E → ℝ :=
  secondJetPolynomial j.1 j.2.1 j.2.2.1 j.2.2.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit polynomial is jointly smooth in its independent jet and spatial arguments. -/
theorem contDiff_scalarSecondJetPolynomial_joint :
    ContDiff ℝ ∞ (fun q : ScalarSecondJet E × E ↦
      scalarSecondJetPolynomial q.1 q.2) := by
  have hs : ContDiff ℝ ∞ (fun q : ScalarSecondJet E × E ↦ q.2 - q.1.1) :=
    contDiff_snd.sub contDiff_fst.fst
  have hp : ContDiff ℝ ∞ (fun q : ScalarSecondJet E × E ↦ q.1.2.2.1) :=
    contDiff_fst.snd.snd.fst
  have hB : ContDiff ℝ ∞ (fun q : ScalarSecondJet E × E ↦ q.1.2.2.2) :=
    contDiff_fst.snd.snd.snd
  exact (contDiff_fst.snd.fst.add (hp.clm_apply hs)).add
    (contDiff_const.mul ((hB.clm_apply hs).clm_apply hs))

/-- At its own center the polynomial has the supplied covector, without bilinear symmetry. -/
theorem hasFDerivAt_scalarSecondJetPolynomial_center (j : ScalarSecondJet E) :
    HasFDerivAt (scalarSecondJetPolynomial j) j.2.2.1 j.1 := by
  have hs := (hasFDerivAt_id (𝕜 := ℝ) j.1).sub_const j.1
  have hquad := ((j.2.2.2.hasFDerivAt.comp j.1 hs).clm_apply hs).const_mul (1 / 2 : ℝ)
  have h := ((j.2.2.1.hasFDerivAt.comp j.1 hs).const_add j.2.1).add hquad
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro w
  simp

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The explicit polynomial level map has a jointly smooth, parameter-preserving local
inverse on a fixed reference covector kernel. No symmetry of the bilinear parameter
and no preexisting family of level charts are required. -/
theorem exists_smooth_secondJet_levelCoordinates
    (j₀ : ScalarSecondJet E) (v₀ : E) (hv₀ : j₀.2.2.1 v₀ ≠ 0) :
    let p₀ := j₀.2.2.1
    let π₀ : E →L[ℝ] p₀.ker :=
      (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
        (covectorSplitting p₀ v₀ hv₀).symm.toContinuousLinearMap
    let Φ : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ) :=
      fun q ↦ (q.1, (π₀ (q.2 - q.1.1),
        (scalarSecondJetPolynomial q.1 q.2 - q.1.2.1) / p₀ v₀))
    ∃ e : OpenPartialHomeomorph
        (ScalarSecondJet E × E) (ScalarSecondJet E × (p₀.ker × ℝ)),
      (e : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ)) = Φ ∧
      (j₀, j₀.1) ∈ e.source ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ q ∈ e.target, (e.symm q).1 = q.1 := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let p₀ := j₀.2.2.1
  let levelJetGroup : AddCommGroup (ScalarSecondJet E) :=
    (inferInstance : NormedAddCommGroup (ScalarSecondJet E)).toAddCommGroup
  let levelJetModule : Module ℝ (ScalarSecondJet E) :=
    (inferInstance : NormedSpace ℝ (ScalarSecondJet E)).toModule
  let S := covectorSplitting p₀ v₀ hv₀
  let π₀ : E →L[ℝ] p₀.ker :=
    (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp S.symm.toContinuousLinearMap
  let ψ : ScalarSecondJet E × E → p₀.ker × ℝ := fun q ↦
    (π₀ (q.2 - q.1.1), (scalarSecondJetPolynomial q.1 q.2 - q.1.2.1) / p₀ v₀)
  let Φ : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ) := fun q ↦ (q.1, ψ q)
  change ∃ e : OpenPartialHomeomorph (ScalarSecondJet E × E) (ScalarSecondJet E × (p₀.ker × ℝ)),
    (e : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ)) = Φ ∧ (j₀, j₀.1) ∈ e.source ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ q ∈ e.target, (e.symm q).1 = q.1
  have hψ : ContDiff ℝ ∞ ψ :=
    (π₀.contDiff.comp (contDiff_snd.sub contDiff_fst.fst)).prodMk
      ((contDiff_scalarSecondJetPolynomial_joint.sub contDiff_fst.snd.fst).div_const
        (p₀ v₀))
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_fst.prodMk hψ
  obtain ⟨K, hψD⟩ := hψ.contDiffAt.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hproj : HasFDerivAt (fun y ↦ π₀ (y - j₀.1)) π₀ j₀.1 := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using!
      π₀.hasFDerivAt.comp j₀.1
      ((hasFDerivAt_id (𝕜 := ℝ) j₀.1).sub_const j₀.1)
  have hscalar : HasFDerivAt
      (fun y ↦ (scalarSecondJetPolynomial j₀ y - j₀.2.1) / p₀ v₀)
      ((p₀ v₀)⁻¹ • p₀) j₀.1 := by
    have hs :=
      ((hasFDerivAt_scalarSecondJetPolynomial_center j₀).sub_const j₀.2.1).const_smul
        (p₀ v₀)⁻¹
    convert! hs using 1
    ext y
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hsplit : π₀.prod ((p₀ v₀)⁻¹ • p₀) = S.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext
    · rfl
    · simp [S, div_eq_mul_inv, mul_comm]
  have hfixed : HasFDerivAt (fun y ↦ ψ (j₀, y)) S.symm.toContinuousLinearMap j₀.1 := by
    rw [← hsplit]
    exact hproj.prodMk hscalar
  have hchain := HasFDerivAt.comp (𝕜 := ℝ) (E := E)
    (F := ScalarSecondJet E × E) (G := p₀.ker × ℝ) j₀.1 hψD
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) j₀ j₀.1)
  have hK : ∀ w, K (0, w) = S.symm w := by
    have heq : K.comp (ContinuousLinearMap.inr ℝ (ScalarSecondJet E) E) =
        S.symm.toContinuousLinearMap :=
      hchain.fderiv.symm.trans hfixed.fderiv
    intro w
    exact DFunLike.congr_fun heq w
  let D : (ScalarSecondJet E × E) →L[ℝ] (ScalarSecondJet E × (p₀.ker × ℝ)) :=
    (ContinuousLinearMap.fst ℝ (ScalarSecondJet E) E).prod K
  have hD : HasFDerivAt Φ D (j₀, j₀.1) :=
    HasFDerivAt.prodMk (𝕜 := ℝ) (E := ScalarSecondJet E × E)
      (F := ScalarSecondJet E) (G := p₀.ker × ℝ)
      (hasFDerivAt_fst (𝕜 := ℝ) (E := ScalarSecondJet E) (F := E)) hψD
  have hbij : Function.Bijective D :=
    base_preserving_block_bijective (B := ScalarSecondJet E) (E := E)
      (V := p₀.ker × ℝ) K S.symm hK
  let d := (LinearEquiv.ofBijective D.toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt Φ d.toContinuousLinearMap (j₀, j₀.1) := hD
  let e₀ := hΦ.contDiffAt.toOpenPartialHomeomorph Φ hd (by simp)
  let V := (fderiv ℝ Φ) ⁻¹'
    range ((↑) : ((ScalarSecondJet E × E) ≃L[ℝ] (ScalarSecondJet E × (p₀.ker × ℝ))) →
      (ScalarSecondJet E × E) →L[ℝ] (ScalarSecondJet E × (p₀.ker × ℝ)))
  have hV : IsOpen V :=
    ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv (by simp))
  have hzV : (j₀, j₀.1) ∈ V := ⟨d, hd.fderiv.symm⟩
  let e := e₀.restrOpen V hV
  have he : (e : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ)) = Φ := rfl
  have hzsource : (j₀, j₀.1) ∈ e.source :=
    ⟨hΦ.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp), hzV⟩
  refine ⟨e, he, hzsource, hΦ.contDiffOn, ?_, ?_⟩
  · apply e.open_target.contDiffOn_iff.mpr
    intro q hq
    have hx := e.map_target hq
    obtain ⟨A, hA⟩ := hx.2
    have hdq : HasFDerivAt e A.toContinuousLinearMap (e.symm q) := by
      rw [he, hA]
      exact (hΦ.contDiffAt.differentiableAt (by simp)).hasFDerivAt
    exact e.contDiffAt_symm hq hdq (by rw [he]; exact hΦ.contDiffAt)
  · intro q hq
    have h := congrArg Prod.fst (e.right_inv hq)
    change (Φ (e.symm q)).1 = q.1 at h
    exact h

end FiniteDimensional

/-- A single product neighborhood gives genuine level sections of the same joint inverse.
Each section retains the exact level image with its chosen transverse-domain restriction. -/
theorem exists_smooth_secondJet_levelChart_product
    (j₀ : ScalarSecondJet E) (v₀ : E) (hv₀ : j₀.2.2.1 v₀ ≠ 0) :
    let p₀ := j₀.2.2.1
    let π₀ : E →L[ℝ] p₀.ker :=
      (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
        (covectorSplitting p₀ v₀ hv₀).symm.toContinuousLinearMap
    let Φ : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ) :=
      fun q ↦ (q.1, (π₀ (q.2 - q.1.1),
        (scalarSecondJetPolynomial q.1 q.2 - q.1.2.1) / p₀ v₀))
    ∀ e : OpenPartialHomeomorph
        (ScalarSecondJet E × E) (ScalarSecondJet E × (p₀.ker × ℝ)),
      (e : ScalarSecondJet E × E → ScalarSecondJet E × (p₀.ker × ℝ)) = Φ →
      (j₀, j₀.1) ∈ e.source →
      ContDiffOn ℝ ∞ e.symm e.target →
      let σ : ScalarSecondJet E × p₀.ker → E :=
        fun q ↦ (e.symm (q.1, (q.2, 0))).2
      ∃ (O : Set (ScalarSecondJet E)) (B : Set p₀.ker),
        IsOpen O ∧ j₀ ∈ O ∧ IsOpen B ∧ (0 : p₀.ker) ∈ B ∧
        (∀ j ∈ O, j.2.2.1 v₀ ≠ 0 ∧ (j, j.1) ∈ e.source) ∧
        (∀ j ∈ O, ∀ w ∈ B, (j, (w, 0)) ∈ e.target) ∧
        ContDiffOn ℝ ∞ σ (O ×ˢ B) ∧
        ∀ j ∈ O, σ (j, 0) = j.1 ∧
          (∀ w ∈ B, scalarSecondJetPolynomial j (σ (j, w)) = j.2.1 ∧
            π₀ (σ (j, w) - j.1) = w) ∧
          InjOn (fun w ↦ σ (j, w)) B ∧
          (fun w ↦ σ (j, w)) '' B =
            {y | (j, y) ∈ e.source ∧ π₀ (y - j.1) ∈ B ∧
              scalarSecondJetPolynomial j y = j.2.1} := by
  classical
  dsimp only
  intro e he hz hInv
  let p₀ := j₀.2.2.1
  let π₀ : E →L[ℝ] p₀.ker :=
    (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
      (covectorSplitting p₀ v₀ hv₀).symm.toContinuousLinearMap
  let σ : ScalarSecondJet E × p₀.ker → E :=
    fun q ↦ (e.symm (q.1, (q.2, 0))).2
  have hbase (q : ScalarSecondJet E × (p₀.ker × ℝ)) (hq : q ∈ e.target) :
      (e.symm q).1 = q.1 := by
    have h := congrArg Prod.fst (e.right_inv hq)
    rw [he] at h
    exact h
  have hgraph (j : ScalarSecondJet E) : e (j, j.1) = (j, (0, 0)) := by
    rw [he]
    simp [scalarSecondJetPolynomial, secondJetPolynomial]
  let N := (fun q : ScalarSecondJet E × p₀.ker ↦ (q.1, (q.2, 0))) ⁻¹' e.target
  have hN : IsOpen N := e.open_target.preimage
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  have hzN : (j₀, (0 : p₀.ker)) ∈ N := by
    change (j₀, (0, 0)) ∈ e.target
    rw [← hgraph j₀]
    exact e.map_source hz
  obtain ⟨O₀, B, hO₀, hjO₀, hB, h0B, hprod⟩ :=
    mem_nhds_prod_iff'.mp (hN.mem_nhds hzN)
  let O := O₀ ∩ ((fun j : ScalarSecondJet E ↦ (j, j.1)) ⁻¹' e.source ∩
    {j : ScalarSecondJet E | j.2.2.1 v₀ ≠ 0})
  have hO : IsOpen O := hO₀.inter
    ((e.open_source.preimage (continuous_id.prodMk continuous_fst)).inter
      (isOpen_ne_fun (continuous_snd.snd.fst.clm_apply continuous_const) continuous_const))
  have hjO : j₀ ∈ O := ⟨hjO₀, hz, hv₀⟩
  have htarget (j : ScalarSecondJet E) (hj : j ∈ O) (w : p₀.ker) (hw : w ∈ B) :
      (j, (w, 0)) ∈ e.target := by
    change (j, w) ∈ N
    exact hprod ⟨hj.1, hw⟩
  have hpair (j : ScalarSecondJet E) (hj : j ∈ O) (w : p₀.ker) (hw : w ∈ B) :
      e.symm (j, (w, 0)) = (j, σ (j, w)) :=
    Prod.ext (hbase _ (htarget j hj w hw)) rfl
  have hforward (j : ScalarSecondJet E) (hj : j ∈ O) (w : p₀.ker) (hw : w ∈ B) :
      e (j, σ (j, w)) = (j, (w, 0)) := by
    rw [← hpair j hj w hw]
    exact e.right_inv (htarget j hj w hw)
  have hlevel (j : ScalarSecondJet E) (hj : j ∈ O) (w : p₀.ker) (hw : w ∈ B) :
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1 ∧
        π₀ (σ (j, w) - j.1) = w := by
    have hleft := congrArg (fun q ↦ q.2.1) (hforward j hj w hw)
    have hright := congrArg (fun q ↦ q.2.2) (hforward j hj w hw)
    rw [he] at hleft hright
    change π₀ (σ (j, w) - j.1) = w at hleft
    change (scalarSecondJetPolynomial j (σ (j, w)) - j.2.1) / p₀ v₀ = 0 at hright
    exact ⟨sub_eq_zero.mp ((div_eq_zero_iff.mp hright).resolve_right hv₀), hleft⟩
  refine ⟨O, B, hO, hjO, hB, h0B, ?_, htarget, ?_, ?_⟩
  · intro j hj
    exact ⟨hj.2.2, hj.2.1⟩
  · exact (hInv.comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
      (fun q hq ↦ htarget q.1 hq.1 q.2 hq.2)).snd
  · intro j hj
    have hcenter : σ (j, 0) = j.1 := by
      have h := e.left_inv hj.2.1
      rw [hgraph j] at h
      exact congrArg Prod.snd h
    refine ⟨hcenter, hlevel j hj, ?_, ?_⟩
    · intro w hw z hz hsame
      change σ (j, w) = σ (j, z) at hsame
      calc
        w = π₀ (σ (j, w) - j.1) := (hlevel j hj w hw).2.symm
        _ = π₀ (σ (j, z) - j.1) := by rw [hsame]
        _ = z := (hlevel j hj z hz).2
    · ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hsrc := e.map_target (htarget j hj w hw)
        rw [hpair j hj w hw] at hsrc
        exact ⟨hsrc, by rwa [(hlevel j hj w hw).2], (hlevel j hj w hw).1⟩
      · rintro ⟨hy, hw, hval⟩
        refine ⟨π₀ (y - j.1), hw, ?_⟩
        have hfwd : e (j, y) = (j, (π₀ (y - j.1), 0)) := by
          rw [he]
          change (j, (π₀ (y - j.1),
            (scalarSecondJetPolynomial j y - j.2.1) / p₀ v₀)) = _
          rw [hval, sub_self, zero_div]
        have hback := e.left_inv hy
        rw [hfwd] at hback
        exact congrArg Prod.snd hback

end OTSelector.Geometry

end
end
