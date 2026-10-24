import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import OTSelector.Analysis.Calculus.SmoothInjectiveTube
import OTSelector.Analysis.NormedSpace.CovectorSplitting
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CommonLevelSection.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CommonLevelSection`; the selected original proof blocks follow. -/
section

/-!
Conditions: A fixed projection is transverse to the given nonzero level covector and the actual level map is C1 near the center.

Objects: A common local level section and its differential.

Proof detail: Invert the level/projection product map, differentiate its inverse identity and solve the level and projection linear equations.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Jiří Lebl, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57 (https://www.jirka.org/ra/realanal2.pdf#page=51).
Relation: Explicit implicit-function construction and derivative, with transversality included in the hypotheses.
-/

/-!
# Common level sections with a fixed projection

One fixed covector projection gives compatible local level sections at nearby centers.
The derivative follows from their actual level and projection identities.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual level and fixed-projection identities determine the section derivative. -/
theorem hasFDerivAt_levelSection_of_fixedProjection
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    {f : E → ℝ} {x : E} {p : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f p x) (hp : p v₀ ≠ 0)
    {σ : p₀.ker → E} (hσ : DifferentiableAt ℝ σ 0) (hσ₀ : σ 0 = x)
    (hlevel : ∀ᶠ w in 𝓝 (0 : p₀.ker), f (σ w) = f x)
    (hprojection :
      let π₀ : E →L[ℝ] p₀.ker :=
        (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
          (covectorSplitting p₀ v₀ hp₀).symm.toContinuousLinearMap
      ∀ᶠ w in 𝓝 (0 : p₀.ker), π₀ (σ w - x) = w) :
    HasFDerivAt σ
      (p₀.ker.subtypeL -
        (p.comp p₀.ker.subtypeL).smulRight ((p v₀)⁻¹ • v₀)) 0 := by
  let π₀ : E →L[ℝ] p₀.ker :=
    (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
      (covectorSplitting p₀ v₀ hp₀).symm.toContinuousLinearMap
  let R := fderiv ℝ σ 0
  have hR : HasFDerivAt σ R 0 := hσ.hasFDerivAt
  have hpf : p.comp R = 0 := by
    have hf₀ : HasFDerivAt f p (σ 0) := by simpa only [hσ₀] using hf
    have hh := hf₀.comp 0 hR
    exact (hh.congr_of_eventuallyEq (Filter.EventuallyEq.symm hlevel)).unique
      (hasFDerivAt_const _ _)
  change ∀ᶠ w in 𝓝 (0 : p₀.ker), π₀ (σ w - x) = w at hprojection
  have hπ : π₀.comp R = ContinuousLinearMap.id ℝ p₀.ker := by
    have hh := π₀.hasFDerivAt.comp 0 (hR.sub_const x)
    exact (hh.congr_of_eventuallyEq (Filter.EventuallyEq.symm hprojection)).unique
      (hasFDerivAt_id _)
  have heq : R = p₀.ker.subtypeL -
      (p.comp p₀.ker.subtypeL).smulRight ((p v₀)⁻¹ • v₀) := by
    ext w
    have hw : (w : E) = R w - (p₀ (R w) / p₀ v₀) • v₀ := by
      have hh := congrArg (fun A : p₀.ker →L[ℝ] p₀.ker ↦ (A w : E)) hπ
      simpa [π₀] using hh.symm
    have hpw : p (R w) = 0 := by
      have hh := congrArg (fun A : p₀.ker →L[ℝ] ℝ ↦ A w) hpf
      simpa using hh
    have hc : p₀ (R w) / p₀ v₀ = -(p (w : E) / p v₀) := by
      have hh := congrArg p hw
      simp only [map_sub, map_smul, smul_eq_mul, hpw, zero_sub] at hh
      apply (eq_neg_iff_add_eq_zero).mpr
      apply (mul_right_cancel₀ hp)
      simp only [add_mul, div_mul_cancel₀ _ hp, zero_mul]
      linarith
    rw [hc] at hw
    simp only [sub_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smul_smul]
    rw [← div_eq_mul_inv]
    rw [neg_smul, sub_neg_eq_add] at hw
    exact eq_sub_of_add_eq hw.symm
  exact heq ▸ hR

variable [FiniteDimensional ℝ E]

private theorem exists_fixedProjection_inverse
    {G : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω)
    (v₀ : E) (hpv : (fderiv ℝ G x₀) v₀ ≠ 0) :
    let p₀ := fderiv ℝ G x₀
    let π₀ : E →L[ℝ] p₀.ker :=
      (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
        (covectorSplitting p₀ v₀ hpv).symm.toContinuousLinearMap
    ∃ e : OpenPartialHomeomorph E (p₀.ker × ℝ),
      (e : E → p₀.ker × ℝ) = (fun y ↦ (π₀ (y - x₀), G y - G x₀)) ∧
      x₀ ∈ e.source ∧ e.source ⊆ Ω ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target := by
  let p₀ := fderiv ℝ G x₀
  let S := covectorSplitting p₀ v₀ hpv
  let π₀ : E →L[ℝ] p₀.ker :=
    (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp S.symm.toContinuousLinearMap
  let A := S.toHomeomorph.trans (Homeomorph.addRight x₀)
  have hA : ContDiff ℝ 1 A := S.contDiff.add contDiff_const
  have hAs : ContDiff ℝ 1 A.symm :=
    S.symm.contDiff.comp (contDiff_id.add contDiff_const)
  have hAz : A (0, 0) = x₀ := by simp [A]
  let Ω' := A ⁻¹' Ω
  have hΩ' : IsOpen Ω' := hΩ.preimage A.continuous
  let f : p₀.ker × ℝ → p₀.ker × ℝ := fun z ↦ (z.1, G (A z) - G x₀)
  have hf : ContDiffOn ℝ 1 f Ω' :=
    contDiffOn_fst.prodMk ((hG.comp hA.contDiffOn (fun _ hz ↦ hz)).sub contDiffOn_const)
  let D := (ContinuousLinearEquiv.refl ℝ p₀.ker).prodCongr
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (p₀ v₀) hpv))
  have hGA : HasFDerivAt (fun z ↦ G (A z) - G x₀)
      (p₀.comp S.toContinuousLinearMap) (0, 0) := by
    have hg : HasFDerivAt G p₀ (A (0, 0)) := by
      rw [hAz]
      exact (hG.contDiffAt (hΩ.mem_nhds hx₀)).differentiableAt (by simp) |>.hasFDerivAt
    exact (hg.comp (0, 0) (S.hasFDerivAt.add_const x₀)).sub_const (G x₀)
  have hD : HasFDerivAt f D.toContinuousLinearMap (0, 0) := by
    have heq : (ContinuousLinearMap.fst ℝ p₀.ker ℝ).prod
        (p₀.comp S.toContinuousLinearMap) = D.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      rintro ⟨w, t⟩
      apply Prod.ext
      · rfl
      · have hw : p₀ (w : E) = 0 := w.property
        simp [D, S, hw, smul_eq_mul]
    rw [← heq]
    exact hasFDerivAt_fst.prodMk hGA
  have hcenter : ({0} : Set p₀.ker) ×ˢ ({0} : Set ℝ) ⊆ Ω' := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    simp only [mem_singleton_iff] at hw ht
    subst w
    subst t
    change A (0, 0) ∈ Ω
    rwa [hAz]
  have hInv : ∀ t ∈ ({0} : Set p₀.ker), (fderiv ℝ f (t, 0)).IsInvertible := by
    intro t ht
    rcases mem_singleton_iff.mp ht with rfl
    rw [hD.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  obtain ⟨T, V, e₀, _, _, hT, hV, hTV, he₀, hs₀, _, hF, hI⟩ :=
    exists_smooth_common_tube_inverse isCompact_singleton hΩ' (by rfl) hf hcenter
      (Set.injOn_singleton _ _) hInv
  let e := A.symm.transOpenPartialHomeomorph e₀
  have he : (e : E → p₀.ker × ℝ) =
      (fun y ↦ (π₀ (y - x₀), G y - G x₀)) := by
    funext y
    change e₀ (A.symm y) = _
    rw [he₀]
    change ((A.symm y).1, G (A (A.symm y)) - G x₀) = _
    rw [A.apply_symm_apply]
    simp [A, π₀, Homeomorph.addRight_symm, sub_eq_add_neg]
  have hes : e.source ⊆ Ω := by
    intro y hy
    change A.symm y ∈ e₀.source at hy
    rw [hs₀] at hy
    have hh := hTV hy
    change A (A.symm y) ∈ Ω at hh
    simpa using hh
  refine ⟨e, he, ?_, hes, ?_, ?_⟩
  · change A.symm x₀ ∈ e₀.source
    rw [← hAz, A.symm_apply_apply, hs₀]
    exact ⟨hT (mem_singleton _), hV⟩
  · exact hF.comp hAs.contDiffOn (fun _ hy ↦ hy)
  · exact hA.contDiffOn.comp hI (mapsTo_univ _ _)

/-- One common fixed-projection inverse supplies compatible nearby level sections. -/
theorem exists_contDiff_common_fixedProjection_levelSection
    {G : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω)
    (v₀ : E) (hpv : (fderiv ℝ G x₀) v₀ ≠ 0) :
    let p₀ := fderiv ℝ G x₀
    let π₀ : E →L[ℝ] p₀.ker :=
      (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
        (covectorSplitting p₀ v₀ hpv).symm.toContinuousLinearMap
    ∃ e : OpenPartialHomeomorph E (p₀.ker × ℝ),
      (e : E → p₀.ker × ℝ) =
        (fun y ↦ (π₀ (y - x₀), G y - G x₀)) ∧
      x₀ ∈ e.source ∧ e.source ⊆ Ω ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      let ρ : E × p₀.ker → E :=
        fun z ↦ e.symm (π₀ (z.1 - x₀) + z.2, G z.1 - G x₀)
      ∃ (U : Set E) (B : Set p₀.ker),
        IsOpen U ∧ x₀ ∈ U ∧ U ⊆ e.source ∧
        IsOpen B ∧ (0 : p₀.ker) ∈ B ∧ ContDiffOn ℝ 1 ρ (U ×ˢ B) ∧
        ∀ x ∈ U,
          (fderiv ℝ G x) v₀ ≠ 0 ∧ ρ (x, 0) = x ∧
          (∀ w ∈ B,
            (π₀ (x - x₀) + w, G x - G x₀) ∈ e.target ∧
            ρ (x, w) ∈ e.source ∧ G (ρ (x, w)) = G x ∧
            π₀ (ρ (x, w) - x) = w) ∧
          InjOn (fun w ↦ ρ (x, w)) B ∧
          (fun w ↦ ρ (x, w)) '' B =
            {y | y ∈ e.source ∧ π₀ (y - x) ∈ B ∧ G y = G x} ∧
          HasFDerivAt (fun w ↦ ρ (x, w))
            (p₀.ker.subtypeL -
              ((fderiv ℝ G x).comp p₀.ker.subtypeL).smulRight
                (((fderiv ℝ G x) v₀)⁻¹ • v₀)) 0 := by
  let p₀ := fderiv ℝ G x₀
  let π₀ : E →L[ℝ] p₀.ker :=
    (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
      (covectorSplitting p₀ v₀ hpv).symm.toContinuousLinearMap
  obtain ⟨e, he, hxsource, hsource, hforward, hinverse⟩ :=
    exists_fixedProjection_inverse hΩ hG hx₀ v₀ hpv
  change (e : E → p₀.ker × ℝ) = (fun y ↦ (π₀ (y - x₀), G y - G x₀)) at he
  let T : E × p₀.ker → p₀.ker × ℝ :=
    fun z ↦ (π₀ (z.1 - x₀) + z.2, G z.1 - G x₀)
  let ρ : E × p₀.ker → E := fun z ↦ e.symm (T z)
  have hG₀ : ContDiffAt ℝ 1 G x₀ := hG.contDiffAt (hΩ.mem_nhds hx₀)
  have hT₀ : ContDiffAt ℝ 1 T (x₀, 0) :=
    ((π₀.contDiff.contDiffAt.comp _ (contDiffAt_fst.sub contDiffAt_const)).add
      contDiffAt_snd).prodMk
      ((hG₀.comp _ contDiffAt_fst).sub contDiffAt_const)
  have hTcenter : T (x₀, 0) ∈ e.target := by
    have hh := e.map_source hxsource
    simpa [he, T] using hh
  have hnonzero : ContinuousAt (fun x ↦ (fderiv ℝ G x) v₀) x₀ :=
    ((hG.continuousOn_fderiv_of_isOpen hΩ (by rfl)).continuousAt
      (hΩ.mem_nhds hx₀)).clm_apply continuousAt_const
  have hn0 : ContinuousAt (fun z : E × p₀.ker ↦ (fderiv ℝ G z.1) v₀) (x₀, 0) :=
    hnonzero.comp (f := fun z : E × p₀.ker ↦ z.1)
      (x := (x₀, (0 : p₀.ker))) continuousAt_fst
  have hgood : {z : E × p₀.ker | z.1 ∈ e.source ∧
      (fderiv ℝ G z.1) v₀ ≠ 0 ∧ T z ∈ e.target} ∈ 𝓝 (x₀, 0) := by
    exact inter_mem
      (continuousAt_fst.preimage_mem_nhds (e.open_source.mem_nhds hxsource))
      (inter_mem
        (hn0.eventually_ne hpv)
        (hT₀.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hTcenter)))
  obtain ⟨U, B, hU, hxU, hB, h0B, hUB⟩ := mem_nhds_prod_iff'.mp hgood
  have hUsource : U ⊆ e.source :=
    fun x hx ↦ (hUB (show (x, 0) ∈ U ×ˢ B from ⟨hx, h0B⟩)).1
  have hUΩ : U ⊆ Ω := hUsource.trans hsource
  have htarget (x : E) (hx : x ∈ U) (w : p₀.ker) (hw : w ∈ B) :
      T (x, w) ∈ e.target := (hUB (show (x, w) ∈ U ×ˢ B from ⟨hx, hw⟩)).2.2
  have hT : ContDiffOn ℝ 1 T (U ×ˢ B) :=
    ((π₀.contDiff.comp_contDiffOn
      (contDiffOn_fst.sub contDiffOn_const)).add contDiffOn_snd).prodMk
      ((hG.comp contDiffOn_fst (fun _ hz ↦ hUΩ hz.1)).sub contDiffOn_const)
  have hρ : ContDiffOn ℝ 1 ρ (U ×ˢ B) :=
    hinverse.comp hT (fun z hz ↦ htarget z.1 hz.1 z.2 hz.2)
  have hcenter (x : E) (hx : x ∈ U) : ρ (x, 0) = x := by
    have hTx : T (x, 0) = e x := by simp [T, he]
    change e.symm (T (x, 0)) = x
    rw [hTx, e.left_inv (hUsource hx)]
  have hlevel (x : E) (hx : x ∈ U) (w : p₀.ker) (hw : w ∈ B) :
      G (ρ (x, w)) = G x ∧ π₀ (ρ (x, w) - x) = w := by
    have hh := e.right_inv (htarget x hx w hw)
    have h₁ := congrArg Prod.fst hh
    have h₂ := congrArg Prod.snd hh
    rw [he] at h₁ h₂
    change π₀ (ρ (x, w) - x₀) = π₀ (x - x₀) + w at h₁
    change G (ρ (x, w)) - G x₀ = G x - G x₀ at h₂
    refine ⟨sub_left_injective h₂, ?_⟩
    calc
      π₀ (ρ (x, w) - x) = π₀ (ρ (x, w) - x₀) - π₀ (x - x₀) := by
        simp only [map_sub]
        abel
      _ = w := by rw [h₁]; abel
  refine ⟨e, he, hxsource, hsource, hforward, hinverse,
    U, B, hU, hxU, hUsource, hB, h0B, hρ, ?_⟩
  intro x hx
  have hxn : (fderiv ℝ G x) v₀ ≠ 0 := (hUB (show (x, 0) ∈ U ×ˢ B from ⟨hx, h0B⟩)).2.1
  refine ⟨hxn, hcenter x hx, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact ⟨htarget x hx w hw, e.map_target (htarget x hx w hw), hlevel x hx w hw⟩
  · intro w hw z hz hsame
    change ρ (x, w) = ρ (x, z) at hsame
    calc
      w = π₀ (ρ (x, w) - x) := (hlevel x hx w hw).2.symm
      _ = π₀ (ρ (x, z) - x) := by rw [hsame]
      _ = z := (hlevel x hx z hz).2
  · ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨e.map_target (htarget x hx w hw),
        by rwa [(hlevel x hx w hw).2], (hlevel x hx w hw).1⟩
    · rintro ⟨hy, hw, hGy⟩
      refine ⟨π₀ (y - x), hw, ?_⟩
      have hTy : T (x, π₀ (y - x)) = e y := by
        rw [he]
        change (π₀ (x - x₀) + π₀ (y - x), G x - G x₀) = _
        simp only [map_sub, hGy]
        congr 1
        abel
      change e.symm (T (x, π₀ (y - x))) = y
      rw [hTy, e.left_inv hy]
  · have hGD : HasFDerivAt G (fderiv ℝ G x) x :=
      (hG.contDiffAt (hΩ.mem_nhds (hUΩ hx))).differentiableAt (by simp) |>.hasFDerivAt
    have hρD : DifferentiableAt ℝ (fun w ↦ ρ (x, w)) 0 :=
      ((hρ.contDiffAt ((hU.prod hB).mem_nhds ⟨hx, h0B⟩)).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hpv hGD hxn hρD (hcenter x hx)
      (Filter.eventually_of_mem (hB.mem_nhds h0B) (fun w hw ↦ (hlevel x hx w hw).1))
      (Filter.eventually_of_mem (hB.mem_nhds h0B) (fun w hw ↦ (hlevel x hx w hw).2))

end OTSelector.Geometry

end
end
