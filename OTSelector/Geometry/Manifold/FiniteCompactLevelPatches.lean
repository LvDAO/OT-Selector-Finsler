import OTSelector.Geometry.Manifold.RegularLevelChart
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FiniteCompactLevelPatches.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FiniteCompactLevelPatches`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C1 scalar regular level near a compact set and actual transverse local inverse maps.

Objects: Finitely many compact level patches with smaller closed label balls inside larger Lipschitz balls.

Proof detail: Apply the implicit function theorem, choose nested balls, obtain local derivative/Lipschitz bounds and take a finite compact subcover.

Sources: Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Quantitative compact regular-level atlas corollary.
-/

/-!
# Compact label interiors of actual regular level patches

The same inverse level chart retains a larger Lipschitz ball around the closed
inner label ball. Its inner open image still covers a relative neighborhood.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A regular C1 level has a Lipschitz ball section whose image is the exact level
inside an open neighborhood, retaining the actual kernel-inclusion derivative. -/
theorem exists_compact_lipschitz_levelPatch {f : E → ℝ} {Ω : Set E} {x : E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) (hx : x ∈ Ω)
    (hp : fderiv ℝ f x ≠ 0) :
    let W := (fderiv ℝ f x).ker
    ∃ (a : ℝ) (C : ℝ≥0) (σ : W → E) (U : Set E),
      0 < a ∧ σ 0 = x ∧ ContDiffOn ℝ 1 σ (ball 0 (2 * a)) ∧
      LipschitzOnWith C σ (ball 0 (2 * a)) ∧ MapsTo σ (ball 0 (2 * a)) Ω ∧
      (∀ w ∈ ball 0 (2 * a), f (σ w) = f x) ∧ HasFDerivAt σ W.subtypeL 0 ∧
      InjOn σ (ball 0 (2 * a)) ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      σ '' ball 0 a = U ∩ {y | f y = f x} ∧
      Module.finrank ℝ W + 1 = Module.finrank ℝ E ∧
      ∀ w ∈ ball 0 (2 * a), Function.Injective (fderiv ℝ σ w) := by
  obtain ⟨e, hxe, hsource, he, hei, hex, hfirst, hsection, hdim⟩ :=
    exists_contDiff_levelCoordinates (by rfl : (1 : ℕ∞ω) ≤ 1) hΩ hf hx hp
  let W := (fderiv ℝ f x).ker
  let σ : W → E := fun w ↦ e.symm (f x, w)
  let B : Set W := {w | (f x, w) ∈ e.target}
  have hB : IsOpen B := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have h0 : (0 : W) ∈ B := by
    change (f x, 0) ∈ e.target
    rw [← hex]
    exact e.map_source hxe
  have hσ : ContDiffOn ℝ 1 σ B :=
    hei.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ hw)
  have hσ0 : σ 0 = x := by
    change e.symm (f x, 0) = x
    rw [← hex, e.left_inv hxe]
  obtain ⟨C, S, hS, hLip⟩ := (hσ.contDiffAt (hB.mem_nhds h0)).exists_lipschitzOnWith
  obtain ⟨R, hR, has⟩ := Metric.mem_nhds_iff.mp (inter_mem hS (hB.mem_nhds h0))
  let a := R / 2
  have ha : 0 < a := half_pos hR
  have htwice : 2 * a = R := by dsimp [a]; ring
  have has' : ball (0 : W) (2 * a) ⊆ S ∩ B := by simpa only [htwice] using has
  have haB : ball (0 : W) (2 * a) ⊆ B := fun _ hw ↦ (has' hw).2
  have hsmall : ball (0 : W) a ⊆ ball 0 (2 * a) := ball_subset_ball (by linarith)
  let U : Set E := e.source ∩ (fun y ↦ (e y).2) ⁻¹' ball (0 : W) a
  have hU : IsOpen U := e.continuousOn.snd.isOpen_inter_preimage e.open_source isOpen_ball
  have hcenter : x ∈ U := by
    exact ⟨hxe, by change (e x).2 ∈ ball 0 a; rw [hex]; exact mem_ball_self ha⟩
  have hlevel : ∀ w ∈ ball 0 (2 * a), f (σ w) = f x := by
    intro w hw
    simpa only [hfirst] using congrArg Prod.fst (e.right_inv (haB hw))
  have hinj : InjOn σ (ball 0 (2 * a)) := by
    intro w hw v hv h
    exact congrArg Prod.snd (e.symm.injOn (haB hw) (haB hv) h)
  have himm (w : W) (hw : w ∈ ball 0 (2 * a)) :
      Function.Injective (fderiv ℝ σ w) := by
    have hs := (hσ.contDiffAt (hB.mem_nhds (haB hw))).differentiableAt one_ne_zero
    have hew := (he.contDiffAt
      (e.open_source.mem_nhds (e.map_target (haB hw)))).differentiableAt one_ne_zero
    have hd := hew.snd.hasFDerivAt.comp w hs.hasFDerivAt
    have hid : HasFDerivAt (id : W → W)
        ((fderiv ℝ (fun y ↦ (e y).2) (σ w)).comp (fderiv ℝ σ w)) w := by
      apply hd.congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds (haB hw)] with v hv
      exact (congrArg Prod.snd (e.right_inv hv)).symm
    have hleft : Function.LeftInverse
        (fderiv ℝ (fun y ↦ (e y).2) (σ w)) (fderiv ℝ σ w) := by
      intro v
      exact congrArg (fun T : W →L[ℝ] W ↦ T v) (hid.unique (hasFDerivAt_id w))
    exact hleft.injective
  refine ⟨a, C, σ, U, ha, hσ0, hσ.mono haB, hLip.mono (fun _ hw ↦ (has' hw).1),
    (fun _ hw ↦ hsource (e.map_target (haB hw))), hlevel, hsection, hinj,
    hU, hcenter, fun _ hy ↦ hsource hy.1, ?_, hdim, himm⟩
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨e.map_target (haB (hsmall hw)), ?_⟩, hlevel w (hsmall hw)⟩
    change (e (e.symm (f x, w))).2 ∈ ball 0 a
    simpa only [e.right_inv (haB (hsmall hw))] using hw
  · rintro ⟨hyU, hyf⟩
    have hey : e y = (f x, (e y).2) := Prod.ext ((hfirst y).trans hyf) rfl
    refine ⟨(e y).2, hyU.2, ?_⟩
    change e.symm (f x, (e y).2) = y
    rw [← hey, e.left_inv hyU.1]

/-- Every level of a compact set on which the actual C1 derivative is nonzero is
covered by finitely many Lipschitz kernel sections, restricted to that same compact set. -/
theorem exists_finite_compact_lipschitz_levelPatches {f : E → ℝ} {K Ω : Set E}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) (hf : ContDiff ℝ 1 f)
    (hp : ∀ x ∈ K, fderiv ℝ f x ≠ 0) (c : ℝ) :
    let H := K ∩ {x | f x = c}
    ∃ (J : Finset H) (a : H → ℝ) (C : H → ℝ≥0)
      (σ : ∀ x : H, (fderiv ℝ f (x : E)).ker → E),
      (∀ x ∈ J, 0 < a x ∧ σ x 0 = (x : E) ∧
        ContDiffOn ℝ 1 (σ x) (ball 0 (2 * a x)) ∧ LipschitzOnWith (C x) (σ x) (ball 0 (2 * a x)) ∧
        MapsTo (σ x) (ball 0 (2 * a x)) Ω ∧ (∀ w ∈ ball 0 (2 * a x), f (σ x w) = c) ∧
        HasFDerivAt (σ x) (fderiv ℝ f (x : E)).ker.subtypeL 0 ∧
        InjOn (σ x) (ball 0 (2 * a x)) ∧
        Module.finrank ℝ (fderiv ℝ f (x : E)).ker + 1 = Module.finrank ℝ E ∧
        ∀ w ∈ ball 0 (2 * a x), Function.Injective (fderiv ℝ (σ x) w)) ∧
      H = ⋃ x ∈ J, σ x '' (ball 0 (a x) ∩ (σ x) ⁻¹' K) := by
  classical
  let H := K ∩ {x | f x = c}
  have hH : IsCompact H := hK.inter_right (isClosed_eq hf.continuous continuous_const)
  have hlocal (x : H) := exists_compact_lipschitz_levelPatch hΩ hf.contDiffOn
    (hKΩ x.property.1) (hp x x.property.1)
  choose a C σ U ha hσ0 hσ hLip hmap hlevel hder hinj hU hxU hUΩ himage hdim himm
    using hlocal
  obtain ⟨J, hJ⟩ := hH.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  refine ⟨J, a, C, σ, ?_, ?_⟩
  · intro x hx
    exact ⟨ha x, hσ0 x, hσ x, hLip x, hmap x,
      fun w hw ↦ (hlevel x w hw).trans x.property.2, hder x, hinj x, hdim x, himm x⟩
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, hyU⟩ := mem_iUnion₂.mp (hJ hy)
      have hylevel : f y = f (x : E) := hy.2.trans x.property.2.symm
      obtain ⟨w, hw, hwy⟩ := (himage x).symm ▸ (show y ∈ U x ∩ {y | f y = f x}
        from ⟨hyU, hylevel⟩)
      refine mem_iUnion₂.mpr ⟨x, hx, w, ⟨hw, ?_⟩, hwy⟩
      change σ x w ∈ K
      exact hwy.symm ▸ hy.1
    · intro y hy
      obtain ⟨x, hx, w, ⟨hw, hwK⟩, rfl⟩ := mem_iUnion₂.mp hy
      exact ⟨hwK, (hlevel x w (ball_subset_ball (by linarith [ha x]) hw)).trans x.property.2⟩

end OTSelector.Geometry

end
end
