import OTSelector.Analysis.Calculus.CommonLevelSection
import OTSelector.Analysis.Calculus.CompactUniformFirstJet
import OTSelector.Analysis.Calculus.ParameterizedSecondJetLevel
import OTSelector.Analysis.Calculus.SecondJetPolynomial
import OTSelector.Analysis.NormedSpace.CovectorSplitting
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformSecondJetLevelSection.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformSecondJetLevelSection`; the selected original proof blocks follow. -/
section

/-!
Conditions: Continuous compact second-jet parameters and two C1 level sections with matching central value and label differential.

Objects: A uniform o(label) comparison of the sections.

Proof detail: Apply the common compact first-order estimates to both sections and cancel their equal first jets.

Sources: Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110); Hassler Whitney, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2).
Relation: Uniform first-order corollary; ambient differentiability of the independent jet parameter is not required.
-/

/-!
# Uniform comparison of original and polynomial level sections

Original centers enter a common smooth polynomial section only through their actual
second-jet parameters. Continuity of that parameter map on the compact center set
suffices; its ambient differentiability is neither required nor asserted.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem uniform_comparison_on_compact_graph
    {P Q W V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U K : Set P} {O : Set Q} {B C : Set W}
    (hU : IsOpen U) (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hC : IsOpen C) (h0C : (0 : W) ∈ C) (hK : IsCompact K) (hKU : K ⊆ U)
    {j : P → Q} (hj : ContinuousOn j K) (hKj : ∀ x ∈ K, j x ∈ O)
    {ρ : P × W → V} {σ : Q × W → V}
    (hρ : ContDiffOn ℝ 1 ρ (U ×ˢ B)) (hσ : ContDiffOn ℝ 1 σ (O ×ˢ C))
    (hcenter : ∀ x ∈ K, ρ (x, 0) = σ (j x, 0))
    (hjets : ∀ x ∈ K,
      fderiv ℝ (fun w ↦ ρ (x, w)) 0 = fderiv ℝ (fun w ↦ σ (j x, w)) 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ K, ∀ w : W, ‖w‖ < r →
      (x, w) ∈ U ×ˢ B ∧ (j x, w) ∈ O ×ˢ C ∧
      ‖ρ (x, w) - σ (j x, w)‖ ≤ ε * ‖w‖ := by
  let D : Set ((P × Q) × W) := (U ×ˢ O) ×ˢ (B ∩ C)
  let L : Set ((P × Q) × W) := (fun x ↦ ((x, j x), (0 : W))) '' K
  let f : (P × Q) × W → V := fun z ↦ ρ (z.1.1, z.2)
  let g : (P × Q) × W → V := fun z ↦ σ (z.1.2, z.2)
  have hD : IsOpen D := (hU.prod hO).prod (hB.inter hC)
  have hL : IsCompact L :=
    hK.image_of_continuousOn ((continuousOn_id.prodMk hj).prodMk continuousOn_const)
  have hLD : L ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨hKU hx, hKj x hx⟩, h0B, h0C⟩
  have hf : ContDiffOn ℝ 1 f D := hρ.comp
    (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun z hz ↦ ⟨hz.1.1, hz.2.1⟩)
  have hg : ContDiffOn ℝ 1 g D := hσ.comp
    (contDiffOn_fst.snd.prodMk contDiffOn_snd) (fun z hz ↦ ⟨hz.1.2, hz.2.2⟩)
  have hvalue : ∀ z ∈ L, f z = g z := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcenter x hx
  have hderiv : ∀ z ∈ L, ∀ w : W,
      (fderiv ℝ f z) (0, w) = (fderiv ℝ g z) (0, w) := by
    rintro _ ⟨x, hx, rfl⟩ w
    have hlegal : ((x, j x), (0 : W)) ∈ D := hLD ⟨x, hx, rfl⟩
    have hfD := (hf.contDiffAt (hD.mem_nhds hlegal)).differentiableAt (by simp)
    have hgD := (hg.contDiffAt (hD.mem_nhds hlegal)).differentiableAt (by simp)
    have hfcomp := hfD.hasFDerivAt.comp 0
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (x, j x) (0 : W))
    have hgcomp := hgD.hasFDerivAt.comp 0
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (x, j x) (0 : W))
    have heq := hfcomp.fderiv.symm.trans ((hjets x hx).trans hgcomp.fderiv)
    exact DFunLike.congr_fun heq w
  obtain ⟨r, hr, hrem⟩ := exists_uniform_label_difference_of_same_firstJet
    hD hf hg hL hLD hvalue hderiv hε
  refine ⟨r, hr, ?_⟩
  intro x hx w hw
  have hh := hrem ((x, j x), 0) ⟨x, hx, rfl⟩ w hw
  have hdom : ((x, j x), w) ∈ D := by simpa only [zero_add] using hh.1
  exact ⟨⟨hdom.1.1, hdom.2.1⟩, ⟨hdom.1.2, hdom.2.2⟩,
    by simpa only [zero_add] using hh.2⟩

/-- The original level section and its selected polynomial section have uniformly
small first-order differences on a compact family of actual second jets. -/
theorem exists_uniform_secondJet_levelSection_error
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    {G : E → ℝ} {U K : Set E} {O : Set (ScalarSecondJet E)}
    {B C : Set p₀.ker} (hU : IsOpen U) (hO : IsOpen O)
    (hB : IsOpen B) (h0B : (0 : p₀.ker) ∈ B)
    (hC : IsOpen C) (h0C : (0 : p₀.ker) ∈ C)
    (hG : ContDiffOn ℝ 1 G U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hH : ContinuousOn (fderiv ℝ (fderiv ℝ G)) K)
    (hKj : ∀ x ∈ K, (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    (hp : ∀ x ∈ K, (fderiv ℝ G x) v₀ ≠ 0)
    {ρ : E × p₀.ker → E} {σ : ScalarSecondJet E × p₀.ker → E}
    (hρ : ContDiffOn ℝ 1 ρ (U ×ˢ B)) (hσ : ContDiffOn ℝ 1 σ (O ×ˢ C))
    (hρ₀ : ∀ x ∈ K, ρ (x, 0) = x)
    (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hρlevel : ∀ x ∈ K, ∀ w ∈ B, G (ρ (x, w)) = G x)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ C, scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    (hρproj : ∀ x ∈ K, ∀ w ∈ B,
      ((covectorSplitting p₀ v₀ hp₀).symm (ρ (x, w) - x)).1 = w)
    (hσproj : ∀ j ∈ O, ∀ w ∈ C,
      ((covectorSplitting p₀ v₀ hp₀).symm (σ (j, w) - j.1)).1 = w)
    {ε : ℝ} (hε : 0 < ε) :
    let j : E → ScalarSecondJet E :=
      fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    ∃ r > 0, ∀ x ∈ K, ∀ w : p₀.ker, ‖w‖ < r →
      (x, w) ∈ U ×ˢ B ∧ (j x, w) ∈ O ×ˢ C ∧
      ‖ρ (x, w) - σ (j x, w)‖ ≤ ε * ‖w‖ := by
  let j : E → ScalarSecondJet E :=
    fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let R (x : E) : p₀.ker →L[ℝ] E :=
    p₀.ker.subtypeL - ((fderiv ℝ G x).comp p₀.ker.subtypeL).smulRight
      (((fderiv ℝ G x) v₀)⁻¹ • v₀)
  have hj : ContinuousOn j K := continuousOn_id.prodMk
    ((hG.continuousOn.mono hKU).prodMk
      (((hG.continuousOn_fderiv_of_isOpen hU (by rfl)).mono hKU).prodMk hH))
  have hρD (x : E) (hx : x ∈ K) : HasFDerivAt (fun w ↦ ρ (x, w)) (R x) 0 := by
    have hGD := (hG.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp)
    have hslice : DifferentiableAt ℝ (fun w ↦ ρ (x, w)) 0 :=
      ((hρ.contDiffAt ((hU.prod hB).mem_nhds ⟨hKU hx, h0B⟩)).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hp₀ hGD.hasFDerivAt
      (hp x hx) hslice (hρ₀ x hx)
      (Filter.eventually_of_mem (hB.mem_nhds h0B) (fun w hw ↦ hρlevel x hx w hw))
      (Filter.eventually_of_mem (hB.mem_nhds h0B) (fun w hw ↦ hρproj x hx w hw))
  have hσD (x : E) (hx : x ∈ K) : HasFDerivAt (fun w ↦ σ (j x, w)) (R x) 0 := by
    have hslice : DifferentiableAt ℝ (fun w ↦ σ (j x, w)) 0 :=
      ((hσ.contDiffAt ((hO.prod hC).mem_nhds ⟨hKj x hx, h0C⟩)).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    apply hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hp₀
      (hasFDerivAt_scalarSecondJetPolynomial_center (j x)) (hp x hx)
      hslice (hσ₀ (j x) (hKj x hx))
    · filter_upwards [hC.mem_nhds h0C] with w hw
      rw [hσlevel (j x) (hKj x hx) w hw]
      simp [scalarSecondJetPolynomial, secondJetPolynomial]
    · exact Filter.eventually_of_mem (hC.mem_nhds h0C)
        (fun w hw ↦ hσproj (j x) (hKj x hx) w hw)
  exact uniform_comparison_on_compact_graph hU hO hB h0B hC h0C hK hKU hj
    hKj hρ hσ (fun x hx ↦ (hρ₀ x hx).trans (hσ₀ (j x) (hKj x hx)).symm)
    (fun x hx ↦ (hρD x hx).fderiv.trans (hσD x hx).fderiv.symm) hε

end OTSelector.Geometry

end
end
