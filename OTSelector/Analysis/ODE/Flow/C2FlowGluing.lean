import OTSelector.Geometry.Finsler.Hamiltonian.IntegralCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.C2FlowGluing.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.C2FlowGluing`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two actual C2 solution families agree at one time on a connected overlap, under the stated local uniqueness hypotheses.

Objects: Agreement throughout the overlap and a glued actual C2 flow family with preserved range and first derivatives.

Proof detail: Propagate equality by open-and-closed uniqueness, use the common local germs across the seam and glue the actual derivatives.

Sources: Gerald Teschl, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61); Gerald Teschl, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49); Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37).
Relation: Parameterized C2 gluing extension of the classical maximal-solution overlap argument.
-/

/-!
# Gluing actual C2 solution families

Local uniqueness of the original smooth field propagates over a connected open
time domain. Two actual C2 families with the same values at one common time
therefore agree on the overlap. Their piecewise gluing retains the original ODE,
range, joint C2 regularity and actual full derivatives on each open piece.
-/

open Set Filter Metric
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Uniqueness of actual smooth-field solutions on a connected open time set.
Only the first curve needs an explicit field-domain condition. -/
theorem integralCurve_eqOn_of_contDiffOn
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {α β : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hmap : MapsTo α I U)
    (hα : ∀ t ∈ I, HasDerivAt α (X (α t)) t)
    (hβ : ∀ t ∈ I, HasDerivAt β (X (β t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (heq : α t₀ = β t₀) : EqOn α β I := by
  have : PreconnectedSpace I := Subtype.preconnectedSpace hconn
  let S : Set I := {t | α t = β t}
  have hc : IsClosed S := isClosed_eq
    (HasDerivAt.continuousOn hα).domRestrict (HasDerivAt.continuousOn hβ).domRestrict
  have ho : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hx : ContDiffAt ℝ 1 X (α t) :=
      (hX.contDiffAt (hU.mem_nhds (hmap t.2))).of_le (by simp)
    have hg := integralCurve_eventuallyEq_of_contDiffAt hx rfl ht.symm
      (Filter.eventually_of_mem (hI.mem_nhds t.2) hα)
      (Filter.eventually_of_mem (hI.mem_nhds t.2) hβ)
    exact continuousAt_subtype_val.tendsto.eventually hg
  have hall : S = univ := (show IsClopen S from ⟨hc, ho⟩).eq_univ ⟨⟨t₀, ht₀⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : I) ∈ S := hall.symm ▸ mem_univ _
  exact hm

/-- Actual solution families glue across an open connected overlap from equality at
one common time. Their full actual derivatives agree with the respective old families. -/
theorem exists_glued_c2Family
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {B : Set W} {I J : Set ℝ} (hB : IsOpen B) (hI : IsOpen I) (hJ : IsOpen J)
    (hconn : IsPreconnected (I ∩ J))
    {Ψ Θ : W × ℝ → E}
    (hΨ : ContDiffOn ℝ 2 Ψ (B ×ˢ I)) (hΘ : ContDiffOn ℝ 2 Θ (B ×ˢ J))
    (hΨmap : MapsTo Ψ (B ×ˢ I) U) (hΘmap : MapsTo Θ (B ×ˢ J) U)
    (hΨode : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt (fun s ↦ Ψ (w, s)) (X (Ψ (w, t))) t)
    (hΘode : ∀ w ∈ B, ∀ t ∈ J, HasDerivAt (fun s ↦ Θ (w, s)) (X (Θ (w, t))) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I ∩ J) (heq : ∀ w ∈ B, Ψ (w, t₀) = Θ (w, t₀)) :
    ∃ Γ : W × ℝ → E,
      ContDiffOn ℝ 2 Γ (B ×ˢ (I ∪ J)) ∧ MapsTo Γ (B ×ˢ (I ∪ J)) U ∧
      (∀ w ∈ B, ∀ t ∈ I ∪ J,
        HasDerivAt (fun s ↦ Γ (w, s)) (X (Γ (w, t))) t) ∧
      EqOn Γ Ψ (B ×ˢ I) ∧ EqOn Γ Θ (B ×ˢ J) ∧
      (∀ z ∈ B ×ˢ I, fderiv ℝ Γ z = fderiv ℝ Ψ z) ∧
      (∀ z ∈ B ×ˢ J, fderiv ℝ Γ z = fderiv ℝ Θ z) := by
  classical
  have hcompat (w : W) (hw : w ∈ B) :
      EqOn (fun t ↦ Ψ (w, t)) (fun t ↦ Θ (w, t)) (I ∩ J) :=
    integralCurve_eqOn_of_contDiffOn hU hX (hI.inter hJ) hconn
      (fun t ht ↦ hΨmap ⟨hw, ht.1⟩) (fun t ht ↦ hΨode w hw t ht.1)
      (fun t ht ↦ hΘode w hw t ht.2) ht₀ (heq w hw)
  let Γ : W × ℝ → E := fun z ↦ if z.2 ∈ I then Ψ z else Θ z
  have hleft : EqOn Γ Ψ (B ×ˢ I) := by
    intro z hz
    simp only [Γ, hz.2, ite_true]
  have hright : EqOn Γ Θ (B ×ˢ J) := by
    intro z hz
    dsimp only [Γ]
    split_ifs with h
    · exact hcompat z.1 hz.1 ⟨h, hz.2⟩
    · rfl
  have hsm : ContDiffOn ℝ 2 Γ ((B ×ˢ I) ∪ (B ×ˢ J)) :=
    (hΨ.congr hleft).union_of_isOpen (hΘ.congr hright) (hB.prod hI) (hB.prod hJ)
  refine ⟨Γ, ?_, ?_, ?_, hleft, hright, ?_, ?_⟩
  · simpa only [prod_union] using hsm
  · intro z hz
    rcases hz.2 with hi | hj
    · rw [hleft ⟨hz.1, hi⟩]
      exact hΨmap ⟨hz.1, hi⟩
    · rw [hright ⟨hz.1, hj⟩]
      exact hΘmap ⟨hz.1, hj⟩
  · intro w hw t ht
    rcases ht with hi | hj
    · have he : (fun s ↦ Γ (w, s)) =ᶠ[𝓝 t] fun s ↦ Ψ (w, s) :=
        Filter.eventually_of_mem (hI.mem_nhds hi) (fun s hs ↦ hleft ⟨hw, hs⟩)
      rw [he.eq_of_nhds]
      exact (hΨode w hw t hi).congr_of_eventuallyEq he
    · have he : (fun s ↦ Γ (w, s)) =ᶠ[𝓝 t] fun s ↦ Θ (w, s) :=
        Filter.eventually_of_mem (hJ.mem_nhds hj) (fun s hs ↦ hright ⟨hw, hs⟩)
      rw [he.eq_of_nhds]
      exact (hΘode w hw t hj).congr_of_eventuallyEq he
  · intro z hz
    exact (hleft.eventuallyEq_of_mem ((hB.prod hI).mem_nhds hz)).fderiv_eq
  · intro z hz
    exact (hright.eventuallyEq_of_mem ((hB.prod hJ).mem_nhds hz)).fderiv_eq

end OTSelector.Geometry

end
