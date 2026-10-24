import OTSelector.Analysis.Calculus.LocalSmoothExtension
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.JointC2
import OTSelector.Analysis.ODE.Flow.LocalC2
import OTSelector.Analysis.ODE.Flow.LocalVariational
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.SameFlowC2.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.SameFlowC2`; the selected original proof blocks follow. -/
section

/-!
Conditions: A given actual local autonomous flow solves a smooth vector field, with the stated local domain and initial conditions.

Objects: Joint C2 regularity of that same flow on a common closed box.

Proof detail: Use a smooth local extension only to apply regularity/uniqueness, identify it with the given flow and choose a common product neighborhood.

Sources: Gerald Teschl, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57); Gerald Teschl, Section 2.2, Theorem 2.2 and Lemma 2.3, pp. 38–39; Section 2.3, Theorem 2.5, pp. 40–41 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Local regularity of an existing flow; the extension is a proof tool and does not change the chosen trajectory.
-/

/-!
# Joint C2 regularity of a given local flow

A smooth autonomous field on an open set makes the same given local flow jointly C2
near its initial state and time. A smooth extension is only a regularity tool: the
function defining the flow is never replaced. A smaller positive closed box retains
the original field equation and lies in an open C2 neighborhood.
-/

open Set Filter Metric Function
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The same local flow of an open-domain smooth field is jointly C2 near a smaller
positive closed box, and retains its original field and range on that box. -/
theorem IsLocalFlow.exists_contDiffOn_C2_in_open
    {X : E → E} {U : Set E} {p : E} {r : ℝ≥0} {t₀ T : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow (fun _ ↦ X) t₀ p r (t₀ - T) (t₀ + T) Φ)
    (hr : 0 < r) (hT : 0 < T) (hU : IsOpen U) (hp : p ∈ U)
    (hX : ContDiffOn ℝ ∞ X U) :
    ∃ (r' : ℝ≥0) (T' : ℝ) (D : Set (E × ℝ)),
      0 < r' ∧ r' ≤ r ∧ 0 < T' ∧ T' ≤ T ∧ IsOpen D ∧
      closedBall p r' ×ˢ Icc (t₀ - T') (t₀ + T') ⊆ D ∧
      IsLocalFlow (fun _ ↦ X) t₀ p r' (t₀ - T') (t₀ + T') Φ ∧
      MapsTo Φ (closedBall p r' ×ˢ Icc (t₀ - T') (t₀ + T')) U ∧
      ContDiffOn ℝ 2 Φ D := by
  obtain ⟨V, Y, hV, hpV, hVU, hY, _, _, hYX⟩ :=
    exists_contDiff_compactlySupported_extension hU hp hX
  obtain ⟨r₁, T₁, hr₁, hr₁le, hT₁, hT₁le, hstay⟩ :=
    hΦ.exists_shrink_mapsTo hr hT hV hpV
  have hspace₁ : closedBall p (r₁ : ℝ) ⊆ closedBall p (r : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hr₁le)
  have htime₁ : Icc (t₀ - T₁) (t₀ + T₁) ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hΦY : IsLocalFlow (fun _ ↦ Y) t₀ p r₁ (t₀ - T₁) (t₀ + T₁) Φ := {
    minTime_le_initial := by linarith
    initial_le_maxTime := by linarith
    apply_initial := fun x hx ↦ hΦ.apply_initial x (hspace₁ hx)
    hasDerivWithinAt := fun x hx t ht ↦ by
      rw [hYX (hstay ⟨hx, ht⟩)]
      exact (hΦ.hasDerivWithinAt x (hspace₁ hx) t (htime₁ ht)).mono htime₁
    continuousOn := hΦ.continuousOn.mono (prod_mono hspace₁ htime₁)
    exists_lipschitz := by
      obtain ⟨K, hK⟩ := hΦ.exists_lipschitz
      exact ⟨K, fun t ht ↦ (hK t (htime₁ ht)).mono hspace₁⟩ }
  have hf : ContDiffOn ℝ 2 (uncurry (fun (_ : ℝ) ↦ Y)) univ :=
    ((hY.of_le (by simp : 2 ≤ ∞)).comp contDiff_snd).contDiffOn
  obtain ⟨D, hD, hpD, hC2⟩ := exists_contDiffOn_flow_C2 hΦY hf
    (by constructor <;> linarith) (show (0 : ℝ) < r₁ from hr₁)
  obtain ⟨r₂, T₂, hr₂, hr₂le, hT₂, hT₂le, hbox⟩ :=
    exists_pos_closed_flow_box_subset (hD.mem_nhds hpD) hr₁ hT₁
  have hspace₂ : closedBall p (r₂ : ℝ) ⊆ closedBall p (r₁ : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hr₂le)
  have htime₂ : Icc (t₀ - T₂) (t₀ + T₂) ⊆ Icc (t₀ - T₁) (t₀ + T₁) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hs := hspace₂.trans hspace₁
  have ht := htime₂.trans htime₁
  refine ⟨r₂, T₂, D, hr₂, hr₂le.trans hr₁le, hT₂, hT₂le.trans hT₁le,
    hD, hbox, ?_, fun q hq ↦ hVU (hstay ⟨hspace₂ hq.1, htime₂ hq.2⟩), hC2⟩
  exact {
    minTime_le_initial := by linarith
    initial_le_maxTime := by linarith
    apply_initial := fun x hx ↦ hΦ.apply_initial x (hs hx)
    hasDerivWithinAt := fun x hx t h ↦
      (hΦ.hasDerivWithinAt x (hs hx) t (ht h)).mono ht
    continuousOn := hΦ.continuousOn.mono (prod_mono hs ht)
    exists_lipschitz := by
      obtain ⟨K, hK⟩ := hΦ.exists_lipschitz
      exact ⟨K, fun t h ↦ (hK t (ht h)).mono hs⟩ }

end OTSelector.Geometry.LocalFlow

end
end
