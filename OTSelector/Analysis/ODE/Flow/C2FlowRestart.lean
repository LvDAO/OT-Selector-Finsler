import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import OTSelector.Analysis.ODE.Flow.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.C2FlowRestart.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.C2FlowRestart`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C2 initial seed and an actual restart flow with the stated common open parameter/time domains.

Objects: Time-shifted flow identity, common restart neighborhood and the initial actual differential.

Proof detail: Compose the same flow with the seed/time shift, shrink the common domain and differentiate the restart identity.

Sources: Gerald Teschl, Section 2.4, Theorem 2.9, pp. 44–45 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=55); Gerald Teschl, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Actual-flow restart adapter; it preserves the selected orbit.
-/

/-!
# Restarting an actual C2 flow with a varying seed

An autonomous local flow can be restarted at any time with an actual C2 seed.
Continuity constructs a common open parameter neighborhood in the original initial
ball. The same flow, shifted in time, retains joint C2 regularity, range and ODE;
its initial identity and true parameter derivative follow from the original flow.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry.LocalFlow

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A time-shifted restart of the same actual local flow accepts a varying C2 seed.
The common parameter neighborhood and its genuine initial derivative are constructed. -/
theorem IsLocalFlow.exists_c2Restart
    {X : E → E} {U : Set E} {p : E} {r : ℝ≥0} {τ T : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow (fun _ ↦ X) τ p r (τ - T) (τ + T) Φ)
    (hT : 0 < T)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)) U)
    (hC2 : ContDiffOn ℝ 2 Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)))
    {seed : W → E} {B : Set W} (hB : IsOpen B) (hseed : ContDiffOn ℝ 2 seed B)
    {w₀ : W} (hw₀ : w₀ ∈ B) (hp : seed w₀ ∈ ball p r) (s₀ : ℝ) :
    let Ψ : W × ℝ → E := fun q ↦ Φ (seed q.1, τ + (q.2 - s₀))
    ∃ B' : Set W, IsOpen B' ∧ w₀ ∈ B' ∧ B' ⊆ B ∧
      MapsTo seed B' (ball p r) ∧
      ContDiffOn ℝ 2 Ψ (B' ×ˢ Ioo (s₀ - T) (s₀ + T)) ∧
      MapsTo Ψ (B' ×ˢ Ioo (s₀ - T) (s₀ + T)) U ∧
      s₀ ∈ Ioo (s₀ - T) (s₀ + T) ∧
      (∀ w ∈ B', Ψ (w, s₀) = seed w) ∧
      (∀ w ∈ B', ∀ t ∈ Ioo (s₀ - T) (s₀ + T),
        HasDerivAt (fun s ↦ Ψ (w, s)) (X (Ψ (w, t))) t) ∧
      fderiv ℝ (fun w ↦ Ψ (w, s₀)) w₀ = fderiv ℝ seed w₀ := by
  let B' := B ∩ seed ⁻¹' ball p (r : ℝ)
  have hB' : IsOpen B' := hseed.continuousOn.isOpen_inter_preimage hB isOpen_ball
  have hw : w₀ ∈ B' := ⟨hw₀, hp⟩
  have hsub : B' ⊆ B := inter_subset_left
  have hs : MapsTo seed B' (ball p r) := fun w hw ↦ hw.2
  have htime (t : ℝ) (ht : t ∈ Ioo (s₀ - T) (s₀ + T)) :
      τ + (t - s₀) ∈ Ioo (τ - T) (τ + T) := by
    constructor <;> linarith [ht.1, ht.2]
  have hinit (w : W) (hw : w ∈ B') : Φ (seed w, τ + (s₀ - s₀)) = seed w := by
    simpa using hΦ.apply_initial (seed w) (ball_subset_closedBall (hs hw))
  refine ⟨B', hB', hw, hsub, hs, ?_, ?_, ⟨by linarith, by linarith⟩, hinit, ?_, ?_⟩
  · apply hC2.comp
      (((hseed.mono hsub).comp contDiffOn_fst (fun _ hz ↦ hz.1)).prodMk
        (contDiffOn_const.add (contDiffOn_snd.sub contDiffOn_const)))
    intro q hq
    exact ⟨ball_subset_closedBall (hs hq.1), Ioo_subset_Icc_self (htime q.2 hq.2)⟩
  · intro q hq
    exact hmap ⟨ball_subset_closedBall (hs hq.1), Ioo_subset_Icc_self (htime q.2 hq.2)⟩
  · intro w hw t ht
    have hd := (hΦ.hasDerivWithinAt (seed w) (ball_subset_closedBall (hs hw))
      (τ + (t - s₀)) (Ioo_subset_Icc_self (htime t ht))).hasDerivAt
        (Icc_mem_nhds (htime t ht).1 (htime t ht).2)
    have hshift := ((hasDerivAt_id t).sub_const s₀).const_add τ
    simpa only [Function.comp_def, one_smul, id_eq] using hd.scomp t hshift
  · have he : (fun w ↦ Φ (seed w, τ + (s₀ - s₀))) =ᶠ[𝓝 w₀] seed :=
      Filter.eventually_of_mem (hB'.mem_nhds hw) hinit
    exact he.fderiv_eq

end OTSelector.Geometry.LocalFlow

end
