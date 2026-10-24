import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Geometry.CalibratedLevelCylinder

## Lemma skeleton

* **Conditions:** A C1 injective local level section, a jointly Lipschitz local translation with fixed-time injectivity, a closed contact core and the stated scalar clock identity.

* **Objects:** A measurable calibrated time×level cylinder with a Lipschitz and injective coordinate map on the contact part.

* **Proof detail:** Shrink the section neighborhood into the spatial ball and obtain its local Lipschitz bound. Compose with the given joint Lipschitz map. Equal outputs first give equal times by the scalar clock identity, then equal labels by the two injectivity assumptions; closed-core preimages give measurability.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=46): Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=201): Section 6.2, Lemma 6.2 and proof, pp. 190–191 (straightening out of vector fields).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106): Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.

Source relation (composition): A locally proved cylinder construction from explicitly supplied clock and translation data. It is not a theorem deriving those data from an arbitrary vector field or Finsler metric.
-/

/-!
# Measurable calibrated time and level cylinders

A C1 injective section of a potential level combines with a jointly Lipschitz
translation into a Lipschitz time-label map. The original potential identifies
time on the closed contact core, so fixed-time injectivity identifies the label.
Injectivity is asserted only on the measurable contact cylinder.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W]

/-- Restrict a C1 level section to a label ball on which the actual time-label map
is jointly Lipschitz and its contact cylinder is measurable and injective. -/
theorem exists_calibrated_levelCylinder
    {σ : W → E} {B : Set W} {x₀ : E} {K : Set E} {ψ : E → ℝ}
    {T : ℝ × E → E} {r τ : ℝ} {C : ℝ≥0}
    (hB : IsOpen B) (h0 : (0 : W) ∈ B) (hσ : ContDiffOn ℝ 1 σ B)
    (hσ0 : σ 0 = x₀) (hinj : InjOn σ B) (hK : IsClosed K) (hr : 0 < r)
    (hT : LipschitzOnWith C T (Icc (-τ) τ ×ˢ closedBall x₀ r))
    (hfixed : ∀ t ∈ Icc (-τ) τ, InjOn (fun x ↦ T (t, x)) (closedBall x₀ r))
    (hclock : ∀ t ∈ Icc (-τ) τ, ∀ x ∈ K ∩ closedBall x₀ r,
      ψ (T (t, x)) = ψ x + t)
    (hlevel : ∀ w ∈ B, σ w ∈ K → ψ (σ w) = ψ x₀) :
    ∃ a : ℝ, ∃ L : ℝ≥0, 0 < a ∧ ball 0 a ⊆ B ∧
      MapsTo σ (ball 0 a) (ball x₀ r) ∧
      LipschitzOnWith L (fun q : ℝ × W ↦ T (q.1, σ q.2))
        (Ioo (-τ) τ ×ˢ ball 0 a) ∧
      (∀ q ∈ Ioo (-τ) τ ×ˢ (ball 0 a ∩ σ ⁻¹' K),
        ψ (T (q.1, σ q.2)) = ψ x₀ + q.1) ∧
      InjOn (fun q : ℝ × W ↦ T (q.1, σ q.2))
        (Ioo (-τ) τ ×ˢ (ball 0 a ∩ σ ⁻¹' K)) ∧
      MeasurableSet (Ioo (-τ) τ ×ˢ (ball 0 a ∩ σ ⁻¹' K)) ∧
      Ioo (-τ) τ ×ˢ (ball 0 a ∩ σ ⁻¹' K) ⊆ Ioo (-τ) τ ×ˢ ball 0 a := by
  have hσat : ContDiffAt ℝ 1 σ 0 := (hσ 0 h0).contDiffAt (hB.mem_nhds h0)
  obtain ⟨A, S, hS, hLip⟩ := hσat.exists_lipschitzOnWith
  have hpre : σ ⁻¹' ball x₀ r ∈ 𝓝 (0 : W) :=
    hσat.continuousAt.preimage_mem_nhds (hσ0 ▸ ball_mem_nhds x₀ hr)
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hS (inter_mem (hB.mem_nhds h0) hpre))
  have haS : ball (0 : W) a ⊆ S := fun w hw ↦ (has hw).1
  have haB : ball (0 : W) a ⊆ B := fun w hw ↦ (has hw).2.1
  have hmap : MapsTo σ (ball 0 a) (ball x₀ r) := fun w hw ↦ (has hw).2.2
  have hσLip : LipschitzOnWith A σ (ball 0 a) := hLip.mono haS
  have hseed : LipschitzOnWith (max 1 A)
      (fun q : ℝ × W ↦ (q.1, σ q.2)) (Ioo (-τ) τ ×ˢ ball 0 a) := by
    simpa only [mul_one, Function.comp_apply] using
      (LipschitzWith.prod_fst.lipschitzOnWith).prodMk
        (hσLip.comp LipschitzWith.prod_snd.lipschitzOnWith (fun q hq ↦ hq.2))
  have htime : ∀ t ∈ Ioo (-τ) τ, t ∈ Icc (-τ) τ := fun _ ht ↦ ⟨ht.1.le, ht.2.le⟩
  have hmaps : MapsTo (fun q : ℝ × W ↦ (q.1, σ q.2))
      (Ioo (-τ) τ ×ˢ ball 0 a) (Icc (-τ) τ ×ˢ closedBall x₀ r) :=
    fun q hq ↦ ⟨htime q.1 hq.1, ball_subset_closedBall (hmap hq.2)⟩
  have hXclock : ∀ q ∈ Ioo (-τ) τ ×ˢ (ball 0 a ∩ σ ⁻¹' K),
      ψ (T (q.1, σ q.2)) = ψ x₀ + q.1 := by
    intro q hq
    rw [hclock q.1 (htime q.1 hq.1) (σ q.2)
      ⟨hq.2.2, ball_subset_closedBall (hmap hq.2.1)⟩,
      hlevel q.2 (haB hq.2.1) hq.2.2]
  have hXinj : InjOn (fun q : ℝ × W ↦ T (q.1, σ q.2))
      (Ioo (-τ) τ ×ˢ (ball 0 a ∩ σ ⁻¹' K)) := by
    intro q hq p hp heq
    have ht : q.1 = p.1 := add_left_cancel
      ((hXclock q hq).symm.trans ((congrArg ψ heq).trans (hXclock p hp)))
    apply Prod.ext ht
    apply hinj (haB hq.2.1) (haB hp.2.1)
    apply hfixed q.1 (htime q.1 hq.1)
      (ball_subset_closedBall (hmap hq.2.1)) (ball_subset_closedBall (hmap hp.2.1))
    simpa only [ht] using heq
  have hopen : IsOpen (ball (0 : W) a ∩ σ ⁻¹' Kᶜ) :=
    (hσ.continuousOn.mono haB).isOpen_inter_preimage isOpen_ball hK.isOpen_compl
  have hmeas : MeasurableSet (ball (0 : W) a ∩ σ ⁻¹' K) := by
    have heq : ball (0 : W) a ∩ σ ⁻¹' K =
        ball (0 : W) a \ (ball (0 : W) a ∩ σ ⁻¹' Kᶜ) := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [heq]
    exact isOpen_ball.measurableSet.diff hopen.measurableSet
  exact ⟨a, C * max 1 A, ha, haB, hmap, hT.comp hseed hmaps,
    hXclock, hXinj, isOpen_Ioo.measurableSet.prod hmeas, fun _ hq ↦ ⟨hq.1, hq.2.1⟩⟩

end OTSelector.Geometry
