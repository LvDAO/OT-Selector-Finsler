import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Closed-set derivative gluing and compact cutoffs

Main declarations: lipschitzWith_of_closed_set_of_fderiv_bound; exists_compact_cutoff_lipschitz_fderiv.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.DerivativeLipschitzGluing`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Real normed domain/target without completeness or finite dimension; a continuous map on a convex domain, closed K, Lipschitz trace on K and actual derivative bound on its complement.
* **Objects:** A Lipschitz estimate on the whole convex domain, and its global version with constant max(trace bound, complement bound).
* **Proof detail:** Parametrize a segment and take its first and last encounters with K. Mean value and endpoint continuity control the two outside pieces; the trace Lipschitz bound controls the middle piece.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
  https://www.jirka.org/ra/realanal2.pdf#page=46

**Relationship to the sources:** A normed-space closed-set refinement of the bounded-derivative mean-value estimate, proved directly and later applied to the actual derivative field.
-/

/-!
# Lipschitz gluing across a closed set

A continuous map on a convex domain is Lipschitz when its trace on a closed set is
Lipschitz and its derivative on the complement obeys the same bound. Along each segment,
use its first and last intersections with the closed set. The two outside pieces are
controlled by the mean value theorem and continuity at their endpoints; the middle
piece is controlled directly by the trace. Neither finite dimension nor completeness
is required. Applying this to the derivative field closes the C1,1 extension step.
-/

open Set Filter Metric
open scoped Topology NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem dist_endpoints_le_of_deriv_bound_Ioo
    {g g' : ℝ → F} {a b : ℝ} {C : ℝ≥0} (hab : a ≤ b)
    (hc : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t)
    (hb : ∀ t ∈ Ioo a b, ‖g' t‖ ≤ C) :
    dist (g b) (g a) ≤ C * (b - a) := by
  obtain hab | rfl := hab.lt_or_eq
  · have hl : LipschitzOnWith C g (Ioo a b) :=
      (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun t ht ↦ (hd t ht).hasDerivWithinAt) (fun t ht ↦ hb t ht)
    have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
    have hlc : LipschitzOnWith C g (Icc a b) := by
      rw [← hcl]
      exact LipschitzOnWith.closure (by rwa [hcl]) hl
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab.le)] using
      hlc.dist_le_mul b (right_mem_Icc.mpr hab.le) a (left_mem_Icc.mpr hab.le)
  · simp

/-- A closed-set Lipschitz trace and a bound on the actual derivative off that set
combine into the same Lipschitz bound on any convex domain. Only continuity on the
domain is required at points of the closed set. -/
theorem lipschitzOnWith_of_closed_set_of_fderiv_bound
    {H : E → F} {Ω K : Set E} {L : ℝ≥0}
    (hΩ : Convex ℝ Ω) (hK : IsClosed K) (hH : ContinuousOn H Ω)
    (hLip : LipschitzOnWith L H (Ω ∩ K))
    (hd : ∀ x ∈ Ω \ K, DifferentiableAt ℝ H x)
    (hbound : ∀ x ∈ Ω \ K, ‖fderiv ℝ H x‖ ≤ L) :
    LipschitzOnWith L H Ω := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let γ : ℝ → E := AffineMap.lineMap x y
  let g : ℝ → F := H ∘ γ
  let g' : ℝ → F := fun t ↦ fderiv ℝ H (γ t) (y - x)
  let C : ℝ≥0 := L * ‖y - x‖₊
  have hγ : Continuous γ := (lipschitzWith_lineMap x y).continuous
  have hmem (t) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω := hΩ.lineMap_mem hx hy ht
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := hH.comp hγ.continuousOn hmem
  have hder (t) (ht : t ∈ Icc (0 : ℝ) 1) (hk : γ t ∉ K) :
      HasDerivAt g (g' t) t :=
    (hd (γ t) ⟨hmem t ht, hk⟩).hasFDerivAt.comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap
  have hnorm (t) (ht : t ∈ Icc (0 : ℝ) 1) (hk : γ t ∉ K) : ‖g' t‖ ≤ C := by
    exact (fderiv ℝ H (γ t)).le_opNorm (y - x) |>.trans
      (mul_le_mul_of_nonneg_right (hbound (γ t) ⟨hmem t ht, hk⟩) (norm_nonneg _))
  let A : Set ℝ := Icc 0 1 ∩ γ ⁻¹' K
  have hA : IsCompact A := isCompact_Icc.inter_right (hK.preimage hγ)
  have htotal : dist (g 1) (g 0) ≤ C := by
    by_cases hne : A.Nonempty
    · obtain ⟨a, ha⟩ := hA.exists_isLeast hne
      obtain ⟨b, hb⟩ := hA.exists_isGreatest hne
      have ha01 : a ∈ Icc (0 : ℝ) 1 := ha.1.1
      have hb01 : b ∈ Icc (0 : ℝ) 1 := hb.1.1
      have hab : a ≤ b := ha.2 hb.1
      have hleft : dist (g a) (g 0) ≤ C * a := by
        have hout (t) (ht : t ∈ Ioo (0 : ℝ) a) : γ t ∉ K := by
          intro hk
          have hat : a ≤ t := ha.2 ⟨⟨ht.1.le, ht.2.le.trans ha01.2⟩, hk⟩
          exact (not_le_of_gt ht.2) hat
        simpa only [sub_zero] using dist_endpoints_le_of_deriv_bound_Ioo ha01.1
          (hg.mono (Icc_subset_Icc le_rfl ha01.2))
          (fun t ht ↦ hder t ⟨ht.1.le, ht.2.le.trans ha01.2⟩ (hout t ht))
          (fun t ht ↦ hnorm t ⟨ht.1.le, ht.2.le.trans ha01.2⟩ (hout t ht))
      have hright : dist (g 1) (g b) ≤ C * (1 - b) := by
        have hout (t) (ht : t ∈ Ioo b (1 : ℝ)) : γ t ∉ K := by
          intro hk
          have htb : t ≤ b := hb.2 ⟨⟨hb01.1.trans ht.1.le, ht.2.le⟩, hk⟩
          exact (not_le_of_gt ht.1) htb
        exact dist_endpoints_le_of_deriv_bound_Ioo hb01.2
          (hg.mono (Icc_subset_Icc hb01.1 le_rfl))
          (fun t ht ↦ hder t ⟨hb01.1.trans ht.1.le, ht.2.le⟩ (hout t ht))
          (fun t ht ↦ hnorm t ⟨hb01.1.trans ht.1.le, ht.2.le⟩ (hout t ht))
      have hmiddle : dist (g b) (g a) ≤ C * (b - a) := by
        calc
          dist (g b) (g a) ≤ L * dist (γ b) (γ a) :=
            hLip.dist_le_mul (γ b) ⟨hmem b hb01, hb.1.2⟩ (γ a) ⟨hmem a ha01, ha.1.2⟩
          _ = C * (b - a) := by
            dsimp only [γ, C]
            rw [dist_lineMap_lineMap, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hab)]
            simp only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm']
            ring
      have htri := dist_triangle4 (g 1) (g b) (g a) (g 0)
      nlinarith
    · have hout (t) (ht : t ∈ Ioo (0 : ℝ) 1) : γ t ∉ K := by
        intro hk
        exact hne ⟨t, ⟨ht.1.le, ht.2.le⟩, hk⟩
      simpa only [sub_zero, mul_one] using dist_endpoints_le_of_deriv_bound_Ioo zero_le_one hg
        (fun t ht ↦ hder t ⟨ht.1.le, ht.2.le⟩ (hout t ht))
        (fun t ht ↦ hnorm t ⟨ht.1.le, ht.2.le⟩ (hout t ht))
  simpa only [g, γ, Function.comp_apply, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero, C, NNReal.coe_mul, coe_nnnorm, ← dist_eq_norm',
    dist_comm (H y) (H x)] using htotal

/-- Global Lipschitz gluing, allowing separate constants for the trace and the derivative
on the complement. Applied to a continuous derivative field, this yields a global C1,1
bound without assuming Lipschitz regularity of that field away from the closed set. -/
theorem lipschitzWith_of_closed_set_of_fderiv_bound
    {H : E → F} {K : Set E} {L C : ℝ≥0}
    (hK : IsClosed K) (hH : Continuous H) (hLip : LipschitzOnWith L H K)
    (hd : ∀ x ∉ K, DifferentiableAt ℝ H x)
    (hbound : ∀ x ∉ K, ‖fderiv ℝ H x‖ ≤ C) :
    LipschitzWith (max L C) H := by
  rw [← lipschitzOnWith_univ]
  apply lipschitzOnWith_of_closed_set_of_fderiv_bound convex_univ hK hH.continuousOn
  · simpa only [univ_inter] using hLip.weaken (le_max_left L C)
  · intro x hx
    exact hd x hx.2
  · intro x hx
    exact (hbound x hx.2).trans (NNReal.coe_le_coe.mpr (le_max_right L C))

end OTSelector.Geometry

end
end

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.CompactCutoff`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional real normed domain, arbitrary real normed target; actual C1 map smooth off a compact K, Lipschitz derivative trace on K and a uniform nearby true Hessian bound.
* **Objects:** A constructed smooth compact cutoff and compactly supported C1 map preserving both values and actual derivative on K, with globally Lipschitz actual derivative.
* **Proof detail:** Choose a bump equal to one on a neighborhood of K. Preserve the jet by eventual equality; bound the actual Hessian near K using the premise and on the remaining compact support using continuity. Glue derivative Lipschitz estimates across K.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
  https://www.jirka.org/ra/realanal2.pdf#page=46
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
  https://www.jirka.org/ra/realanal2.pdf#page=37

**Relationship to the sources:** This combines smooth localization from Whitney construction with a locally proved mean-value/gluing argument. The existence of the final cutoff and derivative constant are conclusions, not extra supplied data.
-/

/-!
# Compact cutoff preserving a Whitney first jet

A smooth bump equal to one around a compact set turns an actual C1 extension with a
near-set Hessian bound into a compactly supported C1,1 extension. Near the compact set,
the cutoff has no effect on either derivative. Away from the set, continuity bounds
the actual Hessian on the remaining compact support. Closed-set Lipschitz gluing then
bounds the global derivative. The cutoff, its derivative bound, and the final Lipschitz
constant are constructed; none is supplied as an assumption.
-/

open Set Filter Metric Function
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance whitneyCutoffHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance whitneyCutoffHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

/-- An actual smooth compact cutoff preserves the value and derivative on a compact
set and upgrades a uniform nearby Hessian bound to global Lipschitz regularity of the
derivative. The target need not be finite-dimensional or complete. -/
theorem exists_compact_cutoff_lipschitz_fderiv
    {G : E → F} {K : Set E} {L : ℝ≥0} {δ A : ℝ}
    (hK : IsCompact K) (hG : ContDiff ℝ 1 G) (hOff : ContDiffOn ℝ ∞ G Kᶜ)
    (hLip : LipschitzOnWith L (fderiv ℝ G) K) (hδ : 0 < δ)
    (hnear : ∀ x ∉ K, infDist x K < δ → ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ A) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ K, η =ᶠ[𝓝 x] fun _ ↦ 1) ∧
      let H : E → F := fun x ↦ η x • G x
      ContDiff ℝ 1 H ∧ HasCompactSupport H ∧ ContDiffOn ℝ ∞ H Kᶜ ∧
      EqOn H G K ∧ EqOn (fderiv ℝ H) (fderiv ℝ G) K ∧
      ∃ C : ℝ≥0, LipschitzWith C (fderiv ℝ H) := by
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  let β : ContDiffBump (0 : E) :=
    ⟨R + δ + 1, R + δ + 2, by linarith, by linarith⟩
  let H : E → F := fun x ↦ β x • G x
  have hH : ContDiff ℝ 1 H := β.contDiff.smul hG
  have hsupport : HasCompactSupport H := β.hasCompactSupport.smul_right
  have hHOff : ContDiffOn ℝ ∞ H Kᶜ := β.contDiff.contDiffOn.smul hOff
  have hηNear (x) (hx : x ∈ K) : (β : E → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := by
    apply β.eventuallyEq_one_of_mem_ball
    change dist x 0 < R + δ + 1
    rw [dist_zero_right]
    linarith [hRK x hx]
  have hHG (x) (hx : x ∈ K) : H =ᶠ[𝓝 x] G := by
    filter_upwards [hηNear x hx] with y hy
    simp only [H, hy, one_smul]
  have hvalue : EqOn H G K := fun x hx ↦ (hHG x hx).self_of_nhds
  have hderiv : EqOn (fderiv ℝ H) (fderiv ℝ G) K := fun x hx ↦ (hHG x hx).fderiv_eq
  have hHsmooth (x) (hx : x ∉ K) : ContDiffAt ℝ ∞ H x :=
    hHOff.contDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ H)) Kᶜ := by
    intro x hx
    exact (((hHsmooth x hx).fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞)
      (by simp)).continuousAt.continuousWithinAt
  have hglobal : ∃ B : ℝ, ∀ x ∉ K, ‖fderiv ℝ (fderiv ℝ H) x‖ ≤ B := by
    by_cases hne : K.Nonempty
    · let S : Set E := tsupport H ∩ {x | δ ≤ infDist x K}
      have hS : IsCompact S := hsupport.inter_right
        (isClosed_le continuous_const (continuous_infDist_pt K))
      have hSK : S ⊆ Kᶜ := by
        intro x hx hmem
        have hz := infDist_zero_of_mem hmem
        exact hδ.not_ge (hz ▸ hx.2)
      obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (hD2.mono hSK)
      refine ⟨max 0 (max A B), ?_⟩
      intro x hx
      by_cases hs : x ∈ tsupport H
      · by_cases hdist : infDist x K < δ
        · obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).mp hdist
          have hball : x ∈ ball (0 : E) β.rIn := by
            change dist x 0 < R + δ + 1
            have ht := dist_triangle x y 0
            simp only [dist_zero_right] at ht
            rw [dist_zero_right]
            linarith [hRK y hy]
          have hEq : H =ᶠ[𝓝 x] G := by
            filter_upwards [β.eventuallyEq_one_of_mem_ball hball] with z hz
            simp only [H, hz, Pi.one_apply, one_smul]
          rw [hEq.fderiv.fderiv_eq]
          exact (hnear x hx hdist).trans ((le_max_left A B).trans (le_max_right _ _))
        · exact (hB x ⟨hs, le_of_not_gt hdist⟩).trans
            ((le_max_right A B).trans (le_max_right _ _))
      · rw [fderiv_of_notMem_tsupport ℝ
          (fun hz ↦ hs (tsupport_fderiv_subset ℝ hz)), norm_zero]
        exact le_max_left _ _
    · have he : K = ∅ := not_nonempty_iff_eq_empty.mp hne
      have hsmooth : ContDiff ℝ ∞ H := by
        simpa only [he, compl_empty, contDiffOn_univ] using hHOff
      obtain ⟨B, hB⟩ := ((hsupport.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous
        ((hsmooth.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
      exact ⟨B, fun x _ ↦ hB x⟩
  obtain ⟨B, hB⟩ := hglobal
  let Cbound : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  have hbound (x) (hx : x ∉ K) : ‖fderiv ℝ (fderiv ℝ H) x‖ ≤ Cbound :=
    (hB x hx).trans (le_max_right _ _)
  have htrace : LipschitzOnWith L (fderiv ℝ H) K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hderiv hx, hderiv hy]
    exact hLip.dist_le_mul x hx y hy
  have hdiff (x) (hx : x ∉ K) : DifferentiableAt ℝ (fderiv ℝ H) x :=
    ((hHsmooth x hx).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  refine ⟨β, β.contDiff, β.hasCompactSupport, (fun x ↦ ⟨β.nonneg, β.le_one⟩),
    hηNear, hH, hsupport, hHOff, hvalue, hderiv, max L Cbound, ?_⟩
  exact lipschitzWith_of_closed_set_of_fderiv_bound hK.isClosed
    (hH.continuous_fderiv one_ne_zero) htrace hdiff hbound

end OTSelector.Geometry

end
end
