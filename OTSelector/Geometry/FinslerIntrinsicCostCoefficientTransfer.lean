import OTSelector.Geometry.FinslerOriginalDeficitTransfer

/-!
# Actual distance-deficit transfer from the label potential remainder

The stationary phase action only needs quadratic agreement of the potential along
the actual original labels. No ambient second derivative or ambient Peano remainder
is required, and the allowed original endpoint set is retained.
-/

open Set Filter Manifold Asymptotics
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Matching initial state jets transfer the true original distance deficit using
only the quadratic-small potential error along the original labels. -/
theorem original_deficit_sub_smooth_isLittleO_of_label_phaseAction
    (F : ContinuousFinslerNorm E M) (old : M)
    (Phi : (E × E) → ℝ → M) (P G : E → ℝ) (u : M → ℝ)
    (a b c : ℝ) {z₀ : E × E} {S : Set W}
    {R N : W → E × E} {D : W →L[ℝ] E × E}
    (hActionC2 : ContDiffAt ℝ 2
      (F.phaseLengthAction old Phi P (a - c) (b - c)) (z₀, z₀))
    (hAction0 : HasFDerivAt
      (F.phaseLengthAction old Phi P (a - c) (b - c))
      (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) (z₀, z₀))
    (hR : HasFDerivWithinAt R D S 0)
    (hN : HasFDerivWithinAt N D S 0)
    (hR0 : R 0 = z₀) (hN0 : N 0 = z₀)
    (hPG : (fun w ↦ P (R w).1 - G (R w).1) =o[𝓝 (0 : W)] fun w ↦ ‖w‖ ^ 2)
    (hRdata : ∀ᶠ w in 𝓝[S] 0,
      (F.chartLength old (R w) : ℝ) = 1 ∧
      u (Phi (R w) (a - c)) = G (R w).1 + (a - c) ∧
      u (Phi (R w) (b - c)) = G (R w).1 + (b - c))
    (hNdata : ∀ᶠ w in 𝓝[S] 0,
      (F.chartLength old (N w) : ℝ) = 1 ∧ P (N w).1 = P z₀.1) :
    (fun q : W × W ↦
      ((F.lengthEDist (Phi (R q.1) (a - c))
          (Phi (R q.2) (b - c))).toReal -
        u (Phi (R q.2) (b - c)) + u (Phi (R q.1) (a - c))) -
      ((F.lengthEDist (Phi (N q.1) (a - c))
          (Phi (N q.2) (b - c))).toReal - (b - a)))
      =o[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q‖ ^ 2 := by
  let A := F.phaseLengthAction old Phi P (a - c) (b - c)
  have hfirst : ∀ᶠ y in 𝓝 (z₀, z₀), HasFDerivAt A (fderiv ℝ A y) y :=
    (hActionC2.eventually (by norm_num)).mono fun y hy ↦
      (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hsecond : DifferentiableAt ℝ (fderiv ℝ A) (z₀, z₀) :=
    (hActionC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hR₁ : HasFDerivWithinAt (fun q : W × W ↦ R q.1)
      (D.comp (ContinuousLinearMap.fst ℝ W W)) (S ×ˢ S) (0, 0) :=
    hR.comp (0, 0) hasFDerivWithinAt_fst (fun _ hq ↦ hq.1)
  have hR₂ : HasFDerivWithinAt (fun q : W × W ↦ R q.2)
      (D.comp (ContinuousLinearMap.snd ℝ W W)) (S ×ˢ S) (0, 0) :=
    hR.comp (0, 0) hasFDerivWithinAt_snd (fun _ hq ↦ hq.2)
  have hN₁ : HasFDerivWithinAt (fun q : W × W ↦ N q.1)
      (D.comp (ContinuousLinearMap.fst ℝ W W)) (S ×ˢ S) (0, 0) :=
    hN.comp (0, 0) hasFDerivWithinAt_fst (fun _ hq ↦ hq.1)
  have hN₂ : HasFDerivWithinAt (fun q : W × W ↦ N q.2)
      (D.comp (ContinuousLinearMap.snd ℝ W W)) (S ×ˢ S) (0, 0) :=
    hN.comp (0, 0) hasFDerivWithinAt_snd (fun _ hq ↦ hq.2)
  have hA := stationary_second_order_comp_sub_isLittleO_within
    hfirst hsecond.hasFDerivAt hAction0.fderiv (hR₁.prodMk hR₂) (hN₁.prodMk hN₂)
    (by simp only [hR0]) (by simp only [hN0])
  have hPG' : (fun w ↦ P (R w).1 - G (R w).1) =o[𝓝 (0 : W)]
      fun w ↦ ‖w - 0‖ ^ 2 := by simpa only [sub_zero] using hPG
  have hrem₁ := quadratic_remainder_comp_isLittleO_within hPG'
    (X := Prod.fst) (S := S ×ˢ S) (t := ((0 : W), 0)) differentiableWithinAt_fst rfl
  have hrem₂ := quadratic_remainder_comp_isLittleO_within hPG'
    (X := Prod.snd) (S := S ×ˢ S) (t := ((0 : W), 0)) differentiableWithinAt_snd rfl
  have hsmall := hA.sub (hrem₁.sub hrem₂)
  have hboth : ∀ᶠ q in 𝓝[S ×ˢ S] ((0 : W), 0),
      ((F.chartLength old (R q.1) : ℝ) = 1 ∧
        u (Phi (R q.1) (a - c)) = G (R q.1).1 + (a - c)) ∧
      ((F.chartLength old (R q.2) : ℝ) = 1 ∧
        u (Phi (R q.2) (b - c)) = G (R q.2).1 + (b - c)) ∧
      ((F.chartLength old (N q.1) : ℝ) = 1 ∧ P (N q.1).1 = P z₀.1) ∧
      ((F.chartLength old (N q.2) : ℝ) = 1 ∧ P (N q.2).1 = P z₀.1) := by
    rw [nhdsWithin_prod_eq]
    filter_upwards [Filter.Eventually.prod_mk (hRdata.and hNdata)
      (hRdata.and hNdata)] with q hq
    exact ⟨⟨hq.1.1.1, hq.1.1.2.1⟩, ⟨hq.2.1.1, hq.2.1.2.2⟩,
      hq.1.2, hq.2.2⟩
  have hsmall' : (fun q : W × W ↦ A (R q.1, R q.2) - A (N q.1, N q.2) -
      ((P (R q.1).1 - G (R q.1).1) - (P (R q.2).1 - G (R q.2).1)))
      =o[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q‖ ^ 2 := by
    simpa only [show ((0 : W), 0) = (0 : W × W) from rfl, sub_zero] using hsmall
  apply hsmall'.congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [hboth] with q hq
  dsimp only [A, phaseLengthAction]
  rw [hq.1.1, hq.2.1.1, hq.2.2.1.1, hq.2.2.2.1,
    hq.2.2.1.2, hq.2.2.2.2, hq.1.2, hq.2.1.2]
  ring


end OTSelector.Geometry.ContinuousFinslerNorm
