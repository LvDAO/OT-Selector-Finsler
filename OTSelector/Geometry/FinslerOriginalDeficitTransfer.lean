import OTSelector.Geometry.FinslerStationaryPhaseAction
import OTSelector.Analysis.Calculus.SecondJetTransfer

/-!
# Original potential deficit from the same stationary phase action

Matching full phase jets transfer the stationary action on the allowed parameter set.
The exact original potential clocks and the initial second-order remainder then give
second-order agreement with the smooth distance defect, retaining the original cost.
-/

open Set Filter Manifold Asymptotics
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Matching allowed phase jets and the original clocks transfer the stationary action
into a second-order comparison of the original-potential and smooth distance defects. -/
theorem original_deficit_sub_smooth_isLittleO_of_phaseAction
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
    (hPG : (fun x ↦ P x - G x) =o[𝓝 z₀.1] fun x ↦ ‖x - z₀.1‖ ^ 2)
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
      =o[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
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
  have hrem₁ := quadratic_remainder_comp_isLittleO_within hPG
    hR₁.fst.differentiableWithinAt (congrArg Prod.fst hR0)
  have hrem₂ := quadratic_remainder_comp_isLittleO_within hPG
    hR₂.fst.differentiableWithinAt (congrArg Prod.fst hR0)
  have hsmall := hA.sub (hrem₁.sub hrem₂)
  have hbound : (fun q : W × W ↦ ‖q - (0, 0)‖ ^ 2)
      =O[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
    apply isBigO_of_le
    intro q
    change ‖‖q - (0 : W × W)‖ ^ 2‖ ≤ ‖‖q.1‖ ^ 2 + ‖q.2‖ ^ 2‖
    rw [sub_zero, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)), Prod.norm_def]
    rcases le_total ‖q.1‖ ‖q.2‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (sq_nonneg _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (sq_nonneg _)
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
  apply (hsmall.trans_isBigO hbound).congr' ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [hboth] with q hq
  dsimp only [A, phaseLengthAction]
  rw [hq.1.1, hq.2.1.1, hq.2.2.1.1, hq.2.2.2.1,
    hq.2.2.1.2, hq.2.2.2.2, hq.1.2, hq.2.1.2]
  ring

end OTSelector.Geometry.ContinuousFinslerNorm
