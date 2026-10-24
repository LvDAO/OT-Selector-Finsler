import OTSelector.Geometry.FinslerIntrinsicCostCoefficientFlow
import OTSelector.Geometry.FinslerPhaseJetHessianTransfer
import OTSelector.Geometry.Finsler.SeedKernelMeasurability

/-!
# Exact first jets and intrinsic coefficients under original label translation

Centering the actual seed at a label changes neither its derivative nor the fixed
label basis. The original Hessian is identified with a smooth centered family using
actual phase derivatives at the two corresponding points.
-/

open Set Filter Manifold Module
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual centered phase derivative is the original derivative at its label. -/
theorem chartMomentum_hasFDerivAt_of_label_add (old : M) {Γ : W → ℝ → M}
    (w : W) (t : ℝ) {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h : HasFDerivAt (F.chartMomentumFamily old (fun z ↦ Γ (w + z))) D (0, t)) :
    HasFDerivAt (F.chartMomentumFamily old Γ) D (w, t) := by
  have h' : HasFDerivAt (F.chartMomentumFamily old (fun z ↦ Γ (w + z))) D
      ((w, t) - (w, 0)) := by
    change HasFDerivAt _ D (w - w, t - 0)
    simpa only [sub_self, sub_zero] using h
  have hd := h'.comp (w, t) ((hasFDerivAt_id (w, t)).sub_const (w, 0))
  simpa [Function.comp_def, chartMomentumFamily] using! hd

/-- Equal actual phase jets at two label anchors give the same fixed-basis chart matrix. -/
theorem chartFamilyLabelHessianMatrix_eq_of_phase_jets_at (F : ContinuousFinslerNorm E M)
    (old : M) (bW : Basis ι ℝ W) {Γ₁ Γ₂ : W → ℝ → M} {q₁ q₂ : W × ℝ}
    {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (hvalue : Γ₁ q₁.1 q₁.2 = Γ₂ q₂.1 q₂.2)
    (h₁ : HasFDerivAt (F.chartMomentumFamily old Γ₁) D q₁)
    (h₂ : HasFDerivAt (F.chartMomentumFamily old Γ₂) D q₂) :
    F.chartFamilyLabelHessianMatrix old bW
      (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ₁ q.1 q.2)) q₁ =
    F.chartFamilyLabelHessianMatrix old bW
      (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ₂ q.1 q.2)) q₂ := by
  have hD₁ : fderiv ℝ (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ₁ q.1 q.2)) q₁ =
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp D := h₁.fst.fderiv
  have hD₂ : fderiv ℝ (fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ₂ q.1 q.2)) q₂ =
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp D := h₂.fst.fderiv
  simp only [chartFamilyLabelHessianMatrix, hD₁, hD₂, hvalue]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace CalibratedLevelSeedPatch

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Centered actual phase-jet agreement identifies the literal original Hessian
with the smooth normal family, without changing its label coordinates or time. -/
theorem familyLabelHessianMatrix_eq_centered_family {u : M → ℝ}
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ S.covector.ker) {w : S.covector.ker} (hw : w ∈ S.labels)
    {Γ : S.covector.ker → ℝ → M} (hcurve : S.curve w = Γ 0)
    {B : Set S.covector.ker} (hB : IsOpen B) (h0 : 0 ∈ B)
    (hG : ContMDiffOn 𝓘(ℝ, S.covector.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (henergy : ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ 0) ⟨t, (1 : ℝ)⟩) = 1 / 2)
    (t : ℝ)
    (hjet : ∀ old, Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old (fun z ↦ S.curve (w + z)))
        (fderiv ℝ (F.chartMomentumFamily old Γ) (0, t)) (0, t) ∧
      HasFDerivAt (F.chartMomentumFamily old Γ)
        (fderiv ℝ (F.chartMomentumFamily old Γ) (0, t)) (0, t)) :
    F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ Γ q.1 q.2) (0, t) := by
  let old := Γ 0 t
  have hx : Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source := mem_extChartAt_source _
  obtain ⟨h₁, h₂⟩ := hjet old hx
  have hOriginal := chartMomentum_hasFDerivAt_of_label_add old w t h₁
  have hd : MDifferentiableAt 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E)
      (fun q ↦ Γ q.1 q.2) (0, t) :=
    ((contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
      ((hB.prod isOpen_univ).mem_nhds ⟨h0, mem_univ _⟩)).mdifferentiableAt (by norm_num)
  have hs : HasFDerivAt (fun r : ℝ ↦ ((0 : S.covector.ker), r))
      (ContinuousLinearMap.inr ℝ S.covector.ker ℝ) t :=
    (hasFDerivAt_const (0 : S.covector.ker) t).prodMk (hasFDerivAt_id t)
  have hD := mfderiv_comp t hd hs.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hs.fderiv] at hD
  have hv : mfderiv 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E)
      (fun q ↦ Γ q.1 q.2) (0, t) (0, 1) ≠ 0 := by
    have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ 0) t 1 =
        mfderiv 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E)
          (fun q ↦ Γ q.1 q.2) (0, t) (0, 1) :=
      congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (Γ 0 t) ↦ L 1) hD
    intro hz
    have he := henergy t
    change F.fiberEnergy (Γ 0 t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ 0) t 1) = 1 / 2 at he
    rw [ht] at he
    rw [hz, F.fiberEnergy_zero] at he
    norm_num at he
  exact (S.chart_labelHessian_eq_intrinsic hF old bW hw
    (by rwa [hcurve])).symm.trans
      ((F.chartFamilyLabelHessianMatrix_eq_of_phase_jets_at old bW
        (congrFun hcurve t) hOriginal h₂).trans
          (hF.chartFamilyLabelHessianMatrix_eq_intrinsic old bW hd hx hv))

end CalibratedLevelSeedPatch
end OTSelector.Geometry.ContinuousFinslerNorm
