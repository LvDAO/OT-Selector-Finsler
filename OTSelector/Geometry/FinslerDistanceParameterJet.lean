import OTSelector.Geometry.Finsler.TubeCoordinateDistance

/-!
# Original distance jets along parameterized endpoints

The known jet in a genuine tube pulls back to arbitrary C2 endpoint maps. The local
inverse identities cancel both coordinate differentials, leaving the original
intrinsic endpoint covectors. The distance in the conclusion is the original cost.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original tube-distance jet gives C2 regularity and the intrinsic first variation
along any C2 pair of endpoint maps. The actual smooth inverse removes the coordinates. -/
theorem distance_comp_jet_of_manifoldTube (F : ContinuousFinslerNorm E M)
    {Y : OpenPartialHomeomorph (ℝ × W) M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    {q₀ : (ℝ × W) × (ℝ × W)} (ha : q₀.1 ∈ Y.source) (hb : q₀.2 ∈ Y.source)
    (pa : TangentSpace 𝓘(ℝ, E) (Y q₀.1) →L[ℝ] ℝ)
    (pb : TangentSpace 𝓘(ℝ, E) (Y q₀.2) →L[ℝ] ℝ)
    (hC2 : ContDiffAt ℝ 2 (F.tubeCoordinateDistance Y) q₀)
    (hd : HasFDerivAt (F.tubeCoordinateDistance Y)
      (pb.comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
        (fun q ↦ Y q.2) q₀) -
       pa.comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
        (fun q ↦ Y q.1) q₀)) q₀)
    {f g : P → M} {x₀ : P}
    (hf : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, E) 2 f x₀)
    (hg : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, E) 2 g x₀)
    (hfa : f x₀ = Y q₀.1) (hgb : g x₀ = Y q₀.2) :
    ContDiffAt ℝ 2 (fun x ↦ (F.lengthEDist (f x) (g x)).toReal) x₀ ∧
      HasFDerivAt (fun x ↦ (F.lengthEDist (f x) (g x)).toReal)
        (pb.comp (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, E) g x₀) -
          pa.comp (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, E) f x₀)) x₀ := by
  have hft : f x₀ ∈ Y.target := hfa ▸ Y.map_source ha
  have hgt : g x₀ ∈ Y.target := hgb ▸ Y.map_source hb
  let K : P → (ℝ × W) × (ℝ × W) := fun x ↦ (Y.symm (f x), Y.symm (g x))
  have hK : K x₀ = q₀ := by
    dsimp only [K]
    rw [hfa, hgb, Y.left_inv ha, Y.left_inv hb]
  have hKC : ContDiffAt ℝ 2 K x₀ :=
    (((hi.contMDiffAt (Y.open_target.mem_nhds hft)).of_le (by simp)).comp x₀ hf).contDiffAt
      |>.prodMk ((((hi.contMDiffAt (Y.open_target.mem_nhds hgt)).of_le
        (by simp)).comp x₀ hg).contDiffAt)
  have heq : (fun x ↦ (F.lengthEDist (f x) (g x)).toReal) =ᶠ[𝓝 x₀]
      F.tubeCoordinateDistance Y ∘ K := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hft),
      hg.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hgt)] with x hfx hgx
    simp only [Function.comp_apply, tubeCoordinateDistance, K,
      Y.right_inv hfx, Y.right_inv hgx]
  have hYa : MDifferentiableAt 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
      (fun q ↦ Y q.1) q₀ :=
    ((hY.contMDiffAt (Y.open_source.mem_nhds ha)).comp q₀
      (contDiffAt_fst (𝕜 := ℝ) (n := ∞)).contMDiffAt).mdifferentiableAt (by simp)
  have hYb : MDifferentiableAt 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
      (fun q ↦ Y q.2) q₀ :=
    ((hY.contMDiffAt (Y.open_source.mem_nhds hb)).comp q₀
      (contDiffAt_snd (𝕜 := ℝ) (n := ∞)).contMDiffAt).mdifferentiableAt (by simp)
  have hea : (fun q ↦ Y q.1) ∘ K =ᶠ[𝓝 x₀] f := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hft)]
      with x hx
    exact Y.right_inv hx
  have heb : (fun q ↦ Y q.2) ∘ K =ᶠ[𝓝 x₀] g := by
    filter_upwards [hg.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hgt)]
      with x hx
    exact Y.right_inv hx
  have hcha := (mfderiv_comp x₀ (hK.symm ▸ hYa)
    (hKC.contMDiffAt.mdifferentiableAt (by norm_num))).symm.trans hea.mfderiv_eq
  have hchb := (mfderiv_comp x₀ (hK.symm ▸ hYb)
    (hKC.contMDiffAt.mdifferentiableAt (by norm_num))).symm.trans heb.mfderiv_eq
  rw [hK, mfderiv_eq_fderiv] at hcha hchb
  rw [← hK] at hd hC2
  have hder := hd.comp x₀ (hKC.differentiableAt (by norm_num)).hasFDerivAt
  rw [hK, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc, hcha, hchb] at hder
  exact ⟨(hC2.comp x₀ hKC).congr_of_eventuallyEq heq, hder.congr_of_eventuallyEq heq⟩

end OTSelector.Geometry.ContinuousFinslerNorm
