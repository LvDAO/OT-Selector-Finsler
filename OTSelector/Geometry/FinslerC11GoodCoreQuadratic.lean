import OTSelector.Geometry.FinslerC11OriginalQuadratic
import OTSelector.Geometry.Finsler.C11LevelCoordinates
import OTSelector.Geometry.FinslerTubeKernelCompliance

/-!
# Original good-core expansion with the actual length-Hessian integral

The actual good-core data supply their own matched smooth family and original
potential-level coordinates. The original deficit has the inverse of the integral
of restricted length-Hessian inverses along the original complete central curve.
-/

open Set Filter Metric MeasureTheory Manifold Bundle Asymptotics
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- An actual original good core supplies its own level coordinates and smooth tube.
The original deficit has the inverse-integral restricted length-Hessian coefficient
along the original central curve; no selected smooth-family witnesses are inputs. -/
theorem exists_original_length_quadratic_of_good_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) {K : Set E}
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ y ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {A : E → ℝ → M}
    (hA : ∀ y ∈ K,
      A y 0 = (extChartAt 𝓘(ℝ, E) old).symm y ∧
      F.IsEulerLagrangeOn (A y) univ ∧
      F.chartMomentumFamily old A (y, 0) = (y, fderiv ℝ G y))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {x : E} (hgood : F.HasC11PotentialFamilyAt m old 0 u G K x)
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    {a b : ℝ} (hab : a < b)
    (hseg : Icc (a - G x) (b - G x) ⊆ Ioo (-δ) δ) :
    let p := fderiv ℝ G x
    let c := G x
    ∃ eG : OpenPartialHomeomorph E (ℝ × p.ker),
      x ∈ eG.source ∧ eG.source ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ContDiffOn ℝ 1 eG eG.source ∧ ContDiffOn ℝ 1 eG.symm eG.target ∧
      eG x = (c, 0) ∧ (∀ y : E, (eG y).1 = G y) ∧
      let σ : p.ker → E := fun w ↦ eG.symm (c, w)
      let B := {w : p.ker | (c, w) ∈ eG.target}
      let S := B ∩ σ ⁻¹' K
      IsOpen B ∧ (0 : p.ker) ∈ B ∧ ContDiffOn ℝ 1 σ B ∧ σ 0 = x ∧
      HasFDerivAt σ p.ker.subtypeL 0 ∧
      σ '' S = eG.source ∩ K ∩
        {y | u ((extChartAt 𝓘(ℝ, E) old).symm y) =
          u ((extChartAt 𝓘(ℝ, E) old).symm x)} ∧
      ∃ (Γ : p.ker → ℝ → M) (Y : OpenPartialHomeomorph (ℝ × p.ker) M),
        A x = Γ 0 ∧
        ContMDiffOn 𝓘(ℝ, ℝ × p.ker) 𝓘(ℝ, E) ∞ Y Y.source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × p.ker) ∞ Y.symm Y.target ∧
        (Y : ℝ × p.ker → M) = (fun q ↦ Γ q.2 q.1) ∧
        (∀ q ∈ Y.source,
          F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2) ∧
        (∀ y ∈ Y.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
          @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 0) y z)
            (F.toFun ⟨y, z⟩ : ℝ)) ∧
        (∀ t ∈ Icc (a - c) (b - c), (t, (0 : p.ker)) ∈ Y.source) ∧
        let τ := ContinuousLinearMap.fst ℝ ℝ p.ker
        let d : p.ker → τ.ker := fun w ↦ ⟨(0, w), by simp [τ]⟩
        let Q := F.tubeLengthKernelCompliance Y τ (A x) (a - c) (b - c)
        let X : ℝ → p.ker → M := fun r w ↦ A (σ w) (r - c)
        (fun q : p.ker × p.ker ↦
          ((F.lengthEDist (X a q.1) (X b q.2)).toReal -
            u (X b q.2) + u (X a q.1)) -
          (1 / 2 : ℝ) * Q.inverse (d (q.2 - q.1)) (d (q.2 - q.1)))
          =o[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2
 := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨hxK, _, _, hsecond, _, e, he, hsub, hInv, hp, P, hP, hPx, _, hPsecond,
    hDPactual, _, hdim, B₀, BP, σP, v, scale, Γ, U, _, hBP, h0P, hBPB₀, _, _,
    hσP, hσP0, hPlevel, hσPD, _, _, hv, _, hv0, hscale0, hstate, hΓEL, hΓinit,
    hm, _, henergy, _, _, _, hjet⟩ := hgood
  have hPxG : P x = G x := hPx.trans (hval hxK).symm
  have hDP : fderiv ℝ P x = fderiv ℝ G x :=
    hDPactual.trans (hactual x hxK).fderiv
  have hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K :=
    fun y hy ↦ (hactual y hy).fderiv.symm
  obtain ⟨_, eG, hxeG, hsourceG, heG, heiG, heGx, hfirstG, _, hσG, _,
      hBG, h0G, hσGC1, hσG0, himage⟩ :=
    hF.exists_original_levelCoordinates_of_calibrated_core hcomplete old hKt hu hG
      hval hmatch hδ hpartners hxK
  let σG : (fderiv ℝ G x).ker → E := fun w ↦ eG.symm (G x, w)
  let BG := {w : (fderiv ℝ G x).ker | (G x, w) ∈ eG.target}
  have hGlevel (w : (fderiv ℝ G x).ker) (hw : w ∈ BG) : G (σG w) = G x := by
    simpa only [hfirstG] using congrArg Prod.fst (eG.right_inv hw)
  have hdomain (w : (fderiv ℝ G x).ker) (hw : w ∈ BP) :
      (σP w, v w) ∈ chartEnergyDomain old := (hstate w hw).1
  have hΓsource (w : (fderiv ℝ G x).ker) (hw : w ∈ BP) :
      Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    have hb : Γ w 0 = (extChartAt 𝓘(ℝ, E) old).symm (σP w) := by
      have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hΓinit w hw)
      rw [tangentChart_symm_eq old (hdomain w hw).1] at h
      exact h
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hdomain w hw).1
  have hvalue : F.chartMomentumFamily old Γ (0, 0) = (x, fderiv ℝ G x) := by
    simpa only [potentialConormalState, hσP0, hscale0, one_smul, hDP] using hm 0 h0P
  have hcenter : A x = Γ 0 := (hcmp BP Γ hBP h0P hΓEL hΓsource hjet hvalue).1
  obtain ⟨Y, hY, hi, heq, hhalf, hbound, hstay, hquad⟩ :=
    hF.exists_original_deficit_quadratic_expansion hcomplete old hu hxK hKt hG hval
      hactual hA hδ hpartners hsecond hcmp he hsub hInv hp hP hPxG hDP hPsecond hdim
      hBG h0G hσG0 hσG hGlevel hBP h0P (hσP.mono hBPB₀) hσP0
      (fun w hw ↦ hPlevel w (hBPB₀ hw)) hσPD hv hv0 hscale0 hdomain hΓEL hΓinit
      hm henergy hjet hab hseg
  refine ⟨eG, hxeG, hsourceG, heG, heiG, ?_, hfirstG, hBG, h0G, hσGC1, hσG0,
    hσG, himage, Γ, Y, hcenter, hY, hi, heq, hhalf, hbound, hstay, ?_⟩
  · exact heGx.trans (Prod.ext (hval hxK).symm rfl)
  · apply hquad.congr_left
    intro q
    have hcoef := hF.tubeEndpointCompliance_inverse_on_timeKernel hY hi heq hhalf 0
      hbound (sub_lt_sub_right hab (G x)) hstay (q.2 - q.1) (q.2 - q.1)
    dsimp only at hcoef ⊢
    rw [hcoef, ← hcenter]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
