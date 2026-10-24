import OTSelector.Reconstruction.OriginalMinimizerRightRegularLevel
import OTSelector.Reconstruction.OriginalRegularBirthTrafficLtwoAssembly

/-! Actual original regular target-death traffic is L2. The original band
rates supply the single elapsed-time sum; a finite endpoint-shell and physical
window cover reads it as the literal original regular clock piece. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The complete actual regular target-death clock piece has L2 real readout
and finite original nonnegative traffic under the same original minimizer. -/
theorem original_minimizer_regularBirth_rightPiece_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 0<qdim)
    {ε gap diameter : ℝ} (hε : 0<ε) (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀x y,|g x y|≤gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hη0 : ∀x,0≤η x) {physicalRadius M₀ : ℝ}
    (hRadius : 0≤physicalRadius) (hM : 0≤M₀)
    (hηM : ∀x,η x≤M₀) (hηR : ∀x,physicalRadius<‖x‖→η x=0) :
    MemLp (fun scene↦(D.originalClockPieceAbsoluteTraffic η ε (.inr (2:Fin 4)) scene).toReal)
      2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
    ∀ᵐscene∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      D.originalClockPieceAbsoluteTraffic η ε (.inr (2:Fin 4)) scene ≠ (∞ : ℝ≥0∞) := by
  let H := D.hi-D.lo
  have hH : 0<H := sub_pos.mpr D.support.lt
  obtain ⟨h,cap,A,Btail,K₀,E₀,_hh,hcap,_hcap1,hA,hBtail,hK₀,hE₀,hallLp,hrate⟩ :=
    D.exists_original_regularBirth_right_level_norm hF hw hq hH hε hgap hbounds
      hg hgb τ Q hmin hη hηI hη0 hRadius hM (by norm_num : (0:ℝ)<1) hηM hηR
  apply D.memLp_original_regularBirth_piece_of_window_level_bounds hF hw hH
    (show D.hi-D.lo≤H from le_rfl) hε hcap hbounds Q hη hηI (1:Fin 2)
    hA hBtail hK₀ (show 0≤E₀ by linarith)
  · intro n ell hell j
    exact hallLp n ell hell j
  · intro n ell hell j hs K hK
    exact (hrate n ell hell j hs hK).2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
