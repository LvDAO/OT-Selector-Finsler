import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthReadout
import OTSelector.Probability.DyadicTrafficTailSummation
import OTSelector.MeasureTheory.Lp.FiniteWindowENNRealReadout

/-! A common analytic readout turns actual regular birth/death band estimates
into their literal original piece. The geometric and Palm level producers are
provided separately for the true source and target intensities. -/
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

/-- Actual single-window level estimates give the complete original regular
piece, with one common shell cutoff and finite physical cover for either side.
Only individual level L2 and quantitative raw level rates are inputs. -/
theorem memLp_original_regularBirth_piece_of_window_level_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {H ε cap : ℝ} (hH : 0<H) (hspan : D.hi-D.lo≤H) (hε : 0<ε) (hcap : 0<cap)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (side : Fin 2) {A Btail K₀ E₀ : ℝ}
    (hA : 0≤A) (hBtail : 0≤Btail) (hK₀ : 0≤K₀) (hE₀ : 0≤E₀)
    (hallLp : ∀n ell : ℕ,ell<birthPhysicalClockWindowCount cap→∀j : ℕ,
      MemLp (fun scene↦∑i∈Finset.range (dyadicBirthBandCount j),
        (D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)))
    (hrate : ∀n ell : ℕ,ell<birthPhysicalClockWindowCount cap→∀j : ℕ,
      birthDyadicElapsedScale H n j≤1→∀{K : ℝ},K₀≤K→
      eLpNorm (fun scene↦∑i∈Finset.range (dyadicBirthBandCount j),
        (D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
        ENNReal.ofReal (A*Real.sqrt (K*E₀)*Real.sqrt (birthDyadicElapsedScale H n j)+
          Btail*((2:ℝ)^j*Real.exp (-K/4)))) :
    MemLp (fun scene↦(D.originalClockPieceAbsoluteTraffic η ε
      (.inr (if side=0 then (0:Fin 4) else 2)) scene).toReal)
      2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
    ∀ᵐscene∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      D.originalClockPieceAbsoluteTraffic η ε (.inr (if side=0 then (0:Fin 4) else 2)) scene ≠
        (∞ : ℝ≥0∞) := by
  obtain ⟨N,hsum⟩ := D.exists_finiteSum_originalRegularBirthWindowAbsoluteTraffic_eq_piece
    hF hw hη hH hspan hε
  let P : Measure (LegalMarkedOptimalInputScene qdim) := Q.law
  let L := Fin N × Fin (birthPhysicalClockWindowCount cap)
  let window := fun (outer : L) (j i : ℕ) (scene : LegalMarkedOptimalInputScene qdim)↦
    D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side outer.1 j i outer.2 scene
  let level := fun (outer : L) (j : ℕ) (scene : LegalMarkedOptimalInputScene qdim)↦
    ∑i∈Finset.range (dyadicBirthBandCount j),(window outer j i scene).toReal
  have hfinite : ∀outer j i,∀ᵐscene∂P,window outer j i scene ≠ (∞ : ℝ≥0∞) := by
    intro outer j i
    exact (D.ae_originalRegularBirthWindowAbsoluteTraffic_lt_top hF hw hbounds Q hη hηI
      H ε cap side outer.1 j i outer.2).mono (fun _ hs↦hs.ne)
  have hseries (outer : L) : MemLp (fun scene↦∑'j,level outer j scene) 2 P ∧
      Summable (fun j↦(eLpNorm (level outer j) 2 P).toReal) ∧
      ∀ᵐscene∂P,Summable (fun j↦‖level outer j scene‖) := by
    apply memLp_dyadic_tsum_of_eventual_level_norm_bounds P hK₀
      (birthDyadicShellScale_pos hH outer.1) (by norm_num : (0:ℝ)<1/2)
      hE₀ hA hBtail (level outer)
    · intro j
      exact hallLp outer.1 outer.2 outer.2.isLt j
    · intro j hs K hK
      have h := hrate outer.1 outer.2 outer.2.isLt j hs hK
      simpa only [Real.sqrt_eq_rpow,birthDyadicElapsedScale,level,window,P] using h
  have hread := memLp_finite_window_ennreal_traffic_readout P
    (fun j : ℕ↦Finset.range (dyadicBirthBandCount j)) window hfinite
    (fun outer↦(hseries outer).1) (fun outer↦(hseries outer).2.2)
  have heq (scene : LegalMarkedOptimalInputScene qdim) :
      (∑outer : L,∑'j : ℕ,∑i∈Finset.range (dyadicBirthBandCount j),window outer j i scene) =
      D.originalClockPieceAbsoluteTraffic η ε (.inr (if side=0 then (0:Fin 4) else 2)) scene := by
    exact hsum hcap side scene
  exact ⟨by simpa only [heq] using hread.1,
    hread.2.mono (fun scene hs↦by simpa only [heq] using hs)⟩


end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
