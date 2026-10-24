import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthOneEdge

/-! The actual endpoint-confined regular birth count event has its K s² band
moment and original-input exponential count tail. No selected-cloud law is used. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- The literal regular left window has its sqrt(s)-weighted Palm budget
in its unchanged original source band, uniformly in every smaller physical cap. -/
theorem exists_original_regularBirth_left_window_weightedPalm_rate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ basecap C : ℝ,0 < basecap ∧ 0 < C ∧
    ∀ {g : ℝ → ℝ → ℝ}
      (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g),
    ∀ {cap : ℝ},0 < cap → cap ≤ basecap → ∀ n j i ell : ℕ,
    (∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0) →
    let s := birthDyadicElapsedScale H n j
    let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
    let weighted := ∫⁻ m,∫⁻ clock : ℝ,
      ENNReal.ofReal (originalNormalizedMomentumMarkNorm S w T m)*
        D.originalRegularBirthWindowWeight H ε cap 0 n j i ell (m,clock)
      ∂volume ∂legalMarkedJointPalm qdim Q.law
    weighted ≠ (∞:ℝ≥0∞) ∧ Real.sqrt s*weighted.toReal ≤
      cap*C*s^2*(∫⁻ m in {m : PhysicalPairPalmMark (Fin qdim) |
        m.1.1 ∈ D.originalLeftBirthNarrowClockBand H n j i},
        ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2) ∂legalMarkedJointPalm qdim Q.law).toReal := by
  let d := min ε (gap/2)
  have hd : 0 < d := lt_min hε (half_pos hgap)
  let J := Icc (D.lo+d/2) (D.hi-d/2)
  have hJI : J ⊆ Ioo D.lo D.hi := by
    intro x hx;constructor <;> dsimp [J] at hx <;> linarith [hx.1,hx.2]
  obtain ⟨C,hC,hweighted⟩ := D.exists_original_regularBirth_weightedPalm_square_rate hF hw isCompact_Icc hJI
  let basecap := d/(4*H)
  have hbasecap : 0 < basecap := div_pos hd (by positivity)
  refine ⟨basecap,C,hbasecap,hC,?_⟩
  intro g Q cap hcap hcapbase n j i ell hnonzero
  dsimp only
  let s := birthDyadicElapsedScale H n j
  let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  let Band := D.originalLeftBirthNarrowClockBand H n j i
  let B := {m : PhysicalPairPalmMark (Fin qdim) | m.1.1 ∈ Band}
  let I := Ioc ref (ref+width)
  let mask := D.originalRegularBirthWindowMask H ε cap 0 n j i ell
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hH n) (by positivity)
  have hcapH : cap*H ≤ d/4 := by
    have hbound := (le_div_iff₀ (by positivity : 0 < 4*H)).mp hcapbase
    nlinarith
  obtain ⟨z,hz⟩ := hnonzero
  have hwin := D.originalRegularBirth_left_window_in_compact hH hε hgap hbounds hcap hcapH n j i ell z hz
  have hB : MeasurableSet B := (D.measurableSet_originalLeftBirthNarrowClockBand H n j i).preimage measurable_fst.fst
  have hlen : volume I ≤ ENNReal.ofReal (cap*s) := by
    rw [Real.volume_Ioc]
    apply ENNReal.ofReal_le_ofReal
    simpa only [add_sub_cancel_left] using (birthPhysicalClockWindow_spec hcap hs).2.2.1
  have hclock : ∀ clock ∈ I,clock-S.level ∈ J := fun clock hc ↦ hwin clock ⟨hc.1.le,hc.2⟩
  have hzout : ∀ m clock,m ∉ B ∨ clock ∉ I → mask (m,clock) = 0 := by
    intro m clock hout
    by_contra hn
    have hm : D.originalSupportedLeftBirthPhysicalClockMask H cap n j i ell (m,clock) ≠ 0 :=
      right_ne_zero_of_mul hn
    have hbirth := (D.originalSupportedLeftBirthPhysicalClockMask_birth H cap n j i ell (m,clock) hm).1
    have hband : m ∈ B := D.originalLeftBirthClockMask_source_mem_clockGridBand H n j i (m,clock) hbirth
    have hclk : clock ∈ I := D.originalLeftBirthPhysicalClockMask_clock_mem H cap n j i ell (m,clock)
      ((D.originalSupportedLeftBirthPhysicalClockMask_ne_zero_iff H cap n j i ell (m,clock)).mp hm).2.2
    exact hout.elim (fun h ↦ h hband) (fun h ↦ h hclk)
  exact hweighted hgap hbounds Q hs hcap.le hB measurableSet_Ioc hlen hclock mask
    (D.originalRegularBirthWindowMask_le_one H ε cap 0 n j i ell) hzout

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
