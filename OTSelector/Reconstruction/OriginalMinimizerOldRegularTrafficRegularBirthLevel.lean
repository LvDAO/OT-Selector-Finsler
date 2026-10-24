import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthFullWindow

/-! The actual endpoint-confined regular birth count event has its K s² band
moment and original-input exponential count tail. No selected-cloud law is used. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
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

/-- The actual finite source bands spend the original momentum budget once.
The resulting single elapsed-time level has a sqrt(s) gain and the exact
2^j count-tail cost, with the same original h and cap at every level. -/
theorem exists_original_regularBirth_left_level_norm
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < qdim)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y,|g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching qdim μ ν
      (D.originalFocalKinetic gap) g,Q.value τ ≤ P.value τ)
    {η : (Fin qdim → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hη0 : ∀ x,0 ≤ η x) {physicalRadius M₀ basecap : ℝ}
    (hRadius : 0 ≤ physicalRadius) (hM : 0 ≤ M₀) (hbasecap : 0 < basecap)
    (hηM : ∀ x,η x ≤ M₀) (hηR : ∀ x,physicalRadius < ‖x‖ → η x = 0) :
    ∃ h cap A Btail K₀ E₀ : ℝ,0 < h ∧ 0 < cap ∧ cap ≤ basecap ∧
      0 ≤ A ∧ 0 ≤ Btail ∧ 0 ≤ K₀ ∧ 1 ≤ E₀ ∧
    (∀ n ell : ℕ,ell < birthPhysicalClockWindowCount cap → ∀ j : ℕ,
      MemLp (fun scene : LegalMarkedOptimalInputScene qdim ↦
        ∑ i ∈ Finset.range (dyadicBirthBandCount j),
        (legalMarkedCompletePathTraffic qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1)
          (fun x ↦ ENNReal.ofReal (η x)) (D.originalRegularBirthWindowWeight H ε cap 0 n j i ell) scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim))) ∧
    ∀ n ell : ℕ,ell < birthPhysicalClockWindowCount cap →
    ∀ j : ℕ,birthDyadicElapsedScale H n j ≤ 1 →
    ∀ {K : ℝ},K₀ ≤ K →
    let s := birthDyadicElapsedScale H n j
    let level := fun scene : LegalMarkedOptimalInputScene qdim ↦
      ∑ i ∈ Finset.range (dyadicBirthBandCount j),
      (legalMarkedCompletePathTraffic qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1)
        (fun x ↦ ENNReal.ofReal (η x)) (D.originalRegularBirthWindowWeight H ε cap 0 n j i ell) scene).toReal
    MemLp level 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
      eLpNorm level 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
        ENNReal.ofReal (A*Real.sqrt (K*E₀)*Real.sqrt s+Btail*((2:ℝ)^j*Real.exp (-K/4))) := by
  obtain ⟨h,cap,Awindow,Bwindow,K₀,hh,hcap,hcapbase,hAwindow,hBwindow,hK₀,hhead,hwindow⟩ :=
    D.exists_original_regularBirth_left_window_norm hF hw hq hH hε hgap hbounds
      hg hgb τ Q hmin hη hηI hη0 hRadius hM hbasecap hηM hηR
  obtain ⟨E₀,hE₀,hbudget⟩ := D.exists_original_regularBirth_clockBand_momentum_budget hF hw hgap hbounds Q
  let A := Real.sqrt (8*H)*Awindow
  let Btail := 8*Bwindow
  refine ⟨h,cap,A,Btail,K₀,E₀,hh,hcap,hcapbase,by dsimp [A];positivity,
    by dsimp [Btail];positivity,hK₀,hE₀,?_,?_⟩
  · intro n ell hell j
    apply memLp_finsetSum
    intro i _
    by_cases hn : ∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0
    · exact hhead n j i ell hell hn
    · have hz : ∀ z,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z = 0 :=
        fun z ↦ by by_contra h;exact hn ⟨z,h⟩
      have hzero : (fun scene : LegalMarkedOptimalInputScene qdim ↦
          (legalMarkedCompletePathTraffic qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1)
            (fun x ↦ ENNReal.ofReal (η x)) (D.originalRegularBirthWindowWeight H ε cap 0 n j i ell) scene).toReal) = 0 := by
        funext scene
        simp only [originalRegularBirthWindowWeight,hz,mul_zero,legalMarkedCompletePathTraffic,lintegral_zero,
          ENNReal.toReal_zero,Pi.zero_apply]
      rw [hzero]
      exact MemLp.zero
  intro n ell hell j hs1 K hK
  dsimp only
  let s := birthDyadicElapsedScale H n j
  let t := birthDyadicShellScale H n
  let bands := Finset.range (dyadicBirthBandCount j)
  let traffic := fun (i : ℕ) (scene : LegalMarkedOptimalInputScene qdim) ↦
    (legalMarkedCompletePathTraffic qdim (fun z ↦ originalSeedPathOffset S w z.2 z.1)
      (fun x ↦ ENNReal.ofReal (η x)) (D.originalRegularBirthWindowWeight H ε cap 0 n j i ell) scene).toReal
  let energy := fun i : ℕ ↦ (∫⁻ m in {m : PhysicalPairPalmMark (Fin qdim) |
        m.1.1 ∈ D.originalLeftBirthNarrowClockBand H n j i},
        ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2) ∂legalMarkedJointPalm qdim Q.law).toReal
  have hs : 0 < s := div_pos (birthDyadicShellScale_pos hH n) (by positivity)
  have hk : 0 ≤ K := hK₀.trans hK
  have hwindow' (i : ℕ) : MemLp (traffic i) 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
      eLpNorm (traffic i) 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
        ENNReal.ofReal (Awindow*Real.sqrt K*s*Real.sqrt (energy i)+Bwindow*Real.exp (-K/4)) := by
    by_cases hn : ∃ z : MarkClock,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z ≠ 0
    · exact hwindow n j i ell hell hs1 hn hK
    · have hz : ∀ z,D.originalRegularBirthWindowMask H ε cap 0 n j i ell z = 0 :=
        fun z ↦ by by_contra h;exact hn ⟨z,h⟩
      have hzero : traffic i = 0 := by
        funext scene
        simp only [traffic,originalRegularBirthWindowWeight,hz,mul_zero,legalMarkedCompletePathTraffic,lintegral_zero,
          ENNReal.toReal_zero,Pi.zero_apply]
      rw [hzero,eLpNorm_zero]
      exact ⟨MemLp.zero,zero_le⟩
  have hbudget' : (∑ i ∈ bands,energy i) ≤ E₀ := by
    have hb := (hbudget (fun m : PhysicalPairPalmMark (Fin qdim) ↦ m.1.1-S.level)
      ((measurable_fst.fst : Measurable (fun m : PhysicalPairPalmMark (Fin qdim) ↦ m.1.1)).sub_const (S.level:ℝ)) (D.lo+t) (show 0 ≤ s/8 by positivity)
      (dyadicBirthBandCount j)).2
    exact hb
  have hsum := sum_sqrt_energy_le_card_sqrt_mul bands energy (fun _ ↦ ENNReal.toReal_nonneg) hbudget'
  have hcard : (bands.card:ℝ) = 8*(2:ℝ)^j := by
    simp only [bands,Finset.card_range,dyadicBirthBandCount,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  have hNs : (bands.card:ℝ)*s ≤ 8*H := by
    have hts : (bands.card:ℝ)*s = 8*t := by
      rw [hcard]
      dsimp only [s,birthDyadicElapsedScale,t]
      field_simp
    rw [hts]
    have htH : t ≤ H := by
      have ht2 : 2*t ≤ H := by
        rw [two_mul_birthDyadicShellScale]
        exact div_le_self hH.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
      linarith [birthDyadicShellScale_pos hH n]
    linarith
  refine ⟨memLp_finsetSum bands (fun i _ ↦ (hwindow' i).1),?_⟩
  calc
    _ = eLpNorm (∑ i ∈ bands,traffic i) 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) := by
      congr 1
      funext scene
      simp only [Finset.sum_apply,bands,traffic]
    _ ≤ ∑ i ∈ bands,eLpNorm (traffic i) 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) :=
      eLpNorm_sum_le (fun i _ ↦ (hwindow' i).1.aestronglyMeasurable) (by norm_num)
    _ ≤ ∑ i ∈ bands,ENNReal.ofReal (Awindow*Real.sqrt K*s*Real.sqrt (energy i)+Bwindow*Real.exp (-K/4)) :=
      Finset.sum_le_sum (fun i _ ↦ (hwindow' i).2)
    _ = ENNReal.ofReal (Awindow*Real.sqrt K*s*(∑ i ∈ bands,Real.sqrt (energy i))+
        (bands.card:ℝ)*(Bwindow*Real.exp (-K/4))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
      congr 1
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ ENNReal.ofReal (Awindow*Real.sqrt K*s*(Real.sqrt (bands.card:ℝ)*Real.sqrt E₀)+
        (bands.card:ℝ)*(Bwindow*Real.exp (-K/4))) :=
      ENNReal.ofReal_le_ofReal (add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) le_rfl)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hscale : Real.sqrt (bands.card:ℝ)*s = Real.sqrt ((bands.card:ℝ)*s)*Real.sqrt s := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _),mul_assoc,Real.mul_self_sqrt hs.le]
      have hmain : Awindow*Real.sqrt K*s*(Real.sqrt (bands.card:ℝ)*Real.sqrt E₀) ≤
          A*Real.sqrt (K*E₀)*Real.sqrt s := by
        calc
          _ = (Awindow*Real.sqrt K*Real.sqrt E₀)*(Real.sqrt (bands.card:ℝ)*s) := by ring
          _ = (Awindow*Real.sqrt K*Real.sqrt E₀)*(Real.sqrt ((bands.card:ℝ)*s)*Real.sqrt s) := by rw [hscale]
          _ ≤ (Awindow*Real.sqrt K*Real.sqrt E₀)*(Real.sqrt (8*H)*Real.sqrt s) := by gcongr
          _ = _ := by dsimp only [A];rw [Real.sqrt_mul hk];ring
      apply (add_le_add hmain le_rfl).trans_eq
      rw [hcard]
      dsimp only [Btail]
      ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
