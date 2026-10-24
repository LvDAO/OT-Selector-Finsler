import OTSelector.Reconstruction.OriginalMinimizerRightCommonScaleTraffic
import OTSelector.Reconstruction.OriginalSameResidueClockBandEnergyBudget
import OTSelector.Reconstruction.FinslerFocalLiteralEdgeOccupation

/-! Actual right-birth window foundations use the unchanged target clock,
right pole and original minimizer. The literal half-open target bands are
identified exactly with reflected inward clock bands. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- The literal right-birth subdivision has one actual physical one-edge
constant at every inward and elapsed scale, before selected input counts. -/
theorem exists_original_right_birthWindow_single_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ ε₀ σ : ℝ, 0 < ε₀ ∧ 0 < σ ∧ ∀ {ε cap : ℝ},
      0 < ε → ε < ε₀ → 0 < cap → cap ≤ σ →
      ∀ (n j i ell : ℕ), i < dyadicBirthBandCount j → ell < birthPhysicalClockWindowCount cap →
      ∀ {R₀ M₀ : ℝ}, 0 ≤ R₀ → 0 ≤ M₀ →
      ∀ {η : (Fin q → ℝ) → ℝ}, (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M₀) →
        (∀ x, R₀ < ‖x‖ → η x = 0) →
      ∀ (x : Fin q → ℝ) (m : PhysicalPairPalmMark (Fin q)),
        (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
          D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell (m,c)) ≤
          ENNReal.ofReal (4*M₀*(R₀+1)) := by
  obtain ⟨δ,hδ,_hδspan,σ,hσ,_hσhalf,hterminal⟩ :=
    D.exists_original_right_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ/4,σ,by positivity,hσ,?_⟩
  intro ε cap hε hεδ hcap hcapσ n j i ell hi hell R₀ M₀ hR₀ hM₀ η hη0 hηM hηR x m
  let mask := D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell
  by_cases hz : ∀ c, mask (m,c)=0
  · simp only [originalSupportedRightBirthPhysicalClockWeight,←show mask=
        D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell from rfl,
        hz,mul_zero,lintegral_zero]
    exact bot_le
  push Not at hz
  obtain ⟨c,hc⟩ := hz
  let e := (physicalPairAnchorHomeomorph q).symm (x,m)
  have he : physicalPairAnchor e=(x,m) := (physicalPairAnchorHomeomorph q).apply_symm_apply (x,m)
  have hclock : e.1.2-S.level∈Ioo D.lo D.hi := by
    have hm := D.originalSupportedRightBirthPhysicalClockMask_support ε cap n j i ell (m,c) hc
    change (physicalPairAnchor e).2.1.1-S.level∈Ioo D.lo D.hi
    rw [he]
    exact ⟨by linarith [hm.2.2.1],by linarith [hm.2.2.2.1,hm.2.2.2.2.1,hm.2.2.2.2.2]⟩
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  let a := D.hi-(ref-S.level)
  have ht : 0<t := birthDyadicShellScale_pos hε n
  have hb := birthDyadicClockBand_base_bounds hε n j i hi
  have hs : 0<s := hb.1
  have hwidth := birthPhysicalClockWindow_spec hcap hs
  have ha := D.originalRightBirthPhysicalClockWindow_inward_bounds hε hcap n j i ell hi hell
    (show ref∈Icc (ref-width) ref from ⟨by linarith [hwidth.2.1],le_rfl⟩)
  have htε : 2*t≤ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have haI : a∈Ioo (0:ℝ) δ := ⟨ht.trans_le ha.1,by dsimp only [a]; linarith [ha.2]⟩
  have hband : ∀ c∈Icc (ref-width) ref,|D.hi-(c-S.level)-a|≤σ*a := by
    intro c hc
    rw [abs_of_nonneg (by dsimp only [a]; linarith [hc.2])]
    have hcs : width≤cap*s := hwidth.2.2.1
    have hst : s≤t := hb.2.1
    have hsA : s≤a := hst.trans ha.1
    calc
      _ ≤ width := by dsimp only [a]; linarith [hc.1]
      _ ≤ cap*s := hcs
      _ ≤ σ*a := mul_le_mul hcapσ hsA hs.le hσ.le
  have hz : ∀ c∉Icc (ref-width) ref,mask ((physicalPairAnchor e).2,c)=0 := by
    intro c hc
    by_contra hn
    have hh := (D.originalSupportedRightBirthPhysicalClockMask_ne_zero_iff
      ε cap n j i ell ((physicalPairAnchor e).2,c)).mp hn
    have hh := D.originalRightBirthPhysicalClockMask_clock_mem ε cap n j i ell _ hh.2.2
    exact hc ⟨hh.1,hh.2.le⟩
  have hedge := (hterminal a haI (ref-width) ref (by linarith [hwidth.2.1]) hband e hclock
    R₀ M₀ hR₀ hM₀ η hη0 hηM hηR mask
    (fun c _ ↦D.originalSupportedRightBirthPhysicalClockMask_le_one ε cap n j i ell _) hz).1
  have hb : originalMaskedCompletePathEdgeTraffic S w η mask e≤ENNReal.ofReal (4*M₀*(R₀+1)) :=
    hedge.trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (by positivity) (min_le_left _ _)))
  change legalMarkedCompletePathEdgeTraffic q _ _ _ e≤_ at hb
  simpa only [legalMarkedCompletePathEdgeTraffic,he,Prod.fst,Prod.snd,
    originalSupportedRightBirthPhysicalClockWeight,mask] using hb

/-- One true original target Palm energy budget covers every literal reflected
right narrow-band family, preserving its Ico boundary convention exactly. -/
theorem exists_original_right_narrowBirthBands_energy_budget
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi-D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r∈Ioo 0 poleη, originalSeedKernel S w (D.hi-r)=(r ^ 2)⁻¹ • G+Rem r)
    {gap diameter : ℝ} (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g) :
    ∃ E₀ : ℝ, 1≤E₀ ∧ ∀ {ε : ℝ},0<ε→∀ n j N : ℕ,
      let B := fun i ↦{m : PhysicalPairPalmMark (Fin q) |
        m.1.2∈D.originalRightBirthNarrowClockBand ε n j i}
      (∀ i : ℕ,
        (∫⁻ m in B i,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
          ∂legalMarkedJointPalm q Q.law)≠(∞:ℝ≥0∞) ∧
        (∫⁻ m in B i,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
          ∂legalMarkedJointPalm q Q.law)≠(∞:ℝ≥0∞)) ∧
      (∑ i∈Finset.range N,(∫⁻ m in B i,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
        ∂legalMarkedJointPalm q Q.law).toReal)≤E₀ ∧
      (∑ i∈Finset.range N,(∫⁻ m in B i,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
        ∂legalMarkedJointPalm q Q.law).toReal)≤E₀ := by
  obtain ⟨E₀,hE₀,hbudget⟩ := D.exists_original_right_sameResidue_clockBand_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  refine ⟨E₀,hE₀,?_⟩
  intro ε hε n j N
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  have hs : 0<s := div_pos (birthDyadicShellScale_pos hε n) (by positivity)
  have hset : ∀ i : ℕ,{m : PhysicalPairPalmMark (Fin q) |
      m.1.2∈D.originalRightBirthNarrowClockBand ε n j i} =
      (fun m : PhysicalPairPalmMark (Fin q) ↦D.hi-(m.1.2-S.level)) ⁻¹' clockGridBand t (s/8) i := by
    intro i
    ext m
    simp only [mem_ofPred_eq,originalRightBirthNarrowClockBand,clockGridBand,
      mem_preimage,mem_Ioc,mem_Ico]
    constructor
    · intro hm
      constructor <;> dsimp only [t,s] <;> linarith [hm.1,hm.2]
    · intro hm
      constructor <;> dsimp only [t,s] at hm <;> linarith [hm.1,hm.2]
  have hb := hbudget t (div_nonneg hs.le (by norm_num : (0:ℝ)≤8)) N
  dsimp only at hb ⊢
  simpa only [←hset] using hb

/-- Rank zero makes the same original right residue energy identically zero. -/
theorem original_right_poleEnergy_eq_zero_of_rank_zero
    {G : Matrix (Fin q) (Fin q) ℝ} (hGzero : G.rank=0)
    (m : PhysicalPairPalmMark (Fin q)) : originalSeedRightPoleEnergy S w D.hi G m=0 := by
  have hlin : G.mulVecLin=0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hGzero)
  have hzero : G=0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    change G.mulVecLin (Pi.single i 1)=(0:Matrix (Fin q) (Fin q) ℝ).mulVecLin (Pi.single i 1)
    rw [hlin,Matrix.mulVecLin_zero]
  simp only [originalSeedRightPoleEnergy,hzero,Matrix.zero_mulVec,dotProduct_zero,zero_div]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
