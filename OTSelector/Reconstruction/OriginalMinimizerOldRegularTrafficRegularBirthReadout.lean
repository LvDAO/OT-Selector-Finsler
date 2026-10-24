import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthWindows

/-! Exact original-scene regular birth/death readouts retain the literal
narrow bands and finite physical windows. Endpoint separation leaves only
finitely many inward shells; original kinetic finiteness precedes toReal. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
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
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

private theorem sum_fin_product_eq_ranges {A : Type*} [AddCommMonoid A]
    (f : ℕ→ℕ→A) (N L : ℕ) :
    (∑i : Fin N,∑ell : Fin L,f i ell) = ∑i∈Finset.range N,∑ell∈Finset.range L,f i ell := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ↦∑ell : Fin L,f i ell) N]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Fin.sum_univ_eq_sum_range (f i) L

/-- Literal original traffic in a regular birth/death narrow band and physical window. -/
def originalRegularBirthWindowAbsoluteTraffic
    (η : (Fin qdim→ℝ)→ℝ) (H ε cap : ℝ) (side : Fin 2) (n j i ell : ℕ)
    (scene : LegalMarkedOptimalInputScene qdim) : ℝ≥0∞ :=
  legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
    (fun x↦ENNReal.ofReal (η x))
    (fun z↦ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
      D.originalRegularBirthWindowMask H ε cap side n j i ell z) scene

theorem measurable_originalRegularBirthWindowAbsoluteTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η)
    (H ε cap : ℝ) (side : Fin 2) (n j i ell : ℕ) :
    Measurable (D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell) :=
  measurable_legalMarkedCompletePathTraffic _ (measurable_originalSeedPathOffset_joint S hF hw)
    hη.ennreal_ofReal ((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
      (D.measurable_originalRegularBirthWindowMask H ε cap side n j i ell))

/-- The existing original kinetic first moment makes every literal regular
birth/death window finite before any of its real-valued estimates are used. -/
theorem ae_originalRegularBirthWindowAbsoluteTraffic_lt_top
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (H ε cap : ℝ) (side : Fin 2) (n j i ell : ℕ) :
    ∀ᵐscene∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene < (∞ : ℝ≥0∞) := by
  filter_upwards [D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hη hηI]
    with scene hs
  refine lt_of_le_of_lt ?_ hs
  apply legalMarkedCompletePathTraffic_mono_weights
  intro z
  exact mul_le_of_le_one_right (by positivity)
    (D.originalRegularBirthWindowMask_le_one H ε cap side n j i ell z)

/-- All actual regular windows reconstruct exactly their same regular clock
piece, pointwise in the original scene, with no L2 or summability assumption. -/
theorem tsum_originalRegularBirthWindowAbsoluteTraffic_eq_piece
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η)
    {H ε cap : ℝ} (hH : 0<H) (hspan : D.hi-D.lo≤H) (hcap : 0<cap)
    (side : Fin 2) (scene : LegalMarkedOptimalInputScene qdim) :
    (∑'n : ℕ,∑'j : ℕ,∑i∈Finset.range (dyadicBirthBandCount j),
      ∑ell∈Finset.range (birthPhysicalClockWindowCount cap),
        D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene) =
      D.originalClockPieceAbsoluteTraffic η ε
        (.inr (if side=0 then (0:Fin 4) else 2)) scene := by
  let I := Σn : ℕ,Σj : ℕ,Fin (dyadicBirthBandCount j) × Fin (birthPhysicalClockWindowCount cap)
  let W := fun k : I↦fun z : MarkClock↦
    ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
      D.originalRegularBirthWindowMask H ε cap side k.1 k.2.1 k.2.2.1 k.2.2.2 z
  have hW : ∀k,Measurable (W k) := fun k↦
    (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul
      (D.measurable_originalRegularBirthWindowMask H ε cap side k.1 k.2.1 k.2.2.1 k.2.2.2)
  have hweights (z : MarkClock) : (∑'k : I,W k z) =
      D.originalClockPieceSupportedWeight ε (.inr (if side=0 then (0:Fin 4) else 2)) z := by
    simp only [I,ENNReal.tsum_sigma',W,tsum_fintype,Fintype.sum_prod_type]
    calc
      _ = ∑'n : ℕ,∑'j : ℕ,∑i∈Finset.range (dyadicBirthBandCount j),
          ∑ell∈Finset.range (birthPhysicalClockWindowCount cap),
            ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
              D.originalRegularBirthWindowMask H ε cap side n j i ell z := by
        apply tsum_congr
        intro n
        apply tsum_congr
        intro j
        exact sum_fin_product_eq_ranges (fun i ell : ℕ↦
          ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ *
            D.originalRegularBirthWindowMask H ε cap side n j i ell z) _ _
      _ = _ := by
        simp_rw [←Finset.mul_sum,ENNReal.tsum_mul_left]
        rw [D.tsum_finiteSum_originalRegularBirthWindowMask hH hspan hcap]
        fin_cases side <;>
          dsimp [originalClockPieceSupportedWeight,originalClockTrafficPieceWeight,
            originalClockTrafficPieceMask,originalRegularRegionIndex] <;> ac_rfl
  have hs := legalMarkedCompletePathTraffic_tsum_weights
    (fun z : MarkClock↦originalSeedPathOffset S w z.2 z.1)
    (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal W hW scene
  rw [show (fun z↦∑'k : I,W k z) =
      D.originalClockPieceSupportedWeight ε (.inr (if side=0 then (0:Fin 4) else 2)) from funext hweights] at hs
  simp only [I,ENNReal.tsum_sigma',tsum_fintype,Fintype.sum_prod_type] at hs
  calc
    _ = ∑'n : ℕ,∑'j : ℕ,∑i : Fin (dyadicBirthBandCount j),
        ∑ell : Fin (birthPhysicalClockWindowCount cap),
          D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene := by
      symm
      apply tsum_congr
      intro n
      apply tsum_congr
      intro j
      exact sum_fin_product_eq_ranges
        (fun i ell : ℕ↦D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene) _ _
    _ = _ := hs.symm

/-- Regular endpoint separation turns the full actual window decomposition
into a finite shell family, uniformly over the physical cap and both sides. -/
theorem exists_finiteSum_originalRegularBirthWindowAbsoluteTraffic_eq_piece
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η)
    {H ε : ℝ} (hH : 0<H) (hspan : D.hi-D.lo≤H) (hε : 0<ε) :
    ∃N : ℕ,∀{cap : ℝ},0<cap→∀side : Fin 2,∀scene : LegalMarkedOptimalInputScene qdim,
      (∑outer : Fin N × Fin (birthPhysicalClockWindowCount cap),
        ∑'j : ℕ,∑i∈Finset.range (dyadicBirthBandCount j),
          D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side outer.1 j i outer.2 scene) =
        D.originalClockPieceAbsoluteTraffic η ε
          (.inr (if side=0 then (0:Fin 4) else 2)) scene := by
  obtain ⟨N,hN⟩ := D.exists_originalRegularBirthWindowMask_finite_shell_support hH hε
  refine ⟨N,?_⟩
  intro cap hcap side scene
  have htrunc : (∑n∈Finset.range N,∑'j : ℕ,∑i∈Finset.range (dyadicBirthBandCount j),
      ∑ell∈Finset.range (birthPhysicalClockWindowCount cap),
        D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene) =
      D.originalClockPieceAbsoluteTraffic η ε (.inr (if side=0 then (0:Fin 4) else 2)) scene := by
    rw [←D.tsum_originalRegularBirthWindowAbsoluteTraffic_eq_piece hF hw hη hH hspan hcap side scene]
    symm
    apply tsum_eq_sum
    intro n hn
    have hnN : N≤n := by simpa only [Finset.mem_range,not_lt] using hn
    have hzero (j i ell : ℕ) : D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene = 0 := by
      unfold originalRegularBirthWindowAbsoluteTraffic
      have hz := hN n hnN cap side j i ell
      simp only [hz,mul_zero,legalMarkedCompletePathTraffic,lintegral_zero]
    simp only [hzero,Finset.sum_const_zero,tsum_zero]
  have hfinite (n : ℕ) :
      (∑ell : Fin (birthPhysicalClockWindowCount cap),∑'j : ℕ,
        ∑i∈Finset.range (dyadicBirthBandCount j),
          D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene) =
      ∑'j : ℕ,∑i∈Finset.range (dyadicBirthBandCount j),
        ∑ell∈Finset.range (birthPhysicalClockWindowCount cap),
          D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene := by
    let f := fun (ell : Fin (birthPhysicalClockWindowCount cap)) (j : ℕ)↦
      ∑i∈Finset.range (dyadicBirthBandCount j),
        D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene
    change (∑ell,∑'j : ℕ,f ell j) = _
    calc
      _ = ∑'ell : Fin (birthPhysicalClockWindowCount cap),∑'j : ℕ,f ell j := by rw [tsum_fintype]
      _ = ∑'j : ℕ,∑'ell : Fin (birthPhysicalClockWindowCount cap),f ell j := ENNReal.tsum_comm
      _ = _ := by
        apply tsum_congr
        intro j
        rw [tsum_fintype]
        dsimp only [f]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _hi
        exact Fin.sum_univ_eq_sum_range (fun ell : ℕ↦
          D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene) _
  rw [Fintype.sum_prod_type]
  simp_rw [hfinite]
  exact (Fin.sum_univ_eq_sum_range (fun n : ℕ↦∑'j : ℕ,
    ∑i∈Finset.range (dyadicBirthBandCount j),∑ell∈Finset.range (birthPhysicalClockWindowCount cap),
      D.originalRegularBirthWindowAbsoluteTraffic η H ε cap side n j i ell scene) N).trans htrunc

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
