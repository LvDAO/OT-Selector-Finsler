import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylorCycle
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylorLegalRectangles

/-!
# Original physical packing certificates from one actual Taylor center

The Taylor accuracy and its one frozen center are chosen at a fixed positive
geometric gap threshold. A strict frozen cycle above that threshold produces
countable legal rectangles whose rational gap stays above the same threshold.
Every original physical endpoint in the retained masks then satisfies the
original scaled-slack certificate. No population bound for one core is asserted.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module Topology TopologicalSpace
  OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal Classical
noncomputable section

namespace OTSelector.Probability
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Local continuity on the legal domain suffices to detect each strict legal exchange. -/
theorem exists_cavityLegalBasisCycleIndex_of_strict_cycle_above
    (c : X → Y → ℝ) (D : Set (X × Y)) (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry c) D)
    {BX : Set (Set X)} {BY : Set (Set Y)}
    (hBX : IsTopologicalBasis BX) (hBY : IsTopologicalBasis BY)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (x x' : X) (y y' : Y) (hxy : (x, y) ∈ D) (hxy' : (x', y') ∈ D)
    (hcross : (x, y') ∈ D) (hcross' : (x', y) ∈ D)
    (hbad : γ < c x y + c x' y' - c x y' - c x' y) :
    ∃ i : CavityBasisCycleIndex BX BY, γ < (i.2 : ℝ) ∧ CavityLegalBasisCycleValid c D i ∧
      (x, y) ∈ i.1.1.1.val ×ˢ i.1.1.2.val ∧
      (x', y') ∈ i.1.2.1.val ×ˢ i.1.2.2.val := by
  obtain ⟨q, hγq, hqgap⟩ := exists_rat_btwn hbad
  have hq : (0 : ℚ) < q := by exact_mod_cast hγ.trans_lt hγq
  let a := ((x, y), (x', y'))
  let legal : Set ((X × Y) × (X × Y)) :=
    {z | z.1 ∈ D ∧ z.2 ∈ D ∧ (z.1.1, z.2.2) ∈ D ∧ (z.2.1, z.1.2) ∈ D}
  have hlegal : IsOpen legal :=
    (hD.preimage continuous_fst).inter ((hD.preimage continuous_snd).inter
      ((hD.preimage (continuous_fst.fst.prodMk continuous_snd.snd)).inter
        (hD.preimage (continuous_snd.fst.prodMk continuous_fst.snd))))
  have h₀ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.1.1 z.1.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ z.1)
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hxy)) continuous_fst.continuousAt
  have h₁ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.2.1 z.2.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ z.2)
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hxy')) continuous_snd.continuousAt
  have h₂ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.1.1 z.2.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ (z.1.1, z.2.2))
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hcross))
      (continuous_fst.fst.prodMk continuous_snd.snd).continuousAt
  have h₃ : ContinuousAt (fun z : (X × Y) × (X × Y) ↦ c z.2.1 z.1.2) a :=
    ContinuousAt.comp (f := fun z : (X × Y) × (X × Y) ↦ (z.2.1, z.1.2))
      (g := Function.uncurry c) (x := a)
      (hc.continuousAt (hD.mem_nhds hcross'))
      (continuous_snd.fst.prodMk continuous_fst.snd).continuousAt
  have hcont : ContinuousAt (fun z : (X × Y) × (X × Y) ↦
      c z.1.1 z.1.2 + c z.2.1 z.2.2 - c z.1.1 z.2.2 - c z.2.1 z.1.2) a :=
    ((h₀.add h₁).sub h₂).sub h₃
  have hn : {z : (X × Y) × (X × Y) |
      (q : ℝ) < c z.1.1 z.1.2 + c z.2.1 z.2.2 - c z.1.1 z.2.2 - c z.2.1 z.1.2} ∩
        legal ∈ 𝓝 a :=
    inter_mem (hcont.preimage_mem_nhds (Ioi_mem_nhds hqgap))
      (hlegal.mem_nhds ⟨hxy, hxy', hcross, hcross'⟩)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨C, hC, E, hE, hCE⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨A₀, hA₀, hx, hAA⟩ := hBX.mem_nhds_iff.mp hA
  obtain ⟨B₀, hB₀, hy, hBB⟩ := hBY.mem_nhds_iff.mp hB
  obtain ⟨C₀, hC₀, hx', hCC⟩ := hBX.mem_nhds_iff.mp hC
  obtain ⟨E₀, hE₀, hy', hEE⟩ := hBY.mem_nhds_iff.mp hE
  have hall : ∀ a ∈ A₀, ∀ b ∈ B₀, ∀ a' ∈ C₀, ∀ b' ∈ E₀,
      (q : ℝ) < c a b + c a' b' - c a b' - c a' b ∧
      (a, b) ∈ D ∧ (a', b') ∈ D ∧ (a, b') ∈ D ∧ (a', b) ∈ D := by
    intro a ha b hb a' ha' b' hb'
    exact @hUV ((a, b), (a', b'))
      ⟨hAB ⟨hAA ha, hBB hb⟩, hCE ⟨hCC ha', hEE hb'⟩⟩
  refine ⟨(((⟨A₀, hA₀⟩, ⟨B₀, hB₀⟩), (⟨C₀, hC₀⟩, ⟨E₀, hE₀⟩)), q), hγq,
    ⟨⟨hq, ?_⟩, ?_⟩, ⟨hx, hy⟩, ⟨hx', hy'⟩⟩
  · intro a ha b hb a' ha' b' hb'
    exact (hall a ha b hb a' ha' b' hb').1.le
  · intro a ha b hb a' ha' b' hb'
    exact (hall a ha b hb a' ha' b' hb').2

end OTSelector.Probability

namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore
variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- The original physical endpoint observed in the literal scaled seed coordinates. -/
def actualSeedRootedEndpoint (scale : ℝ)
    (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (x : M) :
    (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ :=
  (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale x - root, u x)

/-- The observed frozen cost is exactly the coefficient evaluated on the actual
rooted displacement and original clocks. -/
theorem actualFrozenRootedQuadratic_eq_frozenQuadraticCost_endpoint
    (c : ℚ → M) (scale : ℝ)
    (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (x y : M) :
    C.actualFrozenRootedQuadratic c scale root x y =
      C.frozenQuadraticCost c (C.actualSeedRootedEndpoint scale root x)
        (C.actualSeedRootedEndpoint scale root y) := rfl

/-- The open legal clock rectangle also screens each actual rooted endpoint
inside the one fixed spatial radius. -/
def frozenClockRadiusOpenRectangle (R sL sR tL tR : ℝ) : Set
    (((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)) :=
  {p | p ∈ C.frozenClockOpenRectangle sL sR tL tR ∧ ‖p.1.1‖ < R ∧ ‖p.2.1‖ < R}

theorem isOpen_frozenClockRadiusOpenRectangle (R sL sR tL tR : ℝ) :
    IsOpen (C.frozenClockRadiusOpenRectangle R sL sR tL tR) :=
  (C.isOpen_frozenClockOpenRectangle sL sR tL tR).inter
    ((isOpen_lt continuous_fst.fst.norm continuous_const).inter
      (isOpen_lt continuous_snd.fst.norm continuous_const))

theorem frozenClockRadiusOpenRectangle_subset_original_region
    {R sL sR tL tR : ℝ}
    (hs : Icc sL sR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (hclockgap : (C.window.val.2.2 : ℝ) ≤ tL - sR) :
    C.frozenClockRadiusOpenRectangle R sL sR tL tR ⊆
      C.frozenQuadraticLegalDomain id :=
  fun _ hp ↦ C.frozenClockOpenRectangle_subset_original_region hs ht hclockgap hp.1

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- A fixed positive geometric gap determines one actual Taylor center first.
Every strict frozen cycle above that threshold, in the original strict clock
bins and bounded rooted window, then supplies a countable legal rectangle with
the SAME original physical scaled-slack packing certificate on the retained
source and target masks. No bound on discarded population mass is asserted. -/
theorem exists_actualMacroscopicTaylor_legal_masked_packing_certificate
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    (hrem : ∀ η > 0, ∃ radius > 0,
      ∀ z ∈ C.roots, C.SourceCoordinateRemainderBound z η radius)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {K : Set (ℚ → M)} (hK : IsCompact K) (hsub : K ⊆ C.roots)
    {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ K)
    (H Ks Kt : Set M)
    (hsource : ∀ x ∈ H ∩ Ks, a x ∈ K ∧ x ∈ F.potentialRegularDomain u)
    (htarget : ∀ y ∈ Kt, a y ∈ K ∧ y ∈ F.potentialRegularDomain u)
    (R sL sR tL tR : ℝ)
    (hs : Icc sL sR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc (C.window.val.1 : ℝ) (C.window.val.2.1 : ℝ))
    (hclockgap : (C.window.val.2.2 : ℝ) ≤ tL - sR)
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε > 0, ∃ T : C.TaylorRootCover ε,
    ∃ A : C.ActualMacroscopicTaylorCertificate T K macroCenter,
    ∃ threshold > 0,
    ∀ ξ η : Fin 2 → ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ),
      (∀ i, ‖(ξ i).1‖ < R) → (∀ j, ‖(η j).1‖ < R) →
      (∀ i, (ξ i).2 ∈ Ioo sL sR) → (∀ j, (η j).2 ∈ Ioo tL tR) →
      γ < C.frozenQuadraticCost A.frozenCenter (ξ 0) (η 0) +
        C.frozenQuadraticCost A.frozenCenter (ξ 1) (η 1) -
        C.frozenQuadraticCost A.frozenCenter (ξ 0) (η 1) -
        C.frozenQuadraticCost A.frozenCenter (ξ 1) (η 0) →
      ∃ i : CavityBasisCycleIndex
        (cavitySpatialBasis
          (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ))
        (cavitySpatialBasis
          (ι := Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) (A := ℝ)),
        γ < (i.2 : ℝ) ∧
        CavityLegalBasisCycleValid (C.frozenQuadraticCost A.frozenCenter)
          (C.frozenClockRadiusOpenRectangle R sL sR tL tR) i ∧
        (ξ 0, η 0) ∈ i.1.1.1.val ×ˢ i.1.1.2.val ∧
        (ξ 1, η 1) ∈ i.1.2.1.val ×ˢ i.1.2.2.val ∧
        Disjoint i.1.1.1.val i.1.2.1.val ∧ Disjoint i.1.1.2.val i.1.2.2.val ∧
        (∃ phaseSize > 0, ∃ offset :
          Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
          ∀ s ∈ i.1.1.1.val ∪ i.1.2.1.val,
            s.1 - offset ∈ cavityGridPhaseCell _ phaseSize) ∧
        ∀ scale : ℝ, threshold ≤ scale →
        ∀ root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
          dist (physicalSceneMacroscopicRoot scale root)
            ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
              (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) <
                A.macroRadius →
        ∀ n : ℕ, ∀ Y : Fin (n + 1) → M,
        ∀ x ∈ H ∩ Ks, ∀ x' ∈ H ∩ Ks,
          C.actualSeedRootedEndpoint scale root x ∈ i.1.1.1.val →
          C.actualSeedRootedEndpoint scale root x' ∈ i.1.2.1.val →
        ∀ j, Y j ∈ Kt → C.actualSeedRootedEndpoint scale root (Y j) ∈ i.1.1.2.val →
        ∀ l, Y l ∈ Kt → C.actualSeedRootedEndpoint scale root (Y l) ∈ i.1.2.2.val →
          γ / 2 ≤
            scale ^ 2 * ((F.lengthEDist x (Y j)).toReal - u (Y j) + u x) +
            scale ^ 2 * ((F.lengthEDist x' (Y l)).toReal - u (Y l) + u x') -
            scale ^ 2 * ((F.lengthEDist x (Y l)).toReal - u (Y l) + u x) -
            scale ^ 2 * ((F.lengthEDist x' (Y j)).toReal - u (Y j) + u x') := by
  obtain ⟨B, hB, ε, hε, hbudget, T, A, threshold, hthreshold, hcycles⟩ :=
    C.exists_actualMacroscopicTaylorCycleGap hF hcomplete hu ha hinj
      hlabel hrem horder hK hsub hmacroCenter R hγ
  refine ⟨ε, hε, T, A, threshold, hthreshold, ?_⟩
  intro ξ η hξR hηR hξclock hηclock hgap
  let D := C.frozenClockRadiusOpenRectangle R sL sR tL tR
  have hD := C.isOpen_frozenClockRadiusOpenRectangle R sL sR tL tR
  have hDsub : D ⊆ C.frozenQuadraticLegalDomain id :=
    C.frozenClockRadiusOpenRectangle_subset_original_region hs ht hclockgap
  have hmodel (i j : Fin 2) : (ξ i, η j) ∈ D :=
    ⟨⟨hξclock i, hηclock j⟩, hξR i, hηR j⟩
  obtain ⟨i, hγi, hi, hleft, hright⟩ :=
    exists_cavityLegalBasisCycleIndex_of_strict_cycle_above
      (C.frozenQuadraticCost A.frozenCenter) D hD
      ((C.continuousOn_frozenQuadraticCost_clock_region
        (T.subset A.frozenCenter_mem)).mono hDsub)
      isTopologicalBasis_cavitySpatialBasis isTopologicalBasis_cavitySpatialBasis
      γ hγ.le (ξ 0) (ξ 1) (η 0) (η 1)
      (hmodel 0 0) (hmodel 1 1) (hmodel 0 1) (hmodel 1 0) hgap
  obtain ⟨hdisj, hdisjt⟩ := hi.1.disjoint ⟨(ξ 0, η 0), hleft⟩ ⟨(ξ 1, η 1), hright⟩
  obtain ⟨phaseSize, hphaseSize, offset, hphase⟩ :=
    exists_phaseCell_of_cavitySpatialBasis i.1.1.1.property i.1.2.1.property
  refine ⟨i, hγi, hi, hleft, hright, hdisj, hdisjt,
    ⟨phaseSize, hphaseSize, offset, hphase⟩, ?_⟩
  intro scale hscale root hmacro n Y x hx x' hx' hAx hAx' j hj hBy l hl hBy'
  let Xp : Fin 2 → M := ![x, x']
  let Yp : Fin 2 → M := ![Y j, Y l]
  have hlegal := hi.2 (C.actualSeedRootedEndpoint scale root x) hAx
    (C.actualSeedRootedEndpoint scale root (Y j)) hBy
    (C.actualSeedRootedEndpoint scale root x') hAx'
    (C.actualSeedRootedEndpoint scale root (Y l)) hBy'
  have hpair (k l : Fin 2) :
      (C.actualSeedRootedEndpoint scale root (Xp k),
        C.actualSeedRootedEndpoint scale root (Yp l)) ∈ D := by
    fin_cases k <;> fin_cases l
    · simpa [Xp, Yp] using hlegal.1
    · simpa [Xp, Yp] using hlegal.2.2.1
    · simpa [Xp, Yp] using hlegal.2.2.2
    · simpa [Xp, Yp] using hlegal.2.1
  have hXR (k : Fin 2) : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale (Xp k) - root‖ ≤ R := (hpair k 0).2.1.le
  have hYR (l : Fin 2) : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale (Yp l) - root‖ ≤ R := (hpair 0 l).2.2.le
  have hclock (k l : Fin 2) : (u (Xp k), u (Yp l)) ∈ C.window.region :=
    hDsub (hpair k l)
  have hX (k : Fin 2) : a (Xp k) ∈ K ∧ Xp k ∈ F.potentialRegularDomain u := by
    fin_cases k
    · simpa [Xp] using hsource x hx
    · simpa [Xp] using hsource x' hx'
  have hY (k : Fin 2) : a (Yp k) ∈ K ∧ Yp k ∈ F.potentialRegularDomain u := by
    fin_cases k
    · simpa [Yp] using htarget (Y j) hj
    · simpa [Yp] using htarget (Y l) hl
  have hfrozen : γ ≤
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (Xp 0) (Yp 0) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (Xp 1) (Yp 1) -
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (Xp 0) (Yp 1) -
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (Xp 1) (Yp 0) := by
    simp only [actualFrozenRootedQuadratic_eq_frozenQuadraticCost_endpoint]
    exact hγi.le.trans (hi.1.2 (C.actualSeedRootedEndpoint scale root x) hAx
      (C.actualSeedRootedEndpoint scale root (Y j)) hBy
      (C.actualSeedRootedEndpoint scale root x') hAx'
      (C.actualSeedRootedEndpoint scale root (Y l)) hBy')
  have hphysical := (hcycles scale hscale root hmacro Xp Yp
    (fun k ↦ (hX k).1) (fun l ↦ (hY l).1) hXR hYR hclock
    (fun k ↦ (hX k).2) (fun l ↦ (hY l).2) hfrozen).2
  simpa [Xp, Yp] using hphysical

end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
