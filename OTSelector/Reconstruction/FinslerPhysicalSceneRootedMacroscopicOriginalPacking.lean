import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicOriginalCenter

/-!
# Actual original macro-coefficient cycles produce physical packing rectangles

Original compact coefficient bounds retain their role when choosing Taylor
accuracy. Strict cycles are tested at the original macro coefficient; the
internally selected Taylor reference only supplies the actual physical estimate.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module Topology TopologicalSpace
  OTSelector.Geometry OTSelector.Probability
open scoped Topology ContDiff ENNReal Classical
noncomputable section
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

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Original compact coefficient bounds are retained jointly with the
actual Taylor scale and physical four-edge estimate. -/
theorem exists_actualMacroscopicTaylorCycleGap_with_model_bound
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    (hrem : ∀ η > 0, ∃ radius > 0,
      ∀ z ∈ C.roots, C.SourceCoordinateRemainderBound z η radius)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {K : Set (ℚ → M)} (hK : IsCompact K) (hsub : K ⊆ C.roots)
    {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ K)
    (R : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ B > 0,
      (∀ z ∈ C.roots, ∀ p ∈ C.window.region,
        ∀ v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
        ‖v‖ ≤ 2 * |R| →
        0 ≤ matrixQuadratic (C.matrix z p) v ∧ matrixQuadratic (C.matrix z p) v ≤ B) ∧
      ∃ ε > 0, 2 * ε * (4 * B) ≤ γ / 2 ∧
      ∃ T : C.TaylorRootCover ε,
      ∃ A : C.ActualMacroscopicTaylorCertificate T K macroCenter,
      ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
      dist (physicalSceneMacroscopicRoot scale root)
        ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) < A.macroRadius →
      ∀ X Y : Fin 2 → M,
      (∀ i, a (X i) ∈ K) → (∀ j, a (Y j) ∈ K) →
      (∀ i, ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        C.seedIndex scale (X i) - root‖ ≤ R) →
      (∀ j, ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        C.seedIndex scale (Y j) - root‖ ≤ R) →
      (∀ i j, (u (X i), u (Y j)) ∈ C.window.region) →
      (∀ i, X i ∈ F.potentialRegularDomain u) →
      (∀ j, Y j ∈ F.potentialRegularDomain u) →
      let Q := fun i j ↦ C.actualFrozenRootedQuadratic A.frozenCenter scale root (X i) (Y j)
      let c := fun i j ↦ scale ^ 2 *
        ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i))
      γ ≤ Q 0 0 + Q 1 1 - Q 0 1 - Q 1 0 →
        Q 0 0 + Q 1 1 + Q 0 1 + Q 1 0 ≤ 4 * B ∧
        γ / 2 ≤ c 0 0 + c 1 1 - c 0 1 - c 1 0 := by
  obtain ⟨B, hB, hupper⟩ := C.exists_uniform_actualFrozenRootedQuadratic_bound R
  let ε := γ / (16 * (B + 1))
  have hden : 0 < 16 * (B + 1) := by positivity
  have hε : 0 < ε := div_pos hγ hden
  have heq : ε * (16 * (B + 1)) = γ := div_mul_cancel₀ _ hden.ne'
  have hbudget : 2 * ε * (4 * B) ≤ γ / 2 := by nlinarith
  obtain ⟨T, ⟨A⟩⟩ := C.exists_actualMacroscopicTaylorCertificate hF hcomplete hu ha hinj
    hlabel hrem hε hK hsub hmacroCenter
  obtain ⟨threshold, hthreshold, hedge⟩ :=
    A.exists_scale_threshold_of_regular hF hcomplete hu ha hinj hsub horder R
  refine ⟨B, hB, hupper, ε, hε, hbudget, T, A, threshold, hthreshold, ?_⟩
  intro scale hs root hmacro X Y hX hY hXR hYR hclock hXreg hYreg
  dsimp only
  intro hgap
  have hQupper (i j : Fin 2) :
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X i) (Y j) ≤ B :=
    (C.actualFrozenRootedQuadratic_le_of_bound hupper (T.subset A.frozenCenter_mem)
      scale root (hXR i) (hYR j) (hclock i j)).2
  have hsum : C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 0) (Y 0) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 1) (Y 1) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 0) (Y 1) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 1) (Y 0) ≤ 4 * B := by
    linarith [hQupper 0 0, hQupper 1 1, hQupper 0 1, hQupper 1 0]
  refine ⟨hsum, ?_⟩
  have hpair (i j : Fin 2) := hedge scale hs root hmacro (X i) (Y j)
    (hX i) (hY j) (hXR i) (hYR j) (hclock i j) (hXreg i) (hYreg j)
  exact four_edge_gap_of_relative_errors hε.le (hpair 0 0) (hpair 1 1) (hpair 0 1) (hpair 1 0)
    hgap hsum hbudget


/-- A cycle at the original macro coefficient produces legal countable
rectangles and a positive true physical gap on the same original masks. -/
theorem exists_actualMacroscopicTaylor_original_center_packing_certificate
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
      2 * γ < C.frozenQuadraticCost macroCenter (ξ 0) (η 0) +
        C.frozenQuadraticCost macroCenter (ξ 1) (η 1) -
        C.frozenQuadraticCost macroCenter (ξ 0) (η 1) -
        C.frozenQuadraticCost macroCenter (ξ 1) (η 0) →
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
  obtain ⟨B, hB, hupper, ε, hε, hbudget, T, A, threshold, hthreshold, hcycles⟩ :=
    C.exists_actualMacroscopicTaylorCycleGap_with_model_bound hF hcomplete hu ha hinj
      hlabel hrem horder hK hsub hmacroCenter R hγ
  refine ⟨ε, hε, T, A, threshold, hthreshold, ?_⟩
  intro ξ η hξR hηR hξclock hηclock hgapOriginal
  have hmodelClock (i j : Fin 2) : ((ξ i).2, (η j).2) ∈ C.window.region := by
    have hp : (ξ i, η j) ∈ C.frozenClockOpenRectangle sL sR tL tR :=
      ⟨hξclock i, hηclock j⟩
    exact C.frozenClockOpenRectangle_subset_original_region hs ht hclockgap hp
  have hgap := A.strict_cycle_of_original_macro hε.le (hsub hmacroCenter) hγ hupper hbudget
    ξ η (fun i ↦ (hξR i).le) (fun j ↦ (hηR j).le) hmodelClock hgapOriginal
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
