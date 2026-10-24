import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylor

/-!
# Original four-edge slack gaps from actual macroscopic Taylor certificates

The algebra sums four literal edge errors. The frozen quadratic evaluations
retain their actual clock pairs, the one certificate-selected original root,
and the actual rooted displacement. Compact original coefficient and clock
domains supply a uniform quadratic upper bound before the accuracy is chosen.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Four absolute edge errors can lower the original signed four-edge gap by
at most their sum. -/
theorem four_edge_gap_of_absolute_errors
    {c00 c11 c01 c10 Q00 Q11 Q01 Q10 e00 e11 e01 e10 γ : ℝ}
    (h00 : |c00 - Q00| ≤ e00) (h11 : |c11 - Q11| ≤ e11)
    (h01 : |c01 - Q01| ≤ e01) (h10 : |c10 - Q10| ≤ e10)
    (hgap : γ ≤ Q00 + Q11 - Q01 - Q10)
    (hbudget : e00 + e11 + e01 + e10 ≤ γ / 2) :
    γ / 2 ≤ c00 + c11 - c01 - c10 := by
  obtain ⟨hl00, hu00⟩ := abs_le.mp h00
  obtain ⟨hl11, hu11⟩ := abs_le.mp h11
  obtain ⟨hl01, hu01⟩ := abs_le.mp h01
  obtain ⟨hl10, hu10⟩ := abs_le.mp h10
  linarith

/-- The four Taylor relative errors consume at most the declared frozen
quadratic sum budget. -/
theorem four_edge_gap_of_relative_errors
    {c00 c11 c01 c10 Q00 Q11 Q01 Q10 ε M γ : ℝ} (hε : 0 ≤ ε)
    (h00 : |c00 - Q00| ≤ (2 * ε) * Q00)
    (h11 : |c11 - Q11| ≤ (2 * ε) * Q11)
    (h01 : |c01 - Q01| ≤ (2 * ε) * Q01)
    (h10 : |c10 - Q10| ≤ (2 * ε) * Q10)
    (hgap : γ ≤ Q00 + Q11 - Q01 - Q10)
    (hsum : Q00 + Q11 + Q01 + Q10 ≤ M)
    (hbudget : 2 * ε * M ≤ γ / 2) :
    γ / 2 ≤ c00 + c11 - c01 - c10 := by
  apply four_edge_gap_of_absolute_errors h00 h11 h01 h10 hgap
  have hfactor : 0 ≤ (2 : ℝ) * ε := mul_nonneg (by norm_num) hε
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  nlinarith

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

/-- The one original coefficient at its frozen root and actual clock pair,
evaluated on the actual rooted seed-basis displacement. -/
def actualFrozenRootedQuadratic (frozenRoot : ℚ → M) (scale : ℝ)
    (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (x y : M) : ℝ :=
  matrixQuadratic (C.matrix frozenRoot (u x, u y))
    ((physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale y - root) -
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale x - root))

/-- Compact original roots, the complete original scalar pair window, and a
bounded actual displacement produce an upper bound independent of Taylor
accuracy and the certificate's selected frozen center. -/
theorem exists_uniform_actualFrozenRootedQuadratic_bound (R : ℝ) :
    ∃ B > 0, ∀ z ∈ C.roots, ∀ p ∈ C.window.region,
      ∀ v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
      ‖v‖ ≤ 2 * |R| →
      0 ≤ matrixQuadratic (C.matrix z p) v ∧ matrixQuadratic (C.matrix z p) v ≤ B := by
  let V := Metric.closedBall
    (0 : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (2 * |R|)
  have hcompact := (C.roots_compact.prod C.window.isCompact_region).prod
    (isCompact_closedBall (0 : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
      (2 * |R|))
  have hq : ContinuousOn
      (fun q ↦ matrixQuadratic (C.matrix q.1.1 q.1.2) q.2)
      ((C.roots ×ˢ C.window.region) ×ˢ V) :=
    continuousOn_matrixQuadratic_field C.coefficient_continuous V
  obtain ⟨B, hB, hbound⟩ :=
    (hcompact.image_of_continuousOn hq).isBounded.exists_pos_norm_le
  obtain ⟨m, hm, hlower⟩ := C.exists_quadratic_lower_bound
  refine ⟨B, hB, ?_⟩
  intro z hz p hp v hv
  have hvV : v ∈ V := by simpa only [V, Metric.mem_closedBall, dist_zero_right] using hv
  have hnorm := hbound (matrixQuadratic (C.matrix z p) v)
    ⟨((z, p), v), ⟨⟨hz, hp⟩, hvV⟩, rfl⟩
  refine ⟨(mul_nonneg hm.le (sq_nonneg ‖v‖)).trans (hlower z hz p hp v), ?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)

/-- A bounded actual rooted window bounds every same-center frozen quadratic
evaluation, preserving the actual clock pair of that edge. -/
theorem actualFrozenRootedQuadratic_le_of_bound
    {B R : ℝ}
    (hbound : ∀ z ∈ C.roots, ∀ p ∈ C.window.region,
      ∀ v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
      ‖v‖ ≤ 2 * |R| →
      0 ≤ matrixQuadratic (C.matrix z p) v ∧ matrixQuadratic (C.matrix z p) v ≤ B)
    {c : ℚ → M} (hc : c ∈ C.roots) (scale : ℝ)
    (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    {x y : M}
    (hxR : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale x - root‖ ≤ R)
    (hyR : ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale y - root‖ ≤ R)
    (hp : (u x, u y) ∈ C.window.region) :
    0 ≤ C.actualFrozenRootedQuadratic c scale root x y ∧
      C.actualFrozenRootedQuadratic c scale root x y ≤ B := by
  apply hbound c hc (u x, u y) hp
  exact (norm_sub_le _ _).trans (by nlinarith [le_abs_self R])

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The one actual certificate controls all four edges at the same actual
macro tag, scale, original coefficient center, and original scalar clocks. -/
theorem ActualMacroscopicTaylorCertificate.original_four_edge_gap
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {T : C.TaylorRootCover ε} {K : Set (ℚ → M)} {macroCenter : ℚ → M}
    (A : C.ActualMacroscopicTaylorCertificate T K macroCenter) (hε : 0 ≤ ε)
    (hsub : K ⊆ C.roots)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (scale : ℝ) (hscale : 0 < scale)
    (root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (R : ℝ)
    (hmacro : dist (physicalSceneMacroscopicRoot scale root)
      ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) < A.macroRadius)
    (hsmall : R / scale < A.macroRadius)
    (X Y : Fin 2 → M) (hX : ∀ i, a (X i) ∈ K) (hY : ∀ j, a (Y j) ∈ K)
    (hXR : ∀ i, ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale (X i) - root‖ ≤ R)
    (hYR : ∀ j, ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      C.seedIndex scale (Y j) - root‖ ≤ R)
    (hclock : ∀ i j, (u (X i), u (Y j)) ∈ C.window.region)
    (hXreg : ∀ i, X i ∈ F.potentialRegularDomain u)
    (hYreg : ∀ j, Y j ∈ F.potentialRegularDomain u)
    {γ Mbound : ℝ}
    (hgap : γ ≤ C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 0) (Y 0) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 1) (Y 1) -
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 0) (Y 1) -
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 1) (Y 0))
    (hsum : C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 0) (Y 0) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 1) (Y 1) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 0) (Y 1) +
      C.actualFrozenRootedQuadratic A.frozenCenter scale root (X 1) (Y 0) ≤ Mbound)
    (hbudget : 2 * ε * Mbound ≤ γ / 2) :
    let c := fun i j ↦ scale ^ 2 *
      ((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i))
    γ / 2 ≤ c 0 0 + c 1 1 - c 0 1 - c 1 0 := by
  have hedge (i j : Fin 2) := A.relative_bound_of_regular hF hcomplete hu ha hinj
    hsub horder scale hscale root R hmacro hsmall (hX i) (hY j) (hXR i) (hYR j)
      (hclock i j) (hXreg i) (hYreg j)
  exact four_edge_gap_of_relative_errors hε (hedge 0 0) (hedge 1 1) (hedge 0 1) (hedge 1 0)
    hgap hsum hbudget

/-- The original compact coefficient field first supplies its uniform bounded
window budget. This chooses a positive Taylor accuracy before the actual cover
and frozen center, and then all four literal physical edges inherit half the
tested original frozen-quadratic gap at sufficiently large spatial scale. -/
theorem exists_actualMacroscopicTaylorCycleGap
    (hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots)
    (hrem : ∀ η > 0, ∃ radius > 0,
      ∀ z ∈ C.roots, C.SourceCoordinateRemainderBound z η radius)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {K : Set (ℚ → M)} (hK : IsCompact K) (hsub : K ⊆ C.roots)
    {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ K)
    (R : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ B > 0, ∃ ε > 0, 2 * ε * (4 * B) ≤ γ / 2 ∧
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
  refine ⟨B, hB, ε, hε, hbudget, T, A, threshold, hthreshold, ?_⟩
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

end OriginalPopulationCoefficientCore

variable {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {loss : ℝ≥0∞}

/-- The original local pressure core supplies all coefficient continuity and
Taylor remainder inputs internally, before this four-edge gap test is applied. -/
theorem PopulationLocalPressureCore.exists_actualMacroscopicTaylorCycleGap
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (i : Fin D.haar.continuous.count)
    {K : Set (ℚ → M)} (hK : IsCompact K)
    (hsub : K ⊆ (D.haar.continuous.coefficient i).roots)
    {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ K)
    (R : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    let C := D.haar.continuous.coefficient i
    ∃ B > 0, ∃ ε > 0, 2 * ε * (4 * B) ≤ γ / 2 ∧
      ∃ T : C.TaylorRootCover ε,
      ∃ A : C.ActualMacroscopicTaylorCertificate T K macroCenter,
      ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ root : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
      dist (physicalSceneMacroscopicRoot scale root)
        ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) < A.macroRadius →
      ∀ X Y : Fin 2 → M,
      (∀ k, a (X k) ∈ K) → (∀ j, a (Y j) ∈ K) →
      (∀ k, ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        C.seedIndex scale (X k) - root‖ ≤ R) →
      (∀ j, ‖physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        C.seedIndex scale (Y j) - root‖ ≤ R) →
      (∀ k j, (u (X k), u (Y j)) ∈ C.window.region) →
      (∀ k, X k ∈ F.potentialRegularDomain u) →
      (∀ j, Y j ∈ F.potentialRegularDomain u) →
      let Q := fun k j ↦ C.actualFrozenRootedQuadratic A.frozenCenter scale root (X k) (Y j)
      let c := fun k j ↦ scale ^ 2 *
        ((F.lengthEDist (X k) (Y j)).toReal - u (Y j) + u (X k))
      γ ≤ Q 0 0 + Q 1 1 - Q 0 1 - Q 1 0 →
        Q 0 0 + Q 1 1 + Q 0 1 + Q 1 0 ≤ 4 * B ∧
        γ / 2 ≤ c 0 0 + c 1 1 - c 0 1 - c 1 0 := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  have hlabel : ContinuousOn
      (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    rw [← D.haar.intensity_roots i]
    exact (D.haar.intensity i).continuous_label
  exact C.exists_actualMacroscopicTaylorCycleGap hF hcomplete hu ha hinj hlabel
    (D.source_remainder_on_piece hF hcomplete hu ha hinj i) horder hK hsub hmacroCenter R hγ

end OTSelector.Reconstruction
