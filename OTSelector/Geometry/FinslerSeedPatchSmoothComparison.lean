import OTSelector.Geometry.FinslerSeedPatchEnergyTangency
import OTSelector.Geometry.FinslerSmoothPhaseJetData

/-!
# Smooth comparisons for almost every actual original seed

Actual label differentiability, immersion, normality and the original unit-energy
constraint construct complete smooth comparison families. They retain the original
label anchor, central curve and every legal joint phase first derivative. Their
comparison neighborhoods stay in the original open label domain.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Almost every actual seed label has a complete C² comparison with the same
central original curve and the same joint phase jet in every legal chart. -/
theorem ae_exists_smoothPhaseJetComparison (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.labels,
      let R := fderiv ℝ D.position w
      let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
      let p := (D.position w, fderiv ℝ D.potential (D.position w))
      w ∈ S.labels ∧
        ∃ C : F.SmoothPhaseJetComparison D.initialChart 0 w p R Q,
          C.labels ⊆ S.openLabels ∧ S.curve w = C.curve w ∧
          ∀ (terminal : M) (t : ℝ),
            S.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
            HasFDerivAt (F.chartMomentumFamily terminal S.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t) ∧
            HasFDerivAt (F.chartMomentumFamily terminal C.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t) := by
  filter_upwards [S.ae_initial_phase_regular_energy D hF m] with w hwdata
  obtain ⟨hw, _, hR, hnormal, hQ, _, hiso, e, he, hsource, hInv, hp, henergy, hzero⟩ :=
    hwdata
  let R := fderiv ℝ D.position w
  let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
  let p := (D.position w, fderiv ℝ D.potential (D.position w))
  have hsym (ξ η : S.covector.ker) : Q ξ (R η) = Q η (R ξ) := by
    have hi := hiso ξ η
    change Q η (R ξ) - Q ξ (R η) = 0 at hi
    exact (sub_eq_zero.mp hi).symm
  have hnorm (ξ : S.covector.ker) : p.2 (R ξ) = 0 :=
    congrArg (fun L : S.covector.ker →L[ℝ] ℝ ↦ L ξ) hnormal
  obtain ⟨C⟩ := hF.nonempty_smoothPhaseJetComparison hcomplete D.initialChart 0 w
    he hsource hInv hp henergy R Q hzero hR hsym hnorm
  let C' : F.SmoothPhaseJetComparison D.initialChart 0 w p R Q :=
    { C with
      labels := C.labels ∩ S.openLabels
      open_labels := C.open_labels.inter S.openLabels_open
      anchor_mem := ⟨C.anchor_mem, S.labels_subset hw⟩
      complete := fun z hz ↦ C.complete z hz.1
      initial_source := fun z hz ↦ C.initial_source z hz.1
      tangent_C2 := C.tangent_C2.mono (fun _ hq ↦ ⟨hq.1.1, hq.2⟩)
      energy_eq := fun z hz ↦ C.energy_eq z hz.1 }
  have hsub : C'.labels ⊆ S.openLabels := inter_subset_right
  have hsame := S.same_phase_firstJet_of_initial_phase D hF hcomplete
    (S.labels_subset hw) hQ C'.open_labels C'.anchor_mem hsub C'.complete
      C'.initial_source C'.initial_jet C'.initial_phase
  refine ⟨hw, C', hsub, hsame.1, ?_⟩
  intro terminal t ht
  rw [hsame.1] at ht
  exact hsame.2 terminal t ht

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
