import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalKinetic
import OTSelector.Reconstruction.MarkedStationaryValueLegalFocalFullScene

/-!
# The original conditional focal coefficient produces its own full input scene

The only coefficient used is the original seed inverse compliance. Its bounded
measurable kinetic carrier, compact interior coercivity, finite scalar bins and
all actual legal count deficits are produced inside the theorem from the same
original two conditional populations and their original forward coupling.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff CompactlySupported Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
local instance markedStationaryValueLegalOriginalFocalFullSceneInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalOriginalFocalFullScenePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Genuine original conditional geometry constructs the actual real legal
pressure and a jointly stationary full original Poisson input weak scene of
its own canonical finite optima, including focal endpoint degeneration. -/
theorem exists_stationary_original_focal_fullInput_scene
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} (hG : 0 ≤ G) {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    let _ : IsProbabilityMeasure μ := D.support.source.probability
    let _ : IsProbabilityMeasure ν := D.support.target.probability
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id μ ν (D.originalFocalKinetic gap) g R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p ∧
      ∀ t : ℝ, ∃ (L : ℕ → ℝ) (hL : ∀ k, 0 < L k), Tendsto L atTop atTop ∧
        ∃ Q : ProbabilityMeasure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)), ∃ φ : ℕ → ℕ,
          StrictMono φ ∧ Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) (D.measurable_originalFocalKinetic hF hw gap) g hg t
            (L (φ k)) (hL (φ k))) atTop (𝓝 Q) ∧
          (∀ v : Fin (finrank ℝ S.covector.ker) → ℝ, MeasurePreserving (legalMarkedInputSceneReroot (finrank ℝ S.covector.ker) v)
            (Q : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) (Q : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ∧
          (∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
            (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst = legalInputColorMeasure (finrank ℝ S.covector.ker) s.2 0 ∧
              (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd = legalInputColorMeasure (finrank ℝ S.covector.ker) s.2 1) ∧
          (∀ (radius : ℝ), 0 < radius → ∀ (F : C_c(LegalColoredInputPoint (finrank ℝ S.covector.ker), ℝ)) (hF : ∀ x, 0 ≤ F x),
            (∀ (x : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker)) (c : Fin 2),
              x.1 ∉ haarRootCube (Fin (finrank ℝ S.covector.ker)) radius → F (x, c) = 0) →
            (∫ s, legalMarkedInputSceneLaplace (finrank ℝ S.covector.ker) F hF s ∂(Q : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
              ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
                ∂legalInputPoissonWindowLaw (finrank ℝ S.covector.ker) (haarRootCube (Fin (finrank ℝ S.covector.ker)) radius) μ ν) := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let I : Set ℝ := μ.support ∪ ν.support
  have hI : IsCompact I := hbounds.source_compact.union hbounds.target_compact
  obtain ⟨bins⟩ := exists_finiteScalarBins hI hgap
  have hsrc : ∀ᵐ p ∂π, p.1 ∈ μ.support :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact μ.support_mem_ae)
  have htgt : ∀ᵐ p ∂π, p.2 ∈ ν.support :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact ν.support_mem_ae)
  have hcarry : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I :=
    (hsrc.and htgt).mono (fun _ h ↦ ⟨Or.inl h.1, Or.inr h.2⟩)
  have hsep : ∀ᵐ p ∂μ.prod ν, gap ≤ |p.2 - p.1| := by
    filter_upwards [ae_fst_of_ae μ.support_mem_ae, ae_snd_of_ae ν.support_mem_ae] with p hp hq
    simpa only [Real.dist_eq, abs_sub_comm] using hbounds.separated p.1 hp p.2 hq
  obtain ⟨C, hC, hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  exact bins.exists_stationary_fullInput_legalMarkedPressure_limit_of_interior hgap hI.measurableSet
    π μ ν hπ hcarry (hbounds.ae_clock_gap_of_coupling hπ horder) hsep
    (finrank ℝ S.covector.ker) hq hC hG (D.measurable_originalFocalKinetic hF hw gap)
    (D.originalFocalKinetic_nonneg hF hw hgap) hkb
    (fun a b c _ v ↦ D.originalFocalKinetic_homogeneous gap a b c v) hg hgb
    (measurableSet_Ioo.preimage ((measurable_id : Measurable (id : ℝ → ℝ)).sub_const (S.level : ℝ)))
    μ.isClosed_support.measurableSet ν.isClosed_support.measurableSet
    (ae_iff.mp D.support.source.ae_open) (ae_iff.mp D.support.target.ae_open)
    μ.measure_compl_support ν.measure_compl_support
    (fun a ha b hb ↦ by simpa only [Real.dist_eq, abs_sub_comm] using hbounds.separated a ha b hb)
    (originalSeedPairCoefficient S w) (D.continuousOn_pair_coefficient_interior hF hw)
    (fun p hp hq hpq ↦ (D.pair_compliance_posDef hF hw hp hq hpq).2)
    (fun _ ha _ hb hab v ↦ D.originalFocalKinetic_eq_of_original_support hbounds ha hb hab v)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
