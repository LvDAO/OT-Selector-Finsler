import OTSelector.Reconstruction.OriginalBirthMobilityBounds

/-!
# Birth geometry produced by the actual general Finsler data

Both endpoint theorems produce the residue, comparison constants, canonical
birth frame, actual short-leg bounds, actual full opposite-leg lower bound, and
scaled physical mobility norm. No normalized-leg or mobility oracle is supplied.
-/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual left endpoint produces all birth-scale geometric inputs with
one unchanged residue and one canonical frame at each pair of physical scales. -/
theorem exists_original_left_birth_normalizedGeometry
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ v ∈ Ioo 0 ε,
        (originalSeedKernel S w (D.lo + v) - c • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
        (C • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.lo + v)).PosSemidef) ∧
      ∃ B ≥ 0,
      (∀ {t s r : ℝ}, 0 < t → 0 < s → 4 * t < ε → r ∈ Icc (t / 2) (4 * t) →
        let T := positiveMatrixNormalizer (birthResidueScale G t s)
        ‖s • (T * originalSeedKernel S w (D.lo + r) * Tᵀ)‖ ≤ B) ∧
      ∀ {t s a r b : ℝ}, 0 < t → 0 < s → s ≤ t → 8 * t < ε →
        t / 2 ≤ a → a ≤ r → r ≤ 4 * t → s / 8 ≤ r - a → r - a ≤ 2 * s →
        b - (S.level : ℝ) ∈ Ioo D.lo D.hi → (S.level : ℝ) + D.lo + 8 * t ≤ b →
        let T := positiveMatrixNormalizer (birthResidueScale G t s)
        IsUnit T.det ∧
          (T * originalSeedClockCompliance S w ((S.level : ℝ) + D.lo + a)
            ((S.level : ℝ) + D.lo + r) * Tᵀ - (c / 128) • 1).PosSemidef ∧
          ((8 * C) • 1 - T * originalSeedClockCompliance S w
            ((S.level : ℝ) + D.lo + a) ((S.level : ℝ) + D.lo + r) * Tᵀ).PosSemidef ∧
          (T * originalSeedClockCompliance S w ((S.level : ℝ) + D.lo + r) b * Tᵀ -
            (c / 128) • 1).PosSemidef := by
  obtain ⟨ε, hε, hεspan, G, Rem, hG, _, _, c, hc, C, hC, hcomp⟩ :=
    D.exists_original_kernel_left_pole_loewner_comparison hF hw
  obtain ⟨B, hB, hnorm⟩ := D.original_left_birth_mobility_bound_of_comparison
    hF hw hG hεspan hC.le (fun v hv ↦ (hcomp v hv).2)
  refine ⟨ε, hε, hεspan, G, hG, c, C, hc, hC, hcomp, B, hB, hnorm, ?_⟩
  intro t s a r b ht hs hst htε ha har hr hlenL hlenU hb hfar
  have hlenL' : (1 / 8 : ℝ) * s ≤ r - a := by linarith
  have h := D.original_left_birth_normalizedLegs_of_comparison hF hw hG hεspan hc.le hC.le
    hcomp ht hs hst htε ha har hr hlenL' hlenU hb hfar
  refine ⟨h.1, ?_, ?_, ?_⟩
  · convert h.2.1 using 1
    module
  · convert h.2.2.1 using 1
    module
  · exact scalar_identity_lower_bound_mono (by linarith : c / 128 ≤ c / 8) h.2.2.2

/-- Actual right-endpoint deaths supply the same birth-scale inputs, with the
short target and long source retained in their original forward orientation. -/
theorem exists_original_right_birth_normalizedGeometry
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ v ∈ Ioo 0 ε,
        (originalSeedKernel S w (D.hi - v) - c • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
        (C • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.hi - v)).PosSemidef) ∧
      ∃ B ≥ 0,
      (∀ {t s r : ℝ}, 0 < t → 0 < s → 4 * t < ε → r ∈ Icc (t / 2) (4 * t) →
        let T := positiveMatrixNormalizer (birthResidueScale G t s)
        ‖s • (T * originalSeedKernel S w (D.hi - r) * Tᵀ)‖ ≤ B) ∧
      ∀ {t s a r b : ℝ}, 0 < t → 0 < s → s ≤ t → 8 * t < ε →
        t / 2 ≤ a → a ≤ r → r ≤ 4 * t → s / 8 ≤ r - a → r - a ≤ 2 * s →
        b - (S.level : ℝ) ∈ Ioo D.lo D.hi → b ≤ (S.level : ℝ) + D.hi - 8 * t →
        let T := positiveMatrixNormalizer (birthResidueScale G t s)
        IsUnit T.det ∧
          (T * originalSeedClockCompliance S w ((S.level : ℝ) + D.hi - r)
            ((S.level : ℝ) + D.hi - a) * Tᵀ - (c / 128) • 1).PosSemidef ∧
          ((8 * C) • 1 - T * originalSeedClockCompliance S w
            ((S.level : ℝ) + D.hi - r) ((S.level : ℝ) + D.hi - a) * Tᵀ).PosSemidef ∧
          (T * originalSeedClockCompliance S w b ((S.level : ℝ) + D.hi - r) * Tᵀ -
            (c / 128) • 1).PosSemidef := by
  obtain ⟨ε, hε, hεspan, G, Rem, hG, _, _, c, hc, C, hC, hcomp⟩ :=
    D.exists_original_kernel_right_pole_loewner_comparison hF hw
  obtain ⟨B, hB, hnorm⟩ := D.original_right_birth_mobility_bound_of_comparison
    hF hw hG hεspan hC.le (fun v hv ↦ (hcomp v hv).2)
  refine ⟨ε, hε, hεspan, G, hG, c, C, hc, hC, hcomp, B, hB, hnorm, ?_⟩
  intro t s a r b ht hs hst htε ha har hr hlenL hlenU hb hfar
  have hlenL' : (1 / 8 : ℝ) * s ≤ r - a := by linarith
  have h := D.original_right_birth_normalizedLegs_of_comparison hF hw hG hεspan hc.le hC.le
    hcomp ht hs hst htε ha har hr hlenL' hlenU hb hfar
  refine ⟨h.1, ?_, ?_, ?_⟩
  · convert h.2.1 using 1
    module
  · convert h.2.2.1 using 1
    module
  · exact scalar_identity_lower_bound_mono (by linarith : c / 128 ≤ c / 8) h.2.2.2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
