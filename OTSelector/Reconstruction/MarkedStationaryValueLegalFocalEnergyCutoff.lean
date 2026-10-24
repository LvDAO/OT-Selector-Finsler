import OTSelector.Reconstruction.MarkedStationaryValueLegalAllowedEnergyExtension

/-!
# Continuous minorants supported on original interior clock collars

Tietze extension is used only on the compact support of the chosen clock
cutoff, with the entire displacement retained. Multiplying that extension by
the cutoff gives a global nonnegative continuous test below the actual shifted
signed cost on every original legal carrier pair.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Positive semidefiniteness on the actual closed carrier suffices to
construct its nonnegative continuous shifted-energy test. -/
theorem exists_continuous_nonnegative_matrix_shifted_energy
    (q : ℕ) {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosSemidef)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) K)
    {G : ℝ} (hgb : ∀ w ∈ K, |g w.1 w.2| ≤ G) (t : ℝ) :
    ∃ F : C(PhysicalPairPalmMark (Fin q), ℝ), (∀ m, 0 ≤ F m) ∧
      ∀ m : PhysicalPairPalmMark (Fin q), m.1 ∈ K →
        F m = matrixQuadratic (matrix m.1) m.2 + t * g m.1.1 m.1.2 + |t| * G := by
  let S : Set (PhysicalPairPalmMark (Fin q)) := K ×ˢ univ
  let H (m : PhysicalPairPalmMark (Fin q)) :=
    matrixQuadratic (matrix m.1) m.2 + t * g m.1.1 m.1.2 + |t| * G
  have hH : ContinuousOn H S := by
    have hg' : ContinuousOn (fun m : PhysicalPairPalmMark (Fin q) ↦ g m.1.1 m.1.2) S :=
      hg.comp continuous_fst.continuousOn (fun m hm ↦ hm.1)
    exact ((continuousOn_matrixQuadratic_field hmatrix univ).add
      (continuousOn_const.mul hg')).add continuousOn_const
  let H' : C(S, ℝ) := ⟨fun m ↦ H m, continuousOn_iff_continuous_domRestrict.mp hH⟩
  obtain ⟨E, hE⟩ := H'.exists_restrict_eq (hK.prod isClosed_univ)
  let F : C(PhysicalPairPalmMark (Fin q), ℝ) :=
    ⟨fun m ↦ max (E m) 0, E.continuous.max continuous_const⟩
  refine ⟨F, fun m ↦ le_max_right _ _, fun m hm ↦ ?_⟩
  have hEm : E m = H m := congrArg (fun f : C(S, ℝ) ↦ f ⟨m, hm, mem_univ _⟩) hE
  have habs : |t * g m.1.1 m.1.2| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb m.1 hm) (abs_nonneg t)
  have hkin : 0 ≤ matrixQuadratic (matrix m.1) m.2 := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa only [star_trivial] using (hpos m.1 hm).dotProduct_mulVec_nonneg m.2
  have hn : 0 ≤ H m := by dsimp [H]; linarith [(abs_le.mp habs).1]
  change max (E m) 0 = _
  rw [hEm, max_eq_left hn]

/-- A compact interior clock cutoff gives an actual continuous legal energy
minorant, with exact cutoff-weighted value on the unchanged original carrier.
No values or continuity of the original kernel off that carrier are used. -/
theorem exists_continuous_legal_clockCutoff_shifted_minorant
    (q : ℕ) {O W : Set (ℝ × ℝ)}
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix O) (hpos : ∀ w ∈ O, (matrix w).PosSemidef)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hactual : ∀ w ∈ W, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) O)
    {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (χ : C_c(ℝ × ℝ, ℝ)) (hχ : ∀ w, χ w ∈ Icc 0 1) (hχO : tsupport χ ⊆ O) :
    ∃ F : C(PhysicalPairPalmMark (Fin q), ℝ), (∀ m, 0 ≤ F m) ∧
      (∀ m : PhysicalPairPalmMark (Fin q), m.1 ∈ W →
        F m = χ m.1 * (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G)) ∧
      ∀ m : PhysicalPairPalmMark (Fin q), m.1 ∈ W →
        F m ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G := by
  obtain ⟨H, hHn, hH⟩ := exists_continuous_nonnegative_matrix_shifted_energy q (isClosed_tsupport χ)
    matrix (hmatrix.mono hχO) (fun w hw ↦ hpos w (hχO hw)) (hg.mono hχO)
    (fun w _ ↦ hgb w.1 w.2) t
  let F : C(PhysicalPairPalmMark (Fin q), ℝ) :=
    ⟨fun m ↦ χ m.1 * H m, (χ.continuous.comp continuous_fst).mul H.continuous⟩
  have heq (m : PhysicalPairPalmMark (Fin q)) (hm : m.1 ∈ W) :
      F m = χ m.1 * (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G) := by
    by_cases hz : χ m.1 = 0
    · change χ m.1 * H m = _
      rw [hz, zero_mul, zero_mul]
    · change χ m.1 * H m = _
      rw [hH m (subset_closure hz), ← hactual m.1 hm m.2]
  refine ⟨F, fun m ↦ mul_nonneg (hχ m.1).1 (hHn m), heq, fun m hm ↦ ?_⟩
  rw [heq m hm]
  have habs : |t * g m.1.1 m.1.2| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb m.1.1 m.1.2) (abs_nonneg t)
  have hcost : 0 ≤ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G := by
    linarith [(abs_le.mp habs).1, hkn m.1.1 m.1.2 m.2]
  exact mul_le_of_le_one_left hcost (hχ m.1).2

end OTSelector.Reconstruction
