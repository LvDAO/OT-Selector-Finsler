import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingRate
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingPhysicalGeometry

/-! A literal affine pushforward of the constructed iid population coupling
retains the original physical observations and pays the genuine Euclidean cost. -/
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {q n : ℕ}

/-- The actual finite transport from original physical cube atoms to n times
the full physical cube population, with no auxiliary-cloud observations left. -/
def originalIIDPhysicalCubePopulationCoupling
    (μ : Measure (DyadicUnitCube q)) (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (x : Fin n → DyadicUnitCube q) :
    Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)) :=
  (originalIIDPopulationCoupling μ
    (fun u v ↦ originalCubePopulationSquareCost (u, v)) x).map
      (Prod.map (originalIIDCubePhysicalMap z L) (originalIIDCubePhysicalMap z L))

/-- Both physical marginals are exact, including repeated or absent atoms. -/
theorem originalIIDPhysicalCubePopulationCoupling_marginals
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (x : Fin n → DyadicUnitCube q) :
    let Γ := originalIIDPhysicalCubePopulationCoupling μ z L x
    IsFiniteMeasure Γ ∧
      Γ.map Prod.fst = ∑ i, Measure.dirac (originalIIDCubePhysicalMap z L (x i)) ∧
      Γ.map Prod.snd = (n : ℝ≥0∞) • μ.map (originalIIDCubePhysicalMap z L) := by
  let F := originalIIDCubePhysicalMap z L
  have hF := measurable_originalIIDCubePhysicalMap z L
  have hΓ := originalIIDCubePopulationCoupling_marginals μ x
  have : IsFiniteMeasure (originalIIDPopulationCoupling μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v)) x) := hΓ.1
  refine ⟨by unfold originalIIDPhysicalCubePopulationCoupling; infer_instance, ?_, ?_⟩
  · change ((originalIIDPopulationCoupling μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v)) x).map (Prod.map F F)).map
        Prod.fst = _
    rw [Measure.map_map measurable_fst (hF.prodMap hF)]
    change (originalIIDPopulationCoupling μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v)) x).map (F ∘ Prod.fst) = _
    rw [← Measure.map_map hF measurable_fst, hΓ.2.1,
      Measure.map_finset_sum' hF.aemeasurable]
    simp only [Measure.map_dirac' hF]
  · change ((originalIIDPopulationCoupling μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v)) x).map (Prod.map F F)).map
        Prod.snd = _
    rw [Measure.map_map measurable_snd (hF.prodMap hF)]
    change (originalIIDPopulationCoupling μ
      (fun u v ↦ originalCubePopulationSquareCost (u, v)) x).map (F ∘ Prod.snd) = _
    rw [← Measure.map_map hF measurable_snd, hΓ.2.2, Measure.map_smul]

/-- The actual physical population plans form a measurable family. -/
theorem measurable_originalIIDPhysicalCubePopulationCoupling
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (originalIIDPhysicalCubePopulationCoupling (n := n) μ z L) :=
  (Measure.measurable_map _ ((measurable_originalIIDCubePhysicalMap z L).prodMap
    (measurable_originalIIDCubePhysicalMap z L))).comp
      (measurable_originalIIDCubePopulationCoupling μ)

/-- Literal physical square energy is integrable and obeys the affine cube
scaling bound proved from the actual Euclidean norm. -/
theorem originalIIDPhysicalCubePopulationCoupling_squareCost_le
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (x : Fin n → DyadicUnitCube q) :
    Integrable (fun p ↦ ‖p.1 - p.2‖ ^ 2)
      (originalIIDPhysicalCubePopulationCoupling μ z L x) ∧
    (∫ p, ‖p.1 - p.2‖ ^ 2 ∂originalIIDPhysicalCubePopulationCoupling μ z L x) ≤
      ((q : ℝ) * L ^ 2) * (∫ p, originalCubePopulationSquareCost p
        ∂originalIIDPopulationCoupling μ
          (fun u v ↦ originalCubePopulationSquareCost (u, v)) x) := by
  let F := originalIIDCubePhysicalMap z L
  let Γ := originalIIDPopulationCoupling μ
    (fun u v ↦ originalCubePopulationSquareCost (u, v)) x
  let c : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q) → ℝ :=
    fun p ↦ ‖p.1 - p.2‖ ^ 2
  have hc : Measurable c := (measurable_fst.sub measurable_snd).norm.pow_const 2
  have hF := measurable_originalIIDCubePhysicalMap z L
  have hK : 0 ≤ (q : ℝ) * L ^ 2 := mul_nonneg (Nat.cast_nonneg q) (sq_nonneg L)
  have hI := integrable_originalIIDCubePopulationCoupling_squareCost μ x
  have hbound (p : DyadicUnitCube q × DyadicUnitCube q) :
      c (Prod.map F F p) ≤ ((q : ℝ) * L ^ 2) * originalCubePopulationSquareCost p :=
    originalIIDCubePhysicalMap_squareCost_le z L p.1 p.2
  have hcompI : Integrable (c ∘ Prod.map F F) Γ :=
    (hI.const_mul ((q : ℝ) * L ^ 2)).mono'
      (hc.comp (hF.prodMap hF)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbound p))
  have hmapI : Integrable c (Γ.map (Prod.map F F)) :=
    (integrable_map_measure hc.aestronglyMeasurable (hF.prodMap hF).aemeasurable).2 hcompI
  refine ⟨hmapI, ?_⟩
  change (∫ p, c p ∂Γ.map (Prod.map F F)) ≤ _
  rw [integral_map (hF.prodMap hF).aemeasurable hc.aestronglyMeasurable,
    ← integral_const_mul]
  exact integral_mono_ae hcompI (hI.const_mul _) (Filter.Eventually.of_forall hbound)

/-- The actual empirical-to-population physical plans satisfy the Euclidean
expected square-cost rate with the literal side-length factor q*L^2. -/
theorem expected_originalIIDPhysicalCubePopulationCoupling_squareCost_rate (hq : 4 < q)
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Integrable (fun x : Fin n → DyadicUnitCube q ↦
      ∫ p, ‖p.1 - p.2‖ ^ 2 ∂originalIIDPhysicalCubePopulationCoupling μ z L x)
      (Measure.pi (fun _ : Fin n ↦ μ)) ∧
    (∫ x, ∫ p, ‖p.1 - p.2‖ ^ 2 ∂originalIIDPhysicalCubePopulationCoupling μ z L x
      ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
        ((q : ℝ) * L ^ 2) * dyadicMatchingConstant q *
          (n : ℝ) ^ (1 - 2 / (q : ℝ)) := by
  let c : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q) → ℝ :=
    fun p ↦ ‖p.1 - p.2‖ ^ 2
  have hc : Measurable c := (measurable_fst.sub measurable_snd).norm.pow_const 2
  have hnonneg (x : Fin n → DyadicUnitCube q) :
      0 ≤ ∫ p, c p ∂originalIIDPhysicalCubePopulationCoupling μ z L x :=
    integral_nonneg (fun _ ↦ sq_nonneg _)
  have hm : Measurable (fun x : Fin n → DyadicUnitCube q ↦
      ∫ p, c p ∂originalIIDPhysicalCubePopulationCoupling μ z L x) := by
    have hread := (Measure.measurable_lintegral hc.ennreal_ofReal).comp
      (measurable_originalIIDPhysicalCubePopulationCoupling (n := n) μ z L)
    convert hread.ennreal_toReal using 1
    funext x
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
      (fun _ ↦ sq_nonneg _)) hc.aestronglyMeasurable
  have hcube := expected_originalIIDCubePopulationCoupling_squareCost_rate (n := n) hq μ
  have hK : 0 ≤ (q : ℝ) * L ^ 2 := mul_nonneg (Nat.cast_nonneg q) (sq_nonneg L)
  have hI := (hcube.1.const_mul ((q : ℝ) * L ^ 2)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
      exact (originalIIDPhysicalCubePopulationCoupling_squareCost_le μ z L x).2))
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ((q : ℝ) * L ^ 2) * (∫ x, ∫ p, originalCubePopulationSquareCost p
        ∂originalIIDPopulationCoupling μ
          (fun u v ↦ originalCubePopulationSquareCost (u, v)) x
        ∂Measure.pi (fun _ : Fin n ↦ μ)) := by
      rw [← integral_const_mul]
      exact integral_mono_ae hI (hcube.1.const_mul _)
        (Filter.Eventually.of_forall (fun x ↦
          (originalIIDPhysicalCubePopulationCoupling_squareCost_le μ z L x).2))
    _ ≤ _ := (mul_le_mul_of_nonneg_left hcube.2 hK).trans_eq (by ring)

end OTSelector.Reconstruction
