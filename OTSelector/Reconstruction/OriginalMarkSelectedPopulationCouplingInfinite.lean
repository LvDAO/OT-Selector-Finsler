import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawInfinite
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingPhysical

/-! Actual finite selections of the original infinite iid reserve feed the
physical population plan under finite, unnormalized auxiliary event laws. -/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X] {n q : ℕ}

/-- The actual original positions selected by an auxiliary-only Nat injection. -/
def originalMarkSelectedInfinitePositions (e : Z → Fin n ↪ ℕ)
    (p : Z × (ℕ → X)) : Fin n → X := fun j ↦ p.2 (e p.1 j)

/-- Evaluation at the actual countably indexed, auxiliary-selected coordinates
is measurable without replacing any original position. -/
theorem measurable_originalMarkSelectedInfinitePositions (e : Z → Fin n ↪ ℕ)
    (he : ∀ j, Measurable (fun z ↦ e z j)) :
    Measurable (originalMarkSelectedInfinitePositions (X := X) e) := by
  apply measurable_pi_lambda
  intro j
  have heval : Measurable (fun p : (ℕ → X) × ℕ ↦ p.1 p.2) :=
    measurable_from_prod_countable_left (fun i ↦ measurable_pi_apply i)
  exact heval.comp (measurable_snd.prodMk ((he j).comp measurable_fst))

/-- The true joint law retains the entire auxiliary event data and its mass. -/
theorem measurePreserving_originalMarkSelectedInfiniteJoint
    (μ : Measure X) [IsProbabilityMeasure μ] (P : Measure Z) [IsFiniteMeasure P]
    (e : Z → Fin n ↪ ℕ) (he : ∀ j, Measurable (fun z ↦ e z j)) :
    MeasurePreserving (fun p ↦ (p.1, originalMarkSelectedInfinitePositions (X := X) e p))
      (P.prod (Measure.infinitePi (fun _ : ℕ ↦ μ)))
      (P.prod (Measure.pi (fun _ : Fin n ↦ μ))) :=
  ⟨measurable_fst.prodMk (measurable_originalMarkSelectedInfinitePositions e he),
    OTSelector.Probability.map_mark_selected_original_infinite_iid_positions μ P e he⟩

/-- The actual physical population plan starts at the unchanged selected atoms. -/
def originalMarkSelectedInfinitePhysicalCubePopulationCoupling
    (μ : Measure (DyadicUnitCube q)) (e : Z → Fin n ↪ ℕ)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (p : Z × (ℕ → DyadicUnitCube q)) :=
  originalIIDPhysicalCubePopulationCoupling μ z L (originalMarkSelectedInfinitePositions e p)

/-- The measurable actual plan is finite and has both exact physical marginals,
for every input, including empty selections and repeated physical locations. -/
theorem originalMarkSelectedInfinitePhysicalCubePopulationCoupling_spec
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (e : Z → Fin n ↪ ℕ) (he : ∀ j, Measurable (fun z ↦ e z j))
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Measurable (originalMarkSelectedInfinitePhysicalCubePopulationCoupling μ e z L) ∧
    ∀ p : Z × (ℕ → DyadicUnitCube q),
      let Γ := originalMarkSelectedInfinitePhysicalCubePopulationCoupling μ e z L p
      IsFiniteMeasure Γ ∧
        Γ.map Prod.fst = ∑ j, Measure.dirac (originalIIDCubePhysicalMap z L (p.2 (e p.1 j))) ∧
        Γ.map Prod.snd = (n : ℝ≥0∞) • μ.map (originalIIDCubePhysicalMap z L) :=
  ⟨(measurable_originalIIDPhysicalCubePopulationCoupling μ z L).comp
      (measurable_originalMarkSelectedInfinitePositions e he),
    fun p ↦ originalIIDPhysicalCubePopulationCoupling_marginals μ z L
      (originalMarkSelectedInfinitePositions e p)⟩

/-- The actual infinite iid reserve selection obeys the physical population
energy rate with exactly the finite auxiliary law's mass, without normalization. -/
theorem expected_originalMarkSelectedInfinitePhysicalCubePopulationCoupling_squareCost_rate
    (hq : 4 < q) (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (P : Measure Z) [IsFiniteMeasure P]
    (e : Z → Fin n ↪ ℕ) (he : ∀ j, Measurable (fun z ↦ e z j))
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) :
    Integrable (fun p : Z × (ℕ → DyadicUnitCube q) ↦
      ∫ v, ‖v.1 - v.2‖ ^ 2
        ∂originalMarkSelectedInfinitePhysicalCubePopulationCoupling μ e z L p)
      (P.prod (Measure.infinitePi (fun _ : ℕ ↦ μ))) ∧
    (∫ p, ∫ v, ‖v.1 - v.2‖ ^ 2
      ∂originalMarkSelectedInfinitePhysicalCubePopulationCoupling μ e z L p
      ∂P.prod (Measure.infinitePi (fun _ : ℕ ↦ μ))) ≤
        P.real Set.univ * (((q : ℝ) * L ^ 2) * dyadicMatchingConstant q *
          (n : ℝ) ^ (1 - 2 / (q : ℝ))) := by
  let f : (Fin n → DyadicUnitCube q) → ℝ := fun x ↦
    ∫ v, ‖v.1 - v.2‖ ^ 2 ∂originalIIDPhysicalCubePopulationCoupling μ z L x
  have hp := measurePreserving_originalMarkSelectedInfiniteJoint μ P e he
  have h := expected_originalIIDPhysicalCubePopulationCoupling_squareCost_rate (n := n) hq μ z L
  have hprod : Integrable (fun p : Z × (Fin n → DyadicUnitCube q) ↦ f p.2)
      (P.prod (Measure.pi (fun _ : Fin n ↦ μ))) := h.1.comp_snd P
  have hmapI := hprod.aestronglyMeasurable
  rw [← hp.map_eq] at hmapI
  have heq := integral_map hp.measurable.aemeasurable hmapI
  rw [hp.map_eq] at heq
  refine ⟨hp.integrable_comp_of_integrable hprod, ?_⟩
  calc
    _ = ∫ p : Z × (Fin n → DyadicUnitCube q), f p.2
        ∂P.prod (Measure.pi (fun _ : Fin n ↦ μ)) := heq.symm
    _ = P.real Set.univ * ∫ x, f x ∂Measure.pi (fun _ : Fin n ↦ μ) := by
      simpa only [smul_eq_mul] using integral_fun_snd (μ := P) f
    _ ≤ _ := mul_le_mul_of_nonneg_left h.2 (measureReal_nonneg : 0 ≤ P.real Set.univ)

end OTSelector.Reconstruction
