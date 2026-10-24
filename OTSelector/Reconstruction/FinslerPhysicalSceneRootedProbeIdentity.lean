import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClock

/-!
# Original finite clock probes under genuine Haar rooting

The original plan is unchanged. A source spatial cutoff and the two original
clocks are read from its actual rooted observation. Integrating over all Haar
roots cancels the original mass normalization exactly; cutting the root domain
can only decrease the same nonnegative readout.
-/
open Set Function MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A measurable spatial cutoff counts every original weighted edge with the
same Haar weight, without restricting its target. -/
theorem lintegral_haar_root_weighted_probe
    {V Z : Type*} [AddCommGroup V] [MeasurableSpace V]
    [MeasurableAdd₂ V] [MeasurableNeg V] [MeasurableSub₂ V] [MeasurableSpace Z]
    (β : Measure V) [SFinite β] [β.IsAddLeftInvariant] [β.IsNegInvariant]
    (π : Measure Z) [SFinite π] (loc : Z → V) (hloc : Measurable loc)
    (η : V → ℝ≥0∞) (hη : Measurable η) (g : Z → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, ∫⁻ p, η (loc p - z) * g p ∂π ∂β) =
      (∫⁻ z, η z ∂β) * ∫⁻ p, g p ∂π := by
  have hm : Measurable (fun v : V × Z ↦ η (loc v.2 - v.1) * g v.2) :=
    (hη.comp ((hloc.comp measurable_snd).sub measurable_fst)).mul (hg.comp measurable_snd)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hinner (p : Z) : (∫⁻ z, η (loc p - z) * g p ∂β) =
      (∫⁻ z, η z ∂β) * g p := by
    have htrans : Measurable (fun z : V ↦ η (loc p - z)) :=
      hη.comp (measurable_const.sub measurable_id)
    rw [lintegral_mul_const _ htrans,
      (β.measurePreserving_sub_left (loc p)).lintegral_comp hη]
  simp_rw [hinner]
  exact lintegral_const_mul _ hg

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)

/-- A nonnegative clock-pair probe with a genuine spatial source cutoff. -/
def physicalSceneRootedClockProbe (π : Measure Edge)
    (η : (ι → ℝ) → ℝ≥0∞) (g : ℝ × ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ e, η e.1.1 * g (e.1.2, e.2.2) ∂π

omit [Fintype ι] in
/-- The literal finite rooted observation keeps both original physical clocks
and the original plan weights. -/
theorem physicalSceneRootedClockProbe_eq
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (η : (ι → ℝ) → ℝ≥0∞) (hη : Measurable η)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    physicalSceneRootedClockProbe (physicalSceneRootedPlan Γ coord u N z) η g =
      ENNReal.ofReal N * ∫⁻ p, η (coord p.1 - z) * g (u p.1, u p.2) ∂Γ := by
  let f : Edge → ℝ≥0∞ := fun e ↦ η e.1.1 * g (e.1.2, e.2.2)
  have hf : Measurable f := (hη.comp measurable_fst.fst).mul
    (hg.comp (measurable_fst.snd.prodMk measurable_snd.snd))
  change (∫⁻ e, f e ∂(ENNReal.ofReal N • Γ.map
    (physicalSceneRootedObservation coord u z))) = _
  rw [lintegral_smul_measure, lintegral_map hf
    (measurable_physicalSceneRootedObservation coord hcoord u hu z)]
  rfl

/-- Full Haar rooting exactly recovers the original clock-probe integral with
only the cutoff's Haar integral as factor. The actual scale cancels internally. -/
theorem lintegral_physicalSceneRootedClockProbe_eq
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (η : (ι → ℝ) → ℝ≥0∞) (hη : Measurable η)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, physicalSceneRootedClockProbe (physicalSceneRootedPlan Γ coord u N z) η g
      ∂cavityRootMeasure volume univ N) =
      (∫⁻ z, η z ∂volume) * ∫⁻ p, g (u p.1, u p.2) ∂Γ := by
  simp_rw [physicalSceneRootedClockProbe_eq Γ coord hcoord u hu N _ η hη g hg]
  rw [cavityRootMeasure, Measure.restrict_univ, lintegral_smul_measure,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hN))
      ENNReal.ofReal_ne_top, one_mul]
  exact lintegral_haar_root_weighted_probe volume Γ (fun p ↦ coord p.1)
    (hcoord.comp measurable_fst) η hη (fun p ↦ g (u p.1, u p.2))
    (hg.comp ((hu.comp measurable_fst).prodMk (hu.comp measurable_snd)))

/-- Restricting the actual Haar root domain only lowers the same original
probe integral. No target cutoff or replacement cloud enters the bound. -/
theorem lintegral_physicalSceneRootedClockProbe_le
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ))
    (η : (ι → ℝ) → ℝ≥0∞) (hη : Measurable η)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, physicalSceneRootedClockProbe (physicalSceneRootedPlan Γ coord u N z) η g
      ∂cavityRootMeasure volume D N) ≤
      (∫⁻ z, η z ∂volume) * ∫⁻ p, g (u p.1, u p.2) ∂Γ := by
  have hmeasure : cavityRootMeasure volume D N ≤ cavityRootMeasure volume univ N := by
    simp only [cavityRootMeasure, Measure.restrict_univ]
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.restrict_le_self A) _
  exact (lintegral_mono' hmeasure le_rfl).trans_eq
    (lintegral_physicalSceneRootedClockProbe_eq Γ coord hcoord u hu N hN η hη g hg)

/-- A countable measurable partition of the original root space recovers the
same full Haar readout by summing its original normalized local root laws. -/
theorem tsum_lintegral_physicalSceneRootedClockProbe_eq
    {J : Type*} [Countable J]
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D : J → Set (ι → ℝ)) (hD : ∀ k, MeasurableSet (D k))
    (hdisjoint : Pairwise (Disjoint on D)) (hcover : ⋃ k, D k = univ)
    (η : (ι → ℝ) → ℝ≥0∞) (hη : Measurable η)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∑' k, ∫⁻ z, physicalSceneRootedClockProbe (physicalSceneRootedPlan Γ coord u N z) η g
      ∂cavityRootMeasure volume (D k) N) =
      (∫⁻ z, η z ∂volume) * ∫⁻ p, g (u p.1, u p.2) ∂Γ := by
  rw [← lintegral_physicalSceneRootedClockProbe_eq Γ coord hcoord u hu N hN η hη g hg]
  simp only [cavityRootMeasure, lintegral_smul_measure, smul_eq_mul]
  rw [ENNReal.tsum_mul_left, ← lintegral_iUnion hD hdisjoint, hcover]

/-- Bounded original clock probes pay discarded finite plan mass only,
with the exact same normalized root law and source cutoff Haar mass. -/
theorem lintegral_physicalSceneRootedClockProbe_le_mass
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ))
    (η : (ι → ℝ) → ℝ≥0∞) (hη : Measurable η)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g)
    (G : ℝ≥0∞) (hG : ∀ s t, g (s, t) ≤ G) :
    (∫⁻ z, physicalSceneRootedClockProbe (physicalSceneRootedPlan Γ coord u N z) η g
      ∂cavityRootMeasure volume D N) ≤
      (∫⁻ z, η z ∂volume) * (G * Γ univ) := by
  refine (lintegral_physicalSceneRootedClockProbe_le Γ coord hcoord u hu N hN D η hη g hg).trans ?_
  apply mul_le_mul_right
  simpa only [lintegral_const] using lintegral_mono (fun p : M × M ↦ hG (u p.1) (u p.2))

end OTSelector.Reconstruction
