import OTSelector.Finite.MaxCardValueStability
import OTSelector.Probability.MarkedCloudCoupling
import OTSelector.Finite.MatchingTranspose

/-!
# Continuity of the marked Poissonized pressure in the intensity

The marked pressure of two independent Poissonized marked cube clouds is
continuous in the common intensity `r` on `[1, ∞)`.  The proof uses the
prefix coupling of `MarkedCloudCoupling`: a `Poisson rho` cloud and a
`Poisson (rho + delta)` cloud share one iid marked sequence, with the smaller
count a prefix of the larger one.

Comparing the two optimal maximum-cardinality values along the coupling splits
into two estimates:

* changing the intensity from `rho` to `rho + delta` at fixed counts changes
  every edge by at most `C q |(rho+delta)^{2/q} - rho^{2/q}|`, hence the value
  by `min N M` times this quantity;
* adding the `K` and `L` extra source and target points changes the value by at
  most twice the uniform edge bound per point.

Integrating against the coupling, the expected added counts are both `delta`
and the expected minimum count is at most `rho`, which gives the first-order
bound `markedPressure_diff_le`.  Continuity of `r ↦ markedPressure r / r` on
`[1, ∞)` follows.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

noncomputable section

namespace OTSelector.Probability

noncomputable section

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The pre-coupling

The count coupling `countCouple rho delta` is the image of the product of two
Poisson measures under `(n, k) ↦ (n, n + k)`.  Pulling the whole two-cloud
coupling back along this map makes the extra counts explicit independent
Poisson variables, so that all count expectations are direct. -/

/-- The pre-coupling space: independent base and extra Poisson counts together
with iid marked sequences for both clouds. -/
abbrev MarkedPreCoupleSpace (q : ℕ) (A B : Type*) :=
  ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
    ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B))

/-- One pre-coupled marked cloud: a base Poisson count, an independent extra
Poisson count and an iid marked sequence. -/
noncomputable def preCloudCouple (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (ρ δ : ℝ≥0) :
    Measure ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) :=
  ((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) A α)

instance isProbabilityMeasure_preCloudCouple (q : ℕ) (A : Type*) [MeasurableSpace A]
    (α : Measure A) [IsProbabilityMeasure α] (ρ δ : ℝ≥0) :
    IsProbabilityMeasure (preCloudCouple (q := q) A α ρ δ) := by
  unfold preCloudCouple
  infer_instance

/-- The pre-coupling of the two marked clouds. -/
noncomputable def markedPreCouple (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    Measure (MarkedPreCoupleSpace q A B) :=
  (preCloudCouple (q := q) A α ρ δ).prod (preCloudCouple (q := q) B β ρ δ)

instance isProbabilityMeasure_markedPreCouple (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    IsProbabilityMeasure (markedPreCouple (q := q) A B α β ρ δ) := by
  unfold markedPreCouple
  infer_instance

/-- The map from the pre-coupling to the usual two-cloud coupling. -/
def preCoupleMap (z : MarkedPreCoupleSpace q A B) :
    ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) :=
  (((z.1.1.1, z.1.1.1 + z.1.1.2), z.1.2),
   ((z.2.1.1, z.2.1.1 + z.2.1.2), z.2.2))

/-- The small marked cloud read off the pre-coupling. -/
def preSmallCloud (z : MarkedPreCoupleSpace q A B) : TwoMarkedCloudSpace q A B :=
  ((z.1.1.1, z.1.2), (z.2.1.1, z.2.2))

/-- The large marked cloud read off the pre-coupling. -/
def preLargeCloud (z : MarkedPreCoupleSpace q A B) : TwoMarkedCloudSpace q A B :=
  ((z.1.1.1 + z.1.1.2, z.1.2), (z.2.1.1 + z.2.1.2, z.2.2))

/-- Measurability of the pre-coupling map. -/
theorem measurable_preCoupleMap (q : ℕ) :
    Measurable (preCoupleMap (q := q) (A := A) (B := B)) := by
  unfold preCoupleMap
  fun_prop

/-- The small cloud extracted from the image of the pre-coupling is the small
pre-coupled cloud. -/
theorem smallPair_preCoupleMap (z : MarkedPreCoupleSpace q A B) :
    (coupledSmall (q := q) (preCoupleMap (q := q) z).1,
      coupledSmall (q := q) (preCoupleMap (q := q) z).2) = preSmallCloud z := rfl

/-- The large cloud extracted from the image of the pre-coupling is the large
pre-coupled cloud. -/
theorem largePair_preCoupleMap (z : MarkedPreCoupleSpace q A B) :
    (coupledLarge (q := q) (preCoupleMap (q := q) z).1,
      coupledLarge (q := q) (preCoupleMap (q := q) z).2) = preLargeCloud z := rfl

/-- The two-cloud coupling is the image of the pre-coupling under
`preCoupleMap`. -/
theorem twoCloudCouple_eq_map_markedPreCouple (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    twoCloudCouple (q := q) A B α β ρ δ =
      (markedPreCouple (q := q) A B α β ρ δ).map
        (preCoupleMap (q := q) (A := A) (B := B)) := by
  have hmap : (preCoupleMap (q := q) (A := A) (B := B)) =
      Prod.map
        (Prod.map (fun p : ℕ × ℕ => (p.1, p.1 + p.2)) id)
        (Prod.map (fun p : ℕ × ℕ => (p.1, p.1 + p.2)) id) := rfl
  rw [hmap]
  unfold markedPreCouple twoCloudCouple preCloudCouple cloudCouple countCouple
  rw [← Measure.map_prod_map
    (((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) A α))
    (((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) B β))
    (by fun_prop) (by fun_prop)]
  rw [← Measure.map_prod_map ((poissonMeasure ρ).prod (poissonMeasure δ))
      (markedSeqLaw (q := q) A α) (by fun_prop) measurable_id,
    ← Measure.map_prod_map ((poissonMeasure ρ).prod (poissonMeasure δ))
      (markedSeqLaw (q := q) B β) (by fun_prop) measurable_id]
  rw [Measure.map_id, Measure.map_id]

/-! ## Accessors on the pre-coupling -/

/-- The base source count. -/
def pcSourceCount (z : MarkedPreCoupleSpace q A B) : ℕ := z.1.1.1

/-- The extra source count. -/
def pcExtraSource (z : MarkedPreCoupleSpace q A B) : ℕ := z.1.1.2

/-- The base target count. -/
def pcTargetCount (z : MarkedPreCoupleSpace q A B) : ℕ := z.2.1.1

/-- The extra target count. -/
def pcExtraTarget (z : MarkedPreCoupleSpace q A B) : ℕ := z.2.1.2

/-- The source position. -/
def pcSourcePoint (z : MarkedPreCoupleSpace q A B) (i : ℕ) : Fin q → ℝ :=
  (z.1.2 i).1

/-- The source mark. -/
def pcSourceMark (z : MarkedPreCoupleSpace q A B) (i : ℕ) : A :=
  (z.1.2 i).2

/-- The target position. -/
def pcTargetPoint (z : MarkedPreCoupleSpace q A B) (j : ℕ) : Fin q → ℝ :=
  (z.2.2 j).1

/-- The target mark. -/
def pcTargetMark (z : MarkedPreCoupleSpace q A B) (j : ℕ) : B :=
  (z.2.2 j).2

theorem measurable_pcSourceCount (q : ℕ) :
    Measurable (pcSourceCount (q := q) (A := A) (B := B)) := by
  unfold pcSourceCount
  fun_prop

theorem measurable_pcExtraSource (q : ℕ) :
    Measurable (pcExtraSource (q := q) (A := A) (B := B)) := by
  unfold pcExtraSource
  fun_prop

theorem measurable_pcTargetCount (q : ℕ) :
    Measurable (pcTargetCount (q := q) (A := A) (B := B)) := by
  unfold pcTargetCount
  fun_prop

theorem measurable_pcExtraTarget (q : ℕ) :
    Measurable (pcExtraTarget (q := q) (A := A) (B := B)) := by
  unfold pcExtraTarget
  fun_prop

theorem measurable_preSmallCloud (q : ℕ) :
    Measurable (preSmallCloud (q := q) (A := A) (B := B)) := by
  unfold preSmallCloud
  fun_prop

theorem measurable_preLargeCloud (q : ℕ) :
    Measurable (preLargeCloud (q := q) (A := A) (B := B)) := by
  unfold preLargeCloud
  fun_prop

/-- Measurability of the map extracting the two small clouds from the coupling. -/
theorem measurable_smallPair (q : ℕ) :
    Measurable fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
        ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2) :=
  ((measurable_coupledSmall q).comp measurable_fst).prodMk
    ((measurable_coupledSmall q).comp measurable_snd)

/-- Measurability of the map extracting the two large clouds from the coupling. -/
theorem measurable_largePair (q : ℕ) :
    Measurable fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
        ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2) :=
  ((measurable_coupledLarge q).comp measurable_fst).prodMk
    ((measurable_coupledLarge q).comp measurable_snd)

/-! ## Transfer of the pressure integrals to the pre-coupling -/

/-- The pressure at intensity `rho` is the integral of the small pre-coupled
cloud value. -/
theorem integral_markedTilted_preSmall (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) {C G : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    markedPressure q A B α β ρ kin g t =
      ∫ z, markedTilted (q := q) (r := (ρ : ℝ)) kin g t
        (preSmallCloud (q := q) z)
        ∂(markedPreCouple (q := q) A B α β ρ δ) := by
  unfold markedPressure
  have hpair := measurable_smallPair (q := q) (A := A) (B := B)
  have hT : Measurable (markedTilted (q := q) (r := (ρ : ℝ)) kin g t) :=
    measurable_markedTilted q (ρ : ℝ) ρ.coe_nonneg hC0 hG0 hkin hkin_bound hg hgb t
  have hcomp : Measurable fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      markedTilted (q := q) (r := (ρ : ℝ)) kin g t
        (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2) :=
    hT.comp hpair
  calc ∫ ω, markedTilted (q := q) (r := (ρ : ℝ)) kin g t ω
        ∂(twoMarkedCloudLaw (q := q) A B α β ρ)
      = ∫ Z, markedTilted (q := q) (r := (ρ : ℝ)) kin g t
          (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2)
          ∂(twoCloudCouple (q := q) A B α β ρ δ) := by
        rw [← twoCloudCouple_map_small (q := q) A B α β ρ δ]
        have hfm : AEStronglyMeasurable (markedTilted (q := q) (r := (ρ : ℝ)) kin g t)
            (Measure.map (fun Z =>
              (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2))
              (twoCloudCouple (q := q) A B α β ρ δ)) := by
          rw [twoCloudCouple_map_small (q := q) A B α β ρ δ]
          exact hT.aestronglyMeasurable
        exact integral_map (μ := twoCloudCouple (q := q) A B α β ρ δ)
          (φ := fun Z => (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2))
          hpair.aemeasurable hfm
    _ = ∫ z, markedTilted (q := q) (r := (ρ : ℝ)) kin g t
          (preSmallCloud (q := q) z)
          ∂(markedPreCouple (q := q) A B α β ρ δ) := by
        rw [twoCloudCouple_eq_map_markedPreCouple]
        refine integral_map (μ := markedPreCouple (q := q) A B α β ρ δ)
          (φ := preCoupleMap (q := q) (A := A) (B := B))
          (measurable_preCoupleMap q).aemeasurable ?_
        rw [← twoCloudCouple_eq_map_markedPreCouple]
        exact hcomp.aestronglyMeasurable

/-- The pressure at intensity `rho + delta` is the integral of the large
pre-coupled cloud value. -/
theorem integral_markedTilted_preLarge (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) {C G : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    markedPressure q A B α β (ρ + δ) kin g t =
      ∫ z, markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t
        (preLargeCloud (q := q) z)
        ∂(markedPreCouple (q := q) A B α β ρ δ) := by
  unfold markedPressure
  have hpair := measurable_largePair (q := q) (A := A) (B := B)
  have hT : Measurable (markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t) :=
    measurable_markedTilted q ((ρ + δ : ℝ≥0) : ℝ) (by positivity) hC0 hG0
      hkin hkin_bound hg hgb t
  have hcomp : Measurable fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t
        (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2) :=
    hT.comp hpair
  calc ∫ ω, markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t ω
        ∂(twoMarkedCloudLaw (q := q) A B α β (ρ + δ))
      = ∫ Z, markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t
          (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2)
          ∂(twoCloudCouple (q := q) A B α β ρ δ) := by
        rw [← twoCloudCouple_map_large (q := q) A B α β ρ δ]
        have hfm : AEStronglyMeasurable
            (markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t)
            (Measure.map (fun Z =>
              (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2))
              (twoCloudCouple (q := q) A B α β ρ δ)) := by
          rw [twoCloudCouple_map_large (q := q) A B α β ρ δ]
          exact hT.aestronglyMeasurable
        exact integral_map (μ := twoCloudCouple (q := q) A B α β ρ δ)
          (φ := fun Z => (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2))
          hpair.aemeasurable hfm
    _ = ∫ z, markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t
          (preLargeCloud (q := q) z)
          ∂(markedPreCouple (q := q) A B α β ρ δ) := by
        rw [twoCloudCouple_eq_map_markedPreCouple]
        refine integral_map (μ := markedPreCouple (q := q) A B α β ρ δ)
          (φ := preCoupleMap (q := q) (A := A) (B := B))
          (measurable_preCoupleMap q).aemeasurable ?_
        rw [← twoCloudCouple_eq_map_markedPreCouple]
        exact hcomp.aestronglyMeasurable

/-- Integrability of the small pre-coupled cloud value. -/
theorem integrable_markedTilted_preSmall (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) {C G : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (fun z => markedTilted (q := q) (r := (ρ : ℝ)) kin g t
      (preSmallCloud (q := q) z))
      (markedPreCouple (q := q) A B α β ρ δ) := by
  have hbase := integrable_markedTilted (q := q) α β ρ (C := C) (G := G)
    ρ.coe_nonneg hC0 hG0 hkin hkin_bound hg hgb t
  have hpair := measurable_smallPair (q := q) (A := A) (B := B)
  have h1 : Integrable (fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      markedTilted (q := q) (r := (ρ : ℝ)) kin g t
        (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2))
      (twoCloudCouple (q := q) A B α β ρ δ) := by
    have hbase' : Integrable (markedTilted (q := q) (r := (ρ : ℝ)) kin g t)
        ((twoCloudCouple (q := q) A B α β ρ δ).map
          (fun Z => (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2))) := by
      rw [twoCloudCouple_map_small (q := q) A B α β ρ δ]
      exact hbase
    simpa only [Function.comp_def] using hbase'.comp_measurable hpair
  have h2 : Integrable (fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      markedTilted (q := q) (r := (ρ : ℝ)) kin g t
        (coupledSmall (q := q) Z.1, coupledSmall (q := q) Z.2))
      ((markedPreCouple (q := q) A B α β ρ δ).map
        (preCoupleMap (q := q) (A := A) (B := B))) := by
    rw [← twoCloudCouple_eq_map_markedPreCouple]
    exact h1
  have h3 := h2.comp_measurable (measurable_preCoupleMap (q := q) (A := A) (B := B))
  simpa only [Function.comp_def, smallPair_preCoupleMap] using h3

/-- Integrability of the large pre-coupled cloud value. -/
theorem integrable_markedTilted_preLarge (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) {C G : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (fun z => markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t
      (preLargeCloud (q := q) z))
      (markedPreCouple (q := q) A B α β ρ δ) := by
  have hbase := integrable_markedTilted (q := q) α β (ρ + δ) (C := C) (G := G)
    (by positivity) hC0 hG0 hkin hkin_bound hg hgb t
  have hpair := measurable_largePair (q := q) (A := A) (B := B)
  have h1 : Integrable (fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t
        (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2))
      (twoCloudCouple (q := q) A B α β ρ δ) := by
    have hbase' : Integrable (markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t)
        ((twoCloudCouple (q := q) A B α β ρ δ).map
          (fun Z => (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2))) := by
      rw [twoCloudCouple_map_large (q := q) A B α β ρ δ]
      exact hbase
    simpa only [Function.comp_def] using hbase'.comp_measurable hpair
  have h2 : Integrable (fun Z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) ×
      ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)) =>
      markedTilted (q := q) (r := ((ρ + δ : ℝ≥0) : ℝ)) kin g t
        (coupledLarge (q := q) Z.1, coupledLarge (q := q) Z.2))
      ((markedPreCouple (q := q) A B α β ρ δ).map
        (preCoupleMap (q := q) (A := A) (B := B))) := by
    rw [← twoCloudCouple_eq_map_markedPreCouple]
    exact h1
  have h3 := h2.comp_measurable (measurable_preCoupleMap (q := q) (A := A) (B := B))
  simpa only [Function.comp_def, largePair_preCoupleMap] using h3

/-! ## Count expectations on the pre-coupling -/

/-- For a probability measure, the real total mass is one. -/
private theorem real_univ_eq_one {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [IsProbabilityMeasure ν] : ν.real univ = 1 := by
  simp [Measure.real]

/-- Integration over the first coordinate of a product with a probability measure. -/
private theorem integral_fun_fst_prob {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [SFinite μ] {ν : Measure β} [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : α → E) :
    ∫ z : α × β, f z.1 ∂(μ.prod ν) = ∫ x, f x ∂μ := by
  rw [integral_fun_fst, real_univ_eq_one ν, one_smul]

/-- Integration over the second coordinate of a product with a probability measure. -/
private theorem integral_fun_snd_prob {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {ν : Measure β} [SFinite ν]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : β → E) :
    ∫ z : α × β, f z.2 ∂(μ.prod ν) = ∫ y, f y ∂ν := by
  rw [integral_fun_snd, real_univ_eq_one μ, one_smul]

theorem integrable_pcSourceCount (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    Integrable (fun z : MarkedPreCoupleSpace q A B => ((pcSourceCount z : ℕ) : ℝ))
      (markedPreCouple (q := q) A B α β ρ δ) := by
  have hp : Integrable (fun p : ℕ × ℕ => ((p.1 : ℕ) : ℝ))
      ((poissonMeasure ρ).prod (poissonMeasure δ)) :=
    (integrable_id_poissonMeasure ρ).comp_fst _
  have h1 : Integrable (fun x : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) =>
      ((x.1.1 : ℕ) : ℝ)) (preCloudCouple (q := q) A α ρ δ) := by
    unfold preCloudCouple
    exact hp.comp_fst _
  unfold markedPreCouple
  simpa only [pcSourceCount] using h1.comp_fst (preCloudCouple (q := q) B β ρ δ)

theorem integrable_pcExtraSource (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    Integrable (fun z : MarkedPreCoupleSpace q A B => ((pcExtraSource z : ℕ) : ℝ))
      (markedPreCouple (q := q) A B α β ρ δ) := by
  have hp : Integrable (fun p : ℕ × ℕ => ((p.2 : ℕ) : ℝ))
      ((poissonMeasure ρ).prod (poissonMeasure δ)) :=
    (integrable_id_poissonMeasure δ).comp_snd _
  have h1 : Integrable (fun x : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) =>
      ((x.1.2 : ℕ) : ℝ)) (preCloudCouple (q := q) A α ρ δ) := by
    unfold preCloudCouple
    exact hp.comp_fst _
  unfold markedPreCouple
  simpa only [pcExtraSource] using h1.comp_fst (preCloudCouple (q := q) B β ρ δ)

theorem integrable_pcTargetCount (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    Integrable (fun z : MarkedPreCoupleSpace q A B => ((pcTargetCount z : ℕ) : ℝ))
      (markedPreCouple (q := q) A B α β ρ δ) := by
  have hp : Integrable (fun p : ℕ × ℕ => ((p.1 : ℕ) : ℝ))
      ((poissonMeasure ρ).prod (poissonMeasure δ)) :=
    (integrable_id_poissonMeasure ρ).comp_fst _
  have h1 : Integrable (fun y : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B) =>
      ((y.1.1 : ℕ) : ℝ)) (preCloudCouple (q := q) B β ρ δ) := by
    unfold preCloudCouple
    exact hp.comp_fst _
  unfold markedPreCouple
  simpa only [pcTargetCount] using h1.comp_snd (preCloudCouple (q := q) A α ρ δ)

theorem integrable_pcExtraTarget (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    Integrable (fun z : MarkedPreCoupleSpace q A B => ((pcExtraTarget z : ℕ) : ℝ))
      (markedPreCouple (q := q) A B α β ρ δ) := by
  have hp : Integrable (fun p : ℕ × ℕ => ((p.2 : ℕ) : ℝ))
      ((poissonMeasure ρ).prod (poissonMeasure δ)) :=
    (integrable_id_poissonMeasure δ).comp_snd _
  have h1 : Integrable (fun y : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B) =>
      ((y.1.2 : ℕ) : ℝ)) (preCloudCouple (q := q) B β ρ δ) := by
    unfold preCloudCouple
    exact hp.comp_fst _
  unfold markedPreCouple
  simpa only [pcExtraTarget] using h1.comp_snd (preCloudCouple (q := q) A α ρ δ)

/-- The minimum count is integrable. -/
theorem integrable_pcMinCount (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    Integrable (fun z : MarkedPreCoupleSpace q A B =>
      ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ))
      (markedPreCouple (q := q) A B α β ρ δ) := by
  have hsrc := integrable_pcSourceCount (q := q) A B α β ρ δ
  refine hsrc.mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable (Measurable.comp measurable_from_nat
      ((measurable_pcSourceCount q).min (measurable_pcTargetCount q)))
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Nat.cast_le.mpr (min_le_left (pcSourceCount z) (pcTargetCount z))

/-- The base source count has expectation `rho`. -/
theorem integral_pcSourceCount (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    ∫ z, ((pcSourceCount z : ℕ) : ℝ) ∂(markedPreCouple (q := q) A B α β ρ δ) =
      (ρ : ℝ) := by
  unfold markedPreCouple preCloudCouple pcSourceCount
  change ∫ z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) × ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)),
      (fun x : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) => ((x.1.1 : ℕ) : ℝ)) z.1
      ∂((((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) A α)).prod
        (((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) B β)))
      = (ρ : ℝ)
  rw [integral_fun_fst_prob (f := fun x : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) =>
    ((x.1.1 : ℕ) : ℝ))]
  rw [integral_fun_fst_prob (f := fun p : ℕ × ℕ => ((p.1 : ℕ) : ℝ))]
  change ∫ p : ℕ × ℕ, ((p.1 : ℕ) : ℝ)
      ∂((poissonMeasure ρ).prod (poissonMeasure δ)) = (ρ : ℝ)
  rw [integral_fun_fst_prob (f := fun n : ℕ => (n : ℝ))]
  exact integral_id_poissonMeasure ρ

/-- The extra source count has expectation `delta`. -/
theorem integral_pcExtraSource (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    ∫ z, ((pcExtraSource z : ℕ) : ℝ) ∂(markedPreCouple (q := q) A B α β ρ δ) =
      (δ : ℝ) := by
  unfold markedPreCouple preCloudCouple pcExtraSource
  change ∫ z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) × ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)),
      (fun x : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) => ((x.1.2 : ℕ) : ℝ)) z.1
      ∂((((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) A α)).prod
        (((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) B β)))
      = (δ : ℝ)
  rw [integral_fun_fst_prob (f := fun x : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A) =>
    ((x.1.2 : ℕ) : ℝ))]
  rw [integral_fun_fst_prob (f := fun p : ℕ × ℕ => ((p.2 : ℕ) : ℝ))]
  change ∫ p : ℕ × ℕ, ((p.2 : ℕ) : ℝ)
      ∂((poissonMeasure ρ).prod (poissonMeasure δ)) = (δ : ℝ)
  rw [integral_fun_snd_prob (f := fun k : ℕ => (k : ℝ))]
  exact integral_id_poissonMeasure δ

/-- The extra target count has expectation `delta`. -/
theorem integral_pcExtraTarget (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    ∫ z, ((pcExtraTarget z : ℕ) : ℝ) ∂(markedPreCouple (q := q) A B α β ρ δ) =
      (δ : ℝ) := by
  unfold markedPreCouple preCloudCouple pcExtraTarget
  change ∫ z : ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × A)) × ((ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B)),
      (fun y : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B) => ((y.1.2 : ℕ) : ℝ)) z.2
      ∂((((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) A α)).prod
        (((poissonMeasure ρ).prod (poissonMeasure δ)).prod (markedSeqLaw (q := q) B β)))
      = (δ : ℝ)
  rw [integral_fun_snd_prob (f := fun y : (ℕ × ℕ) × (ℕ → (Fin q → ℝ) × B) =>
    ((y.1.2 : ℕ) : ℝ))]
  rw [integral_fun_fst_prob (f := fun p : ℕ × ℕ => ((p.2 : ℕ) : ℝ))]
  change ∫ p : ℕ × ℕ, ((p.2 : ℕ) : ℝ)
      ∂((poissonMeasure ρ).prod (poissonMeasure δ)) = (δ : ℝ)
  rw [integral_fun_snd_prob (f := fun k : ℕ => (k : ℝ))]
  exact integral_id_poissonMeasure δ

/-- The expected minimum count is at most `rho`. -/
theorem integral_pcMinCount_le (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (ρ δ : ℝ≥0) :
    ∫ z, ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ)
        ∂(markedPreCouple (q := q) A B α β ρ δ) ≤ (ρ : ℝ) := by
  have hmin := integrable_pcMinCount (q := q) A B α β ρ δ
  have hsrc := integrable_pcSourceCount (q := q) A B α β ρ δ
  calc ∫ z, ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ)
        ∂(markedPreCouple (q := q) A B α β ρ δ)
      ≤ ∫ z, ((pcSourceCount z : ℕ) : ℝ)
          ∂(markedPreCouple (q := q) A B α β ρ δ) :=
        integral_mono hmin hsrc (fun z =>
          Nat.cast_le.mpr (min_le_left (pcSourceCount z) (pcTargetCount z)))
    _ = (ρ : ℝ) := integral_pcSourceCount (q := q) A B α β ρ δ

/-! ## The pointwise comparison on the pre-coupling -/

/-- The marked edge evaluated on the pre-coupling. -/
noncomputable def pcEntry (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (z : MarkedPreCoupleSpace q A B) (i j : ℕ) : ℝ :=
  r ^ (2 / (q : ℝ)) * kin (pcSourceMark z i) (pcTargetMark z j)
      (mDisplacement (pcSourcePoint z i) (pcTargetPoint z j)) +
    t * g (pcSourceMark z i) (pcTargetMark z j)

/-- The small cloud value at intensity `r`. -/
noncomputable def pcSmallValue (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (z : MarkedPreCoupleSpace q A B) : ℝ :=
  PartialMatching.maxCardValue (fun i : Fin (pcSourceCount z) =>
    fun j : Fin (pcTargetCount z) => pcEntry q r kin g t z (i : ℕ) (j : ℕ))

/-- The large cloud value at intensity `r`. -/
noncomputable def pcLargeValue (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (z : MarkedPreCoupleSpace q A B) : ℝ :=
  PartialMatching.maxCardValue (fun i : Fin (pcSourceCount z + pcExtraSource z) =>
    fun j : Fin (pcTargetCount z + pcExtraTarget z) =>
      pcEntry q r kin g t z (i : ℕ) (j : ℕ))

/-- The small pre-coupled value is the marked tilted value of the small cloud. -/
theorem pcSmallValue_eq_markedTilted (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (z : MarkedPreCoupleSpace q A B) :
    pcSmallValue q r kin g t z = markedTilted q r kin g t (preSmallCloud z) := rfl

/-- The large pre-coupled value is the marked tilted value of the large cloud. -/
theorem pcLargeValue_eq_markedTilted (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ)
    (z : MarkedPreCoupleSpace q A B) :
    pcLargeValue q r kin g t z = markedTilted q r kin g t (preLargeCloud z) := rfl

/-- Uniform bound on one pre-coupled marked edge. -/
theorem abs_pcEntry_le (q : ℕ) {r C G t : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hgb : ∀ a b, |g a b| ≤ G)
    (z : MarkedPreCoupleSpace q A B) (i j : ℕ) :
    |pcEntry q r kin g t z i j| ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G := by
  unfold pcEntry
  have hkin : |kin (pcSourceMark z i) (pcTargetMark z j)
      (mDisplacement (pcSourcePoint z i) (pcTargetPoint z j))| ≤ C * (q : ℝ) :=
    (hkin_bound _ _ _).trans
      (mul_le_mul_of_nonneg_left (mDisplacement_sq_sum_le q _ _) hC0)
  calc |r ^ (2 / (q : ℝ)) * kin (pcSourceMark z i) (pcTargetMark z j)
        (mDisplacement (pcSourcePoint z i) (pcTargetPoint z j)) +
        t * g (pcSourceMark z i) (pcTargetMark z j)|
      ≤ |r ^ (2 / (q : ℝ)) * kin (pcSourceMark z i) (pcTargetMark z j)
            (mDisplacement (pcSourcePoint z i) (pcTargetPoint z j))| +
          |t * g (pcSourceMark z i) (pcTargetMark z j)| := abs_add_le _ _
    _ = r ^ (2 / (q : ℝ)) *
          |kin (pcSourceMark z i) (pcTargetMark z j)
            (mDisplacement (pcSourcePoint z i) (pcTargetPoint z j))| +
          |t| * |g (pcSourceMark z i) (pcTargetMark z j)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr _)]
    _ ≤ r ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G :=
        add_le_add
          (mul_le_mul_of_nonneg_left hkin (Real.rpow_nonneg hr _))
          (mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg t))

/-- Pointwise comparison of the large and small pre-coupled cloud values. -/
theorem abs_pcLargeValue_sub_pcSmallValue_le
    (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (ρ δ : ℝ≥0) {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hgb : ∀ a b, |g a b| ≤ G)
    (z : MarkedPreCoupleSpace q A B) :
    |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
      pcSmallValue q (ρ : ℝ) kin g t z| ≤
      2 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (pcExtraSource z : ℝ) +
        2 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (pcExtraTarget z : ℝ) +
        (C * (q : ℝ)) *
          |Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow (ρ : ℝ) (2 / (q : ℝ))| *
            ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) := by
  let Bσ : ℝ := Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G
  let aσ : ℝ := Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ))
  let aρ : ℝ := Real.rpow (ρ : ℝ) (2 / (q : ℝ))
  have hσ0 : 0 ≤ ((ρ + δ : ℝ≥0) : ℝ) := by positivity
  have hBσ0 : 0 ≤ Bσ := by
    dsimp only [Bσ]
    exact add_nonneg
      (mul_nonneg (Real.rpow_nonneg hσ0 _) (mul_nonneg hC0 (Nat.cast_nonneg q)))
      (mul_nonneg (abs_nonneg t) hG0)
  have hedge : ∀ i j : ℕ, |pcEntry q ((ρ + δ : ℝ≥0) : ℝ) kin g t z i j| ≤ Bσ :=
    fun i j => abs_pcEntry_le (q := q) hσ0 hC0 hkin_bound hgb z i j
  let rowRestr : Fin (pcSourceCount z) → Fin (pcTargetCount z + pcExtraTarget z) → ℝ :=
    fun i j => pcEntry q ((ρ + δ : ℝ≥0) : ℝ) kin g t z (i : ℕ) (j : ℕ)
  let midMat : Fin (pcSourceCount z) → Fin (pcTargetCount z) → ℝ :=
    fun i j => pcEntry q ((ρ + δ : ℝ≥0) : ℝ) kin g t z (i : ℕ) (j : ℕ)
  have hrow : |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
      PartialMatching.maxCardValue rowRestr| ≤ 2 * Bσ * (pcExtraSource z : ℝ) := by
    have h := PartialMatching.abs_maxCardValue_sub_le_add_rows
      (a := pcSourceCount z) (δ := pcExtraSource z)
      (b := pcTargetCount z + pcExtraTarget z)
      (c := fun i : Fin (pcSourceCount z + pcExtraSource z) =>
        fun j : Fin (pcTargetCount z + pcExtraTarget z) =>
          pcEntry q ((ρ + δ : ℝ≥0) : ℝ) kin g t z (i : ℕ) (j : ℕ))
      hBσ0 (fun i j => hedge (i : ℕ) (j : ℕ))
    simpa only [pcLargeValue, rowRestr, Fin.val_castLE] using h
  have hcol : |PartialMatching.maxCardValue rowRestr -
      PartialMatching.maxCardValue midMat| ≤ 2 * Bσ * (pcExtraTarget z : ℝ) := by
    have h := PartialMatching.abs_maxCardValue_sub_le_add_cols
      (a := pcSourceCount z) (b := pcTargetCount z) (δ := pcExtraTarget z)
      (c := rowRestr) hBσ0 (fun i j => hedge (i : ℕ) (j : ℕ))
    simpa only [midMat, rowRestr, Fin.val_castLE] using h
  have hmid : |PartialMatching.maxCardValue midMat -
      pcSmallValue q (ρ : ℝ) kin g t z| ≤
      ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) *
        ((C * (q : ℝ)) * |aσ - aρ|) := by
    have h := PartialMatching.abs_maxCardValue_sub_le_of_entrywise midMat
      (fun i : Fin (pcSourceCount z) => fun j : Fin (pcTargetCount z) =>
        pcEntry q (ρ : ℝ) kin g t z (i : ℕ) (j : ℕ))
      (B := (C * (q : ℝ)) * |aσ - aρ|)
      (fun i j => ?_)
    · simpa only [pcSmallValue] using h
    · have hkin : |kin (pcSourceMark z (i : ℕ)) (pcTargetMark z (j : ℕ))
          (mDisplacement (pcSourcePoint z (i : ℕ)) (pcTargetPoint z (j : ℕ)))| ≤
          C * (q : ℝ) :=
        (hkin_bound _ _ _).trans
          (mul_le_mul_of_nonneg_left (mDisplacement_sq_sum_le q _ _) hC0)
      have hdiff : pcEntry q ((ρ + δ : ℝ≥0) : ℝ) kin g t z (i : ℕ) (j : ℕ) -
          pcEntry q (ρ : ℝ) kin g t z (i : ℕ) (j : ℕ) =
          (aσ - aρ) * kin (pcSourceMark z (i : ℕ)) (pcTargetMark z (j : ℕ))
            (mDisplacement (pcSourcePoint z (i : ℕ)) (pcTargetPoint z (j : ℕ))) := by
        unfold pcEntry
        have h1 : ((ρ + δ : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) = aσ := rfl
        have h2 : (ρ : ℝ) ^ (2 / (q : ℝ)) = aρ := rfl
        rw [h1, h2]
        ring
      rw [hdiff, abs_mul]
      calc |aσ - aρ| * |kin (pcSourceMark z (i : ℕ)) (pcTargetMark z (j : ℕ))
            (mDisplacement (pcSourcePoint z (i : ℕ)) (pcTargetPoint z (j : ℕ)))|
          ≤ |aσ - aρ| * (C * (q : ℝ)) :=
            mul_le_mul_of_nonneg_left hkin (abs_nonneg _)
        _ = C * (q : ℝ) * |aσ - aρ| := by ring
  have hcomb : |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
      PartialMatching.maxCardValue midMat| ≤
      2 * Bσ * (pcExtraSource z : ℝ) + 2 * Bσ * (pcExtraTarget z : ℝ) := by
    calc |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
          PartialMatching.maxCardValue midMat|
        ≤ |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
            PartialMatching.maxCardValue rowRestr| +
          |PartialMatching.maxCardValue rowRestr -
            PartialMatching.maxCardValue midMat| := abs_sub_le _ _ _
      _ ≤ 2 * Bσ * (pcExtraSource z : ℝ) + 2 * Bσ * (pcExtraTarget z : ℝ) :=
          add_le_add hrow hcol
  calc |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
        pcSmallValue q (ρ : ℝ) kin g t z|
      ≤ |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
            PartialMatching.maxCardValue midMat| +
          |PartialMatching.maxCardValue midMat -
            pcSmallValue q (ρ : ℝ) kin g t z| := abs_sub_le _ _ _
    _ ≤ (2 * Bσ * (pcExtraSource z : ℝ) + 2 * Bσ * (pcExtraTarget z : ℝ)) +
          ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) *
            ((C * (q : ℝ)) * |aσ - aρ|) :=
        add_le_add hcomb hmid
    _ = 2 * Bσ * (pcExtraSource z : ℝ) + 2 * Bσ * (pcExtraTarget z : ℝ) +
          (C * (q : ℝ)) * |aσ - aρ| *
            ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) := by ring
    _ = 2 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (pcExtraSource z : ℝ) +
        2 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (pcExtraTarget z : ℝ) +
        (C * (q : ℝ)) *
          |Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow (ρ : ℝ) (2 / (q : ℝ))| *
            ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) := by
        simp only [Bσ, aσ, aρ]

/-! ## First-order stability of the marked pressure -/

set_option maxHeartbeats 2000000 in
/-- **First-order stability of the marked pressure in the intensity.**  Changing
the intensity from `rho` to `rho + delta` changes the pressure by at most the
uniform edge bound times `4 delta`, plus the change of the kinetic scale
`(rho+delta)^{2/q} - rho^{2/q}` times `C q rho`. -/
theorem markedPressure_diff_le
    (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (ρ δ : ℝ≥0) {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    |markedPressure q A B α β ρ kin g t -
      markedPressure q A B α β (ρ + δ) kin g t| ≤
      4 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (δ : ℝ) +
        C * (q : ℝ) *
          |Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow (ρ : ℝ) (2 / (q : ℝ))| * (ρ : ℝ) := by
  let P := markedPreCouple (q := q) A B α β ρ δ
  let Bσ : ℝ := Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G
  let aσ : ℝ := Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ))
  let aρ : ℝ := Real.rpow (ρ : ℝ) (2 / (q : ℝ))
  have hsmallEq := integral_markedTilted_preSmall (q := q) A B α β ρ δ
    hC0 hG0 hkin hkin_bound hg hgb t
  have hlargeEq := integral_markedTilted_preLarge (q := q) A B α β ρ δ
    hC0 hG0 hkin hkin_bound hg hgb t
  have hsmallInt : Integrable (fun z => pcSmallValue q (ρ : ℝ) kin g t z) P :=
    integrable_markedTilted_preSmall (q := q) A B α β ρ δ
      hC0 hG0 hkin hkin_bound hg hgb t
  have hlargeInt : Integrable (fun z =>
      pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z) P :=
    integrable_markedTilted_preLarge (q := q) A B α β ρ δ
      hC0 hG0 hkin hkin_bound hg hgb t
  have hsmallP : (∫ z, pcSmallValue q (ρ : ℝ) kin g t z ∂P) =
      markedPressure q A B α β ρ kin g t := hsmallEq.symm
  have hlargeP : (∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z ∂P) =
      markedPressure q A B α β (ρ + δ) kin g t := hlargeEq.symm
  have hpoint : ∀ z, |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
      pcSmallValue q (ρ : ℝ) kin g t z| ≤
      2 * Bσ * (pcExtraSource z : ℝ) + 2 * Bσ * (pcExtraTarget z : ℝ) +
        (C * (q : ℝ)) * |aσ - aρ| *
          ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) := by
    intro z
    have h := abs_pcLargeValue_sub_pcSmallValue_le (q := q) A B ρ δ (t := t)
      hC0 hG0 hkin_bound hgb z
    simpa only [Bσ, aσ, aρ] using h
  have hK := integrable_pcExtraSource (q := q) A B α β ρ δ
  have hL := integrable_pcExtraTarget (q := q) A B α β ρ δ
  have hM := integrable_pcMinCount (q := q) A B α β ρ δ
  have hboundInt : Integrable (fun z =>
      2 * Bσ * (pcExtraSource z : ℝ) + 2 * Bσ * (pcExtraTarget z : ℝ) +
        (C * (q : ℝ)) * |aσ - aρ| *
          ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ)) P :=
    ((hK.const_mul (2 * Bσ)).add (hL.const_mul (2 * Bσ))).add
      (hM.const_mul ((C * (q : ℝ)) * |aσ - aρ|))
  have hmain : |(∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z ∂P) -
      ∫ z, pcSmallValue q (ρ : ℝ) kin g t z ∂P| ≤
      4 * Bσ * (δ : ℝ) + (C * (q : ℝ)) * |aσ - aρ| * (ρ : ℝ) := by
    have hdiffInt : Integrable (fun z =>
        pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
          pcSmallValue q (ρ : ℝ) kin g t z) P := hlargeInt.sub hsmallInt
    have hAbsInt : Integrable (fun z =>
        |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
          pcSmallValue q (ρ : ℝ) kin g t z|) P := hdiffInt.abs
    have hsplit : (∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
          pcSmallValue q (ρ : ℝ) kin g t z ∂P) =
        (∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z ∂P) -
          ∫ z, pcSmallValue q (ρ : ℝ) kin g t z ∂P :=
      integral_sub hlargeInt hsmallInt
    calc |(∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z ∂P) -
          ∫ z, pcSmallValue q (ρ : ℝ) kin g t z ∂P|
        = |∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
            pcSmallValue q (ρ : ℝ) kin g t z ∂P| := by rw [hsplit]
      _ ≤ ∫ z, |pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z -
            pcSmallValue q (ρ : ℝ) kin g t z| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, (2 * Bσ * (pcExtraSource z : ℝ) + 2 * Bσ * (pcExtraTarget z : ℝ) +
            (C * (q : ℝ)) * |aσ - aρ| *
              ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ)) ∂P :=
          integral_mono hAbsInt hboundInt hpoint
      _ = 2 * Bσ * (∫ z, (pcExtraSource z : ℝ) ∂P) +
            2 * Bσ * (∫ z, (pcExtraTarget z : ℝ) ∂P) +
            ((C * (q : ℝ)) * |aσ - aρ|) *
              (∫ z, ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) ∂P) := by
          have h12 : (∫ z, 2 * Bσ * (pcExtraSource z : ℝ) +
                2 * Bσ * (pcExtraTarget z : ℝ) ∂P) =
              2 * Bσ * (∫ z, (pcExtraSource z : ℝ) ∂P) +
                2 * Bσ * (∫ z, (pcExtraTarget z : ℝ) ∂P) := by
            calc ∫ z, 2 * Bσ * (pcExtraSource z : ℝ) +
                  2 * Bσ * (pcExtraTarget z : ℝ) ∂P
                = ∫ z, (fun z => 2 * Bσ * (pcExtraSource z : ℝ)) z +
                    (fun z => 2 * Bσ * (pcExtraTarget z : ℝ)) z ∂P := rfl
              _ = (∫ z, (fun z => 2 * Bσ * (pcExtraSource z : ℝ)) z ∂P) +
                    ∫ z, (fun z => 2 * Bσ * (pcExtraTarget z : ℝ)) z ∂P :=
                  integral_add (hK.const_mul (2 * Bσ)) (hL.const_mul (2 * Bσ))
              _ = 2 * Bσ * (∫ z, (pcExtraSource z : ℝ) ∂P) +
                    2 * Bσ * (∫ z, (pcExtraTarget z : ℝ) ∂P) := by
                  rw [integral_const_mul, integral_const_mul]
          have h3 : (∫ z, ((C * (q : ℝ)) * |aσ - aρ|) *
                ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) ∂P) =
              ((C * (q : ℝ)) * |aσ - aρ|) *
                (∫ z, ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) ∂P) :=
            integral_const_mul ((C * (q : ℝ)) * |aσ - aρ|) _
          calc ∫ z, (2 * Bσ * (pcExtraSource z : ℝ) +
                2 * Bσ * (pcExtraTarget z : ℝ)) +
                (C * (q : ℝ)) * |aσ - aρ| *
                  ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) ∂P
              = ∫ z, (fun z => 2 * Bσ * (pcExtraSource z : ℝ) +
                    2 * Bσ * (pcExtraTarget z : ℝ)) z +
                  (fun z => (C * (q : ℝ)) * |aσ - aρ| *
                    ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ)) z ∂P := rfl
            _ = (∫ z, (fun z => 2 * Bσ * (pcExtraSource z : ℝ) +
                    2 * Bσ * (pcExtraTarget z : ℝ)) z ∂P) +
                  ∫ z, (fun z => (C * (q : ℝ)) * |aσ - aρ| *
                    ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ)) z ∂P :=
                integral_add ((hK.const_mul (2 * Bσ)).add (hL.const_mul (2 * Bσ)))
                  (hM.const_mul ((C * (q : ℝ)) * |aσ - aρ|))
            _ = 2 * Bσ * (∫ z, (pcExtraSource z : ℝ) ∂P) +
                  2 * Bσ * (∫ z, (pcExtraTarget z : ℝ) ∂P) +
                  ((C * (q : ℝ)) * |aσ - aρ|) *
                    (∫ z, ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) ∂P) := by
                simp only [h12, h3]
      _ = 2 * Bσ * (δ : ℝ) + 2 * Bσ * (δ : ℝ) +
            ((C * (q : ℝ)) * |aσ - aρ|) *
              (∫ z, ((min (pcSourceCount z) (pcTargetCount z) : ℕ) : ℝ) ∂P) := by
          rw [integral_pcExtraSource (q := q) A B α β ρ δ,
            integral_pcExtraTarget (q := q) A B α β ρ δ]
      _ ≤ 2 * Bσ * (δ : ℝ) + 2 * Bσ * (δ : ℝ) +
            ((C * (q : ℝ)) * |aσ - aρ|) * (ρ : ℝ) := by
          have hmin := integral_pcMinCount_le (q := q) A B α β ρ δ
          have hcoef : 0 ≤ (C * (q : ℝ)) * |aσ - aρ| :=
            mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg q)) (abs_nonneg _)
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmin hcoef)
      _ = 4 * Bσ * (δ : ℝ) + (C * (q : ℝ)) * |aσ - aρ| * (ρ : ℝ) := by ring
  calc |markedPressure q A B α β ρ kin g t -
        markedPressure q A B α β (ρ + δ) kin g t|
      = |(∫ z, pcSmallValue q (ρ : ℝ) kin g t z ∂P) -
          ∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z ∂P| := by
        rw [hsmallP, hlargeP]
    _ = |(∫ z, pcLargeValue q ((ρ + δ : ℝ≥0) : ℝ) kin g t z ∂P) -
          ∫ z, pcSmallValue q (ρ : ℝ) kin g t z ∂P| := by
        rw [abs_sub_comm]
    _ ≤ 4 * Bσ * (δ : ℝ) + (C * (q : ℝ)) * |aσ - aρ| * (ρ : ℝ) := hmain
    _ = 4 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (δ : ℝ) +
        C * (q : ℝ) *
          |Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow (ρ : ℝ) (2 / (q : ℝ))| * (ρ : ℝ) := by
        simp only [Bσ, aσ, aρ]

/-! ## Continuity in the intensity -/

/-- The kinetic intensity scale `r ↦ r ^ (2/q)` is continuous on `ℝ≥0`. -/
theorem continuous_rpow_intensity (q : ℕ) :
    Continuous fun r : ℝ≥0 => Real.rpow (r : ℝ) (2 / (q : ℝ)) := by
  have hq : (0 : ℝ) ≤ 2 / (q : ℝ) := by positivity
  exact (Real.continuous_rpow_const hq).comp (by fun_prop)

set_option maxHeartbeats 2000000 in
/-- **Continuity of the normalized marked pressure in the intensity.**  For
`rho ≥ 1`, the normalized pressure `r ↦ markedPressure r / r` is continuous at
`rho` along the right: adding a small `delta` changes the normalized pressure by
`o(1)`. -/
theorem tendsto_markedPressure_scale
    (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {ρ : ℝ≥0} (hρ : 1 ≤ ρ) :
    Tendsto (fun δ : ℝ≥0 =>
        markedPressure q A B α β (ρ + δ) kin g t / ((ρ + δ : ℝ≥0) : ℝ))
      (𝓝 0) (𝓝 (markedPressure q A B α β ρ kin g t / (ρ : ℝ))) := by
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
    linarith
  have hρne : (ρ : ℝ) ≠ 0 := hρpos.ne'
  have hshift : Tendsto (fun δ : ℝ≥0 => ρ + δ) (𝓝 0) (𝓝 ρ) := by
    have hcont : Continuous fun δ : ℝ≥0 => ρ + δ := continuous_const.add continuous_id
    simpa using hcont.tendsto (0 : ℝ≥0)
  have hshiftR : Tendsto (fun δ : ℝ≥0 => ((ρ + δ : ℝ≥0) : ℝ)) (𝓝 0) (𝓝 (ρ : ℝ)) := by
    have hcoe : Continuous fun r : ℝ≥0 => (r : ℝ) := by fun_prop
    simpa only [Function.comp_def, NNReal.coe_add] using (hcoe.tendsto ρ).comp hshift
  have ha : Tendsto (fun δ : ℝ≥0 => Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)))
      (𝓝 0) (𝓝 (Real.rpow (ρ : ℝ) (2 / (q : ℝ)))) := by
    simpa only [Function.comp_def] using
      ((continuous_rpow_intensity q).tendsto ρ).comp hshift
  have hB : Tendsto (fun δ : ℝ≥0 =>
      Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)
      (𝓝 0) (𝓝 (Real.rpow (ρ : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)) :=
    (ha.mul tendsto_const_nhds).add tendsto_const_nhds
  have hδR : Tendsto (fun δ : ℝ≥0 => (δ : ℝ)) (𝓝 0) (𝓝 0) := by
    have hcoe : Continuous fun r : ℝ≥0 => (r : ℝ) := by fun_prop
    simpa using hcoe.tendsto (0 : ℝ≥0)
  have hterm1 : Tendsto (fun δ : ℝ≥0 =>
      4 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        (δ : ℝ)) (𝓝 0) (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (4 : ℝ))).mul hB).mul hδR
    simpa using h
  have hdiffa : Tendsto (fun δ : ℝ≥0 =>
      Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
        Real.rpow (ρ : ℝ) (2 / (q : ℝ))) (𝓝 0) (𝓝 0) := by
    simpa using ha.sub (tendsto_const_nhds
      (x := Real.rpow (ρ : ℝ) (2 / (q : ℝ))))
  have habs : Tendsto (fun δ : ℝ≥0 =>
      |Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
        Real.rpow (ρ : ℝ) (2 / (q : ℝ))|) (𝓝 0) (𝓝 0) := by
    simpa using hdiffa.abs
  have hterm2 : Tendsto (fun δ : ℝ≥0 =>
      C * (q : ℝ) *
        |Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
          Real.rpow (ρ : ℝ) (2 / (q : ℝ))| * (ρ : ℝ)) (𝓝 0) (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := C * (q : ℝ))).mul habs).mul
      (tendsto_const_nhds (x := (ρ : ℝ)))
    simpa using h
  have hbound_tendsto : Tendsto (fun δ : ℝ≥0 =>
      4 * (Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          (δ : ℝ) +
        C * (q : ℝ) *
          |Real.rpow ((ρ + δ : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow (ρ : ℝ) (2 / (q : ℝ))| * (ρ : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using hterm1.add hterm2
  have hdiff : Tendsto (fun δ : ℝ≥0 =>
      markedPressure q A B α β (ρ + δ) kin g t -
        markedPressure q A B α β ρ kin g t) (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm (fun δ => ?_) hbound_tendsto
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact markedPressure_diff_le q A B α β ρ δ hC0 hG0 hkin hkin_bound hg hgb
  have hinv : Tendsto (fun δ : ℝ≥0 => 1 / ((ρ + δ : ℝ≥0) : ℝ))
      (𝓝 0) (𝓝 (1 / (ρ : ℝ))) := by
    have hcont : ContinuousAt (fun x : ℝ => 1 / x) (ρ : ℝ) := by
      simpa only [one_div] using continuousAt_inv₀ hρne
    exact hcont.tendsto.comp hshiftR
  have htermA : Tendsto (fun δ : ℝ≥0 =>
      (markedPressure q A B α β (ρ + δ) kin g t -
          markedPressure q A B α β ρ kin g t) / ((ρ + δ : ℝ≥0) : ℝ))
      (𝓝 0) (𝓝 0) := by
    have h := hdiff.mul hinv
    simpa [div_eq_mul_inv] using h
  have htermB : Tendsto (fun δ : ℝ≥0 =>
      markedPressure q A B α β ρ kin g t *
        (1 / ((ρ + δ : ℝ≥0) : ℝ) - 1 / (ρ : ℝ))) (𝓝 0) (𝓝 0) := by
    have hsub : Tendsto (fun δ : ℝ≥0 =>
        1 / ((ρ + δ : ℝ≥0) : ℝ) - 1 / (ρ : ℝ)) (𝓝 0) (𝓝 0) := by
      simpa using hinv.sub (tendsto_const_nhds (x := 1 / (ρ : ℝ)))
    have h := (tendsto_const_nhds
      (x := markedPressure q A B α β ρ kin g t)).mul hsub
    simpa using h
  have hdiff2 : Tendsto (fun δ : ℝ≥0 =>
      markedPressure q A B α β (ρ + δ) kin g t / ((ρ + δ : ℝ≥0) : ℝ) -
        markedPressure q A B α β ρ kin g t / (ρ : ℝ)) (𝓝 0) (𝓝 0) := by
    have hdecomp : ∀ δ : ℝ≥0,
        markedPressure q A B α β (ρ + δ) kin g t / ((ρ + δ : ℝ≥0) : ℝ) -
          markedPressure q A B α β ρ kin g t / (ρ : ℝ) =
        (markedPressure q A B α β (ρ + δ) kin g t -
            markedPressure q A B α β ρ kin g t) / ((ρ + δ : ℝ≥0) : ℝ) +
          markedPressure q A B α β ρ kin g t *
            (1 / ((ρ + δ : ℝ≥0) : ℝ) - 1 / (ρ : ℝ)) := by
      intro δ
      have h1 : ((ρ + δ : ℝ≥0) : ℝ) ≠ 0 := by
        have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
        have h : (0 : ℝ) < ((ρ + δ : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_add]
          linarith
        exact h.ne'
      have h2 : (ρ : ℝ) ≠ 0 := hρne
      field_simp
      ring
    simp_rw [hdecomp]
    simpa using htermA.add htermB
  have hfinal := hdiff2.add (tendsto_const_nhds
    (x := markedPressure q A B α β ρ kin g t / (ρ : ℝ)))
  simpa using hfinal

/-! ## Two-sided stability and continuity at every positive intensity -/

/-- Two-sided form of `markedPressure_diff_le`: the pressure difference is
bounded by the uniform edge bound at the larger intensity times the distance,
plus the kinetic-scale difference between the larger and smaller intensities
times the smaller intensity. -/
theorem abs_markedPressure_sub_le_max_min
    (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (ρ r : ℝ≥0) {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    |markedPressure q A B α β ρ kin g t -
      markedPressure q A B α β r kin g t| ≤
      4 * (Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          |(r : ℝ) - (ρ : ℝ)| +
        C * (q : ℝ) *
          |Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow ((min ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ))| *
          ((min ρ r : ℝ≥0) : ℝ) := by
  rcases le_total ρ r with h | h
  · have hsum : ρ + (r - ρ) = r := add_tsub_cancel_of_le h
    have hdiff := markedPressure_diff_le (q := q) (t := t) A B α β ρ (r - ρ)
      hC0 hG0 hkin hkin_bound hg hgb
    have hmax : max ρ r = r := max_eq_right h
    have hmin : min ρ r = ρ := min_eq_left h
    have hdist : ((r - ρ : ℝ≥0) : ℝ) = |(r : ℝ) - (ρ : ℝ)| := by
      rw [NNReal.coe_sub h]
      exact (abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))).symm
    simpa only [hsum, hmax, hmin, hdist] using hdiff
  · have hsum : r + (ρ - r) = ρ := add_tsub_cancel_of_le h
    have hdiff := markedPressure_diff_le (q := q) (t := t) A B α β r (ρ - r)
      hC0 hG0 hkin hkin_bound hg hgb
    have hmax : max ρ r = ρ := max_eq_left h
    have hmin : min ρ r = r := min_eq_right h
    have hdist : ((ρ - r : ℝ≥0) : ℝ) = |(r : ℝ) - (ρ : ℝ)| := by
      rw [NNReal.coe_sub h, abs_sub_comm]
      exact (abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))).symm
    simpa only [hsum, hmax, hmin, hdist, abs_sub_comm] using hdiff

set_option maxHeartbeats 2000000 in
/-- **Two-sided continuity of the normalized marked pressure at every positive
intensity.**  For `rho > 0`, `r ↦ markedPressure r / r` is continuous at
`rho`. -/
theorem continuousAt_markedPressure_scale
    (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {ρ : ℝ≥0} (hρ : 0 < ρ) :
    ContinuousAt (fun r : ℝ≥0 =>
      markedPressure q A B α β r kin g t / (r : ℝ)) ρ := by
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have hρne : (ρ : ℝ) ≠ 0 := hρpos.ne'
  let B2 : ℝ≥0 → ℝ := fun r =>
    4 * (Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
        |(r : ℝ) - (ρ : ℝ)| +
      C * (q : ℝ) *
        |Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
          Real.rpow ((min ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ))| *
          ((min ρ r : ℝ≥0) : ℝ)
  have htwo : ∀ r : ℝ≥0, |markedPressure q A B α β ρ kin g t -
      markedPressure q A B α β r kin g t| ≤ B2 r := by
    intro r
    exact abs_markedPressure_sub_le_max_min (q := q) A B α β ρ r
      hC0 hG0 hkin hkin_bound hg hgb
  have hmax : Tendsto (fun r : ℝ≥0 => max ρ r) (𝓝 ρ) (𝓝 ρ) := by
    have hcont : Continuous fun r : ℝ≥0 => max ρ r := continuous_const.max continuous_id
    simpa using hcont.tendsto ρ
  have hmin : Tendsto (fun r : ℝ≥0 => min ρ r) (𝓝 ρ) (𝓝 ρ) := by
    have hcont : Continuous fun r : ℝ≥0 => min ρ r := continuous_const.min continuous_id
    simpa using hcont.tendsto ρ
  have haMax : Tendsto (fun r : ℝ≥0 => Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)))
      (𝓝 ρ) (𝓝 (Real.rpow (ρ : ℝ) (2 / (q : ℝ)))) := by
    simpa only [Function.comp_def] using ((continuous_rpow_intensity q).tendsto ρ).comp hmax
  have haMin : Tendsto (fun r : ℝ≥0 => Real.rpow ((min ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)))
      (𝓝 ρ) (𝓝 (Real.rpow (ρ : ℝ) (2 / (q : ℝ)))) := by
    simpa only [Function.comp_def] using ((continuous_rpow_intensity q).tendsto ρ).comp hmin
  have hdist : Tendsto (fun r : ℝ≥0 => |(r : ℝ) - (ρ : ℝ)|) (𝓝 ρ) (𝓝 0) := by
    have hcont : Continuous fun r : ℝ≥0 => |(r : ℝ) - (ρ : ℝ)| := by fun_prop
    simpa using hcont.tendsto ρ
  have hB2_tendsto : Tendsto B2 (𝓝 ρ) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ≥0 =>
        4 * (Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) *
          |(r : ℝ) - (ρ : ℝ)|) (𝓝 ρ) (𝓝 0) := by
      have hBmax : Tendsto (fun r : ℝ≥0 =>
          Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)
          (𝓝 ρ) (𝓝 (Real.rpow (ρ : ℝ) (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)) :=
        (haMax.mul tendsto_const_nhds).add tendsto_const_nhds
      have h := ((tendsto_const_nhds (x := (4 : ℝ))).mul hBmax).mul hdist
      simpa using h
    have h2 : Tendsto (fun r : ℝ≥0 =>
        C * (q : ℝ) *
          |Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow ((min ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ))| *
          ((min ρ r : ℝ≥0) : ℝ)) (𝓝 ρ) (𝓝 0) := by
      have hsub : Tendsto (fun r : ℝ≥0 =>
          Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow ((min ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ))) (𝓝 ρ) (𝓝 0) := by
        simpa using haMax.sub haMin
      have habs : Tendsto (fun r : ℝ≥0 =>
          |Real.rpow ((max ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ)) -
            Real.rpow ((min ρ r : ℝ≥0) : ℝ) (2 / (q : ℝ))|) (𝓝 ρ) (𝓝 0) := by
        simpa using hsub.abs
      have hminR : Tendsto (fun r : ℝ≥0 => ((min ρ r : ℝ≥0) : ℝ)) (𝓝 ρ) (𝓝 (ρ : ℝ)) := by
        have hcont : Continuous fun r : ℝ≥0 => ((min ρ r : ℝ≥0) : ℝ) := by fun_prop
        simpa using hcont.tendsto ρ
      have h := ((tendsto_const_nhds (x := C * (q : ℝ))).mul habs).mul hminR
      simpa using h
    simpa [B2] using h1.add h2
  have hdiff : Tendsto (fun r : ℝ≥0 =>
      markedPressure q A B α β r kin g t -
        markedPressure q A B α β ρ kin g t) (𝓝 ρ) (𝓝 0) := by
    refine squeeze_zero_norm (fun r => ?_) hB2_tendsto
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact htwo r
  have hcoe : Continuous fun r : ℝ≥0 => (r : ℝ) := by fun_prop
  have hinv : Tendsto (fun r : ℝ≥0 => 1 / (r : ℝ)) (𝓝 ρ) (𝓝 (1 / (ρ : ℝ))) := by
    have hcont : ContinuousAt (fun x : ℝ => 1 / x) (ρ : ℝ) := by
      simpa only [one_div] using continuousAt_inv₀ hρne
    exact hcont.tendsto.comp (hcoe.tendsto ρ)
  have htermA : Tendsto (fun r : ℝ≥0 =>
      (markedPressure q A B α β r kin g t -
          markedPressure q A B α β ρ kin g t) / (r : ℝ))
      (𝓝 ρ) (𝓝 0) := by
    have h := hdiff.mul hinv
    simpa [div_eq_mul_inv] using h
  have htermB : Tendsto (fun r : ℝ≥0 =>
      markedPressure q A B α β ρ kin g t *
        (1 / (r : ℝ) - 1 / (ρ : ℝ))) (𝓝 ρ) (𝓝 0) := by
    have hsub : Tendsto (fun r : ℝ≥0 =>
        1 / (r : ℝ) - 1 / (ρ : ℝ)) (𝓝 ρ) (𝓝 0) := by
      simpa using hinv.sub (tendsto_const_nhds (x := 1 / (ρ : ℝ)))
    have h := (tendsto_const_nhds
      (x := markedPressure q A B α β ρ kin g t)).mul hsub
    simpa using h
  have hdiff2 : Tendsto (fun r : ℝ≥0 =>
      markedPressure q A B α β r kin g t / (r : ℝ) -
        markedPressure q A B α β ρ kin g t / (ρ : ℝ)) (𝓝 ρ) (𝓝 0) := by
    have hdecomp : ∀ r : ℝ≥0,
        markedPressure q A B α β r kin g t / (r : ℝ) -
          markedPressure q A B α β ρ kin g t / (ρ : ℝ) =
        (markedPressure q A B α β r kin g t -
            markedPressure q A B α β ρ kin g t) / (r : ℝ) +
          markedPressure q A B α β ρ kin g t *
            (1 / (r : ℝ) - 1 / (ρ : ℝ)) := by
      intro r
      by_cases hr : (r : ℝ) = 0
      · simp [hr, div_eq_mul_inv]
      · field_simp [hρne]
        ring
    rw [show (fun r : ℝ≥0 =>
        markedPressure q A B α β r kin g t / (r : ℝ) -
          markedPressure q A B α β ρ kin g t / (ρ : ℝ)) =
        fun r : ℝ≥0 =>
          (markedPressure q A B α β r kin g t -
              markedPressure q A B α β ρ kin g t) / (r : ℝ) +
            markedPressure q A B α β ρ kin g t *
              (1 / (r : ℝ) - 1 / (ρ : ℝ)) from funext hdecomp]
    simpa using htermA.add htermB
  have hfinal := hdiff2.add (tendsto_const_nhds
    (x := markedPressure q A B α β ρ kin g t / (ρ : ℝ)))
  show Tendsto (fun r : ℝ≥0 =>
    markedPressure q A B α β r kin g t / (r : ℝ)) (𝓝 ρ)
    (𝓝 (markedPressure q A B α β ρ kin g t / (ρ : ℝ)))
  simpa only [sub_add_cancel, zero_add] using hfinal

/-- Right-sided continuity at every positive intensity; this weakens the
hypothesis `1 ≤ ρ` of `tendsto_markedPressure_scale` to `0 < ρ`. -/
theorem tendsto_markedPressure_scale'
    (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {ρ : ℝ≥0} (hρ : 0 < ρ) :
    Tendsto (fun δ : ℝ≥0 =>
        markedPressure q A B α β (ρ + δ) kin g t / ((ρ + δ : ℝ≥0) : ℝ))
      (𝓝 0) (𝓝 (markedPressure q A B α β ρ kin g t / (ρ : ℝ))) := by
  have hcont := continuousAt_markedPressure_scale (q := q) (t := t) A B α β
    hC0 hG0 hkin hkin_bound hg hgb hρ
  have hshift : Tendsto (fun δ : ℝ≥0 => ρ + δ) (𝓝 0) (𝓝 ρ) := by
    have hc : Continuous fun δ : ℝ≥0 => ρ + δ := continuous_const.add continuous_id
    simpa using hc.tendsto (0 : ℝ≥0)
  simpa only [Function.comp_def] using hcont.tendsto.comp hshift

end
