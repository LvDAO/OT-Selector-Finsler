import OTSelector.Reconstruction.FinslerPopulationAtlasPressure
import OTSelector.Analysis.Convex.AffineInfimum

/-!
# Weighted and second-moment stationary pressure values and their atlas

This module supplies the interface between the abstract stationary minimisation
of `StationaryPressureClasses` and the population atlas pressure of
`FinslerPopulationAtlasPressure`.

The paper defines, at every root, the weighted stationary pressure `I_{j,w}` and
the second-moment pressure `I_{j,2}` as infima of kinetic energy plus tilt times
the bounded mark probe over two matching classes, the second one requiring a
finite unweighted second moment (`main.tex`, definition
`general-gluing-two-classes`).  Its displayed bounds are
`-|v| ||f||_∞ ≤ I_{j,w} ≤ I_{j,2} ≤ C_q + |v| ||f||_∞`
(`general-gluing-uniform-pressure-bounds`).

Here the concrete point-process matching model is kept abstract: a
`StationaryPressureDatum` records a matching type `W`, the two admissible
classes `Cw` and `C2`, the kinetic energy `K`, the probe `P`, the class
inclusion `C2 ⊆ Cw`, the probe bound `|P| ≤ G`, and finite-kinetic competitors
with `K ≤ Cb`.  The values are

`I_w v = stationaryValue K P Cw v`, `I_2 v = stationaryValue K P C2 v`.

From the infimum representation we prove the class order `I_w ≤ I_2`, the lower
bound `-|v| G ≤ I_w`, the absolute bounds `|I_w v|`, `|I_2 v| ≤ Cb + |v| G`,
concavity and `G`-Lipschitz continuity in the tilt.

The second half instantiates the atlas: the family

`stationaryPressureFamily K P Cw j z v = stationaryValue (K j z) (P j z) (Cw j z) v`

is plugged into `populationAtlasPressure`. The root integrand has inverse density
weight; the Haar integrand has the positive weight `1-2/q`. Full-atlas bounds use
the actual Haar L1 majorants from the atlas module. The finite weighted-sum
approximation is specialised to the stationary family on produced compact cores.

Remaining gaps (out of scope by design): the concrete construction of the
matching type and of the two admissible classes, their nonemptiness, the
Campbell/finite-domination lower comparison identifying the empirical pressure
with the atlas pressure, and the regularity (continuity in the root) of the
stationary values.  These are kept as explicit hypotheses where used.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-! ## Abstract stationary pressure datum -/

/-- An abstract weighted/second-moment stationary pressure datum.

`K` is the kinetic energy, `P` the bounded mark probe, `Cw` the class of
stationary matchings with finite weighted kinetic mean, and `C2` the subclass
with finite unweighted second moment.  `G` bounds the probe and `Cb` bounds the
kinetic energy of the two competitors. -/
structure StationaryPressureDatum (W : Type*) (G Cb : ℝ) where
  /-- Kinetic energy of a matching. -/
  K : W → ℝ
  /-- Bounded mark probe of a matching. -/
  P : W → ℝ
  /-- Stationary matchings with finite weighted kinetic mean. -/
  Cw : Set W
  /-- Stationary matchings with finite unweighted second moment. -/
  C2 : Set W
  /-- The second-moment class is contained in the weighted class. -/
  C2_subset_Cw : C2 ⊆ Cw
  /-- Kinetic energy is nonnegative on the weighted class. -/
  kinetic_nonneg : ∀ w ∈ Cw, 0 ≤ K w
  /-- The probe is uniformly bounded on the weighted class. -/
  probe_bound : ∀ w ∈ Cw, |P w| ≤ G
  /-- A weighted-class competitor with bounded kinetic energy. -/
  competitor : W
  competitor_mem : competitor ∈ Cw
  kinetic_competitor_le : K competitor ≤ Cb
  /-- A second-moment-class competitor with bounded kinetic energy. -/
  competitor2 : W
  competitor2_mem : competitor2 ∈ C2
  kinetic_competitor2_le : K competitor2 ≤ Cb

namespace StationaryPressureDatum

variable {W : Type*} {G Cb : ℝ}

/-- The weighted stationary pressure `I_w`. -/
def Iw (D : StationaryPressureDatum W G Cb) (v : ℝ) : ℝ :=
  stationaryValue D.K D.P D.Cw v

/-- The second-moment stationary pressure `I_2`. -/
def I2 (D : StationaryPressureDatum W G Cb) (v : ℝ) : ℝ :=
  stationaryValue D.K D.P D.C2 v

/-- The weighted class is nonempty, witnessed by its competitor. -/
theorem nonempty_Cw (D : StationaryPressureDatum W G Cb) : D.Cw.Nonempty :=
  ⟨D.competitor, D.competitor_mem⟩

/-- The second-moment class is nonempty, witnessed by its competitor. -/
theorem nonempty_C2 (D : StationaryPressureDatum W G Cb) : D.C2.Nonempty :=
  ⟨D.competitor2, D.competitor2_mem⟩

/-- The probe bound is nonnegative. -/
theorem bound_nonneg (D : StationaryPressureDatum W G Cb) : 0 ≤ G := by
  obtain ⟨w, hw⟩ := D.nonempty_Cw
  exact (abs_nonneg (D.P w)).trans (D.probe_bound w hw)

/-- The competitor bound is nonnegative. -/
theorem competitor_bound_nonneg (D : StationaryPressureDatum W G Cb) : 0 ≤ Cb :=
  (D.kinetic_nonneg D.competitor D.competitor_mem).trans D.kinetic_competitor_le

/-- The weighted value set is bounded below at every tilt. -/
theorem bddBelow_Cw (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    BddBelow ((fun w ↦ D.K w + v * D.P w) '' D.Cw) :=
  bddBelow_stationaryValue (G := G) (v := v) D.kinetic_nonneg D.probe_bound

/-- The second-moment value set is bounded below at every tilt. -/
theorem bddBelow_C2 (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    BddBelow ((fun w ↦ D.K w + v * D.P w) '' D.C2) :=
  bddBelow_stationaryValue (G := G) (v := v)
    (fun w hw ↦ D.kinetic_nonneg w (D.C2_subset_Cw hw))
    (fun w hw ↦ D.probe_bound w (D.C2_subset_Cw hw))

/-- The weighted value is at most the second-moment value: enlarging the class
can only lower the infimum. -/
theorem Iw_le_I2 (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    D.Iw v ≤ D.I2 v :=
  stationaryValue_mono_class (K := D.K) (P := D.P) (admissible₁ := D.Cw)
    (admissible₂ := D.C2) (v := v) D.C2_subset_Cw D.nonempty_C2 (D.bddBelow_Cw v)

/-- The paper's lower bound `-|v| G ≤ I_w`. -/
theorem neg_abs_mul_le_Iw (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    -(|v| * G) ≤ D.Iw v :=
  neg_abs_mul_le_stationaryValue (G := G) (v := v) D.nonempty_Cw
    D.kinetic_nonneg D.probe_bound

/-- The same lower bound for `I_2`. -/
theorem neg_abs_mul_le_I2 (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    -(|v| * G) ≤ D.I2 v :=
  neg_abs_mul_le_stationaryValue (G := G) (v := v) D.nonempty_C2
    (fun w hw ↦ D.kinetic_nonneg w (D.C2_subset_Cw hw))
    (fun w hw ↦ D.probe_bound w (D.C2_subset_Cw hw))

/-- The absolute growth bound `|I_w v| ≤ Cb + |v| G`. -/
theorem abs_Iw_le (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    |D.Iw v| ≤ Cb + |v| * G :=
  abs_stationaryValue_le_add_abs_mul D.competitor_bound_nonneg D.nonempty_Cw
    D.kinetic_nonneg D.probe_bound
    ⟨D.competitor, D.competitor_mem, D.kinetic_competitor_le⟩ v

/-- The corresponding upper bound `I_w v ≤ Cb + |v| G`. -/
theorem Iw_le_upper (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    D.Iw v ≤ Cb + |v| * G :=
  (abs_le.mp (D.abs_Iw_le v)).2

/-- The absolute growth bound `|I_2 v| ≤ Cb + |v| G`, using the second-moment
competitor. -/
theorem abs_I2_le (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    |D.I2 v| ≤ Cb + |v| * G :=
  abs_stationaryValue_le_add_abs_mul D.competitor_bound_nonneg D.nonempty_C2
    (fun w hw ↦ D.kinetic_nonneg w (D.C2_subset_Cw hw))
    (fun w hw ↦ D.probe_bound w (D.C2_subset_Cw hw))
    ⟨D.competitor2, D.competitor2_mem, D.kinetic_competitor2_le⟩ v

/-- The corresponding upper bound `I_2 v ≤ Cb + |v| G`. -/
theorem I2_le_upper (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    D.I2 v ≤ Cb + |v| * G :=
  (abs_le.mp (D.abs_I2_le v)).2

/-- The full displayed chain
`-|v| G ≤ I_w v ≤ I_2 v ≤ Cb + |v| G`. -/
theorem neg_abs_mul_le_Iw_le_I2_le_upper (D : StationaryPressureDatum W G Cb) (v : ℝ) :
    -(|v| * G) ≤ D.Iw v ∧ D.Iw v ≤ D.I2 v ∧ D.I2 v ≤ Cb + |v| * G :=
  ⟨D.neg_abs_mul_le_Iw v, D.Iw_le_I2 v, D.I2_le_upper v⟩

/-- The weighted pressure is concave in the tilt. -/
theorem concaveOn_Iw (D : StationaryPressureDatum W G Cb) :
    ConcaveOn ℝ univ (fun v ↦ D.Iw v) :=
  concaveOn_stationaryValue D.nonempty_Cw D.bddBelow_Cw

/-- The second-moment pressure is concave in the tilt. -/
theorem concaveOn_I2 (D : StationaryPressureDatum W G Cb) :
    ConcaveOn ℝ univ (fun v ↦ D.I2 v) :=
  concaveOn_stationaryValue D.nonempty_C2 D.bddBelow_C2

/-- The weighted pressure is `G`-Lipschitz in the tilt. -/
theorem abs_Iw_sub_le (D : StationaryPressureDatum W G Cb) (v u : ℝ) :
    |D.Iw v - D.Iw u| ≤ G * |v - u| :=
  abs_stationaryValue_sub_le D.nonempty_Cw D.bddBelow_Cw D.bound_nonneg
    D.probe_bound v u

/-- The second-moment pressure is `G`-Lipschitz in the tilt. -/
theorem abs_I2_sub_le (D : StationaryPressureDatum W G Cb) (v u : ℝ) :
    |D.I2 v - D.I2 u| ≤ G * |v - u| :=
  abs_stationaryValue_sub_le D.nonempty_C2 D.bddBelow_C2 D.bound_nonneg
    (fun w hw ↦ D.probe_bound w (D.C2_subset_Cw hw)) v u

end StationaryPressureDatum

/-! ## The stationary pressure family over roots -/

section AtlasFamily

variable {W Z : Type*}

/-- The family `I j z v = stationaryValue (K j z) (P j z) (Cw j z) v` used as the
local weighted pressure of the `j`-th root piece at the root `z`. -/
def stationaryPressureFamily (K : ℕ → Z → W → ℝ) (P : ℕ → Z → W → ℝ)
    (Cw : ℕ → Z → Set W) : ℕ → Z → ℝ → ℝ :=
  fun j z v ↦ stationaryValue (K j z) (P j z) (Cw j z) v

/-- The second-moment analogue `I_2` of the stationary pressure family. -/
def stationarySecondMomentFamily (K : ℕ → Z → W → ℝ) (P : ℕ → Z → W → ℝ)
    (C2 : ℕ → Z → Set W) : ℕ → Z → ℝ → ℝ :=
  fun j z v ↦ stationaryValue (K j z) (P j z) (C2 j z) v

/-- Uniform absolute growth of the stationary pressure family. -/
theorem abs_stationaryPressureFamily_le {G Cb : ℝ}
    (K : ℕ → Z → W → ℝ) (P : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |P j z w| ≤ G)
    (hcomp : ∀ j z, ∃ w ∈ Cw j z, K j z w ≤ Cb)
    (j : ℕ) (z : Z) (v : ℝ) :
    |stationaryPressureFamily K P Cw j z v| ≤ Cb + |v| * G := by
  obtain ⟨w0, hw0, hKw0⟩ := hcomp j z
  have hCb : 0 ≤ Cb := (hK j z w0 hw0).trans hKw0
  exact abs_stationaryValue_le_add_abs_mul hCb ⟨w0, hw0⟩
    (fun w hw ↦ hK j z w hw) (fun w hw ↦ hP j z w hw)
    ⟨w0, hw0, hKw0⟩ v

/-- Uniform lower bound for the stationary pressure family. -/
theorem neg_abs_mul_le_stationaryPressureFamily {G : ℝ}
    (K : ℕ → Z → W → ℝ) (P : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |P j z w| ≤ G)
    (hcomp : ∀ j z, ∃ w ∈ Cw j z, K j z w ≤ Cb)
    (j : ℕ) (z : Z) (v : ℝ) :
    -(|v| * G) ≤ stationaryPressureFamily K P Cw j z v := by
  obtain ⟨w0, hw0, _⟩ := hcomp j z
  exact neg_abs_mul_le_stationaryValue (G := G) (v := v) ⟨w0, hw0⟩
    (fun w hw ↦ hK j z w hw) (fun w hw ↦ hP j z w hw)

/-- The weighted family is pointwise at most the second-moment family. -/
theorem stationaryPressureFamily_le_secondMomentFamily {G : ℝ}
    (K : ℕ → Z → W → ℝ) (P : ℕ → Z → W → ℝ)
    (Cw C2 : ℕ → Z → Set W)
    (hsub : ∀ j z, C2 j z ⊆ Cw j z)
    (hne : ∀ j z, (C2 j z).Nonempty)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |P j z w| ≤ G)
    (j : ℕ) (z : Z) (v : ℝ) :
    stationaryPressureFamily K P Cw j z v ≤
      stationarySecondMomentFamily K P C2 j z v := by
  have hbdd : BddBelow ((fun w ↦ K j z w + v * P j z w) '' Cw j z) :=
    bddBelow_stationaryValue (G := G) (v := v)
      (fun w hw ↦ hK j z w hw) (fun w hw ↦ hP j z w hw)
  exact stationaryValue_mono_class (K := K j z) (P := P j z)
    (admissible₁ := Cw j z) (admissible₂ := C2 j z) (v := v)
    (hsub j z) (hne j z) hbdd

end AtlasFamily

/-! ## Instantiation of the population atlas -/

section PopulationInstantiation

variable {E M Z W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The Haar-weighted atlas integrand built from the stationary pressure family
is uniformly bounded by `Cb * U^(1-2/q) + |t| * G * U` whenever `θ ≤ U` and
`q > 2`.  This bound is for Haar integration; it does not bound the population integrand. -/
theorem abs_populationAtlasHaarIntegrand_stationary_le
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    {G Cb U : ℝ} (hG : 0 ≤ G) (hCb : 0 ≤ Cb)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |Ppr j z w| ≤ G)
    (hcomp : ∀ j z, ∃ w ∈ Cw j z, K j z w ≤ Cb)
    {q t : ℝ} (hq : 2 < q)
    (hthetaU : ∀ j z, populationAtlasTheta P a κ lambda j z ≤ U)
    (j : ℕ) (z : Z) :
    |populationAtlasHaarIntegrand P a κ lambda (stationaryPressureFamily K Ppr Cw j) j q t z| ≤
      Cb * U ^ (1 - 2 / q) + |t| * G * U := by
  have hI : ∀ z w,
      |stationaryPressureFamily K Ppr Cw j z w| ≤ Cb + |w| * G :=
    fun z w ↦ abs_stationaryPressureFamily_le K Ppr Cw hK hP hcomp j z w
  have hqpos : 0 < q := by linarith
  have hbase := abs_populationAtlasHaarIntegrand_le (j := j) (t := t) P a κ lambda
    (stationaryPressureFamily K Ppr Cw j) hCb hG hI hqpos z
  have htheta : 0 ≤ populationAtlasTheta P a κ lambda j z :=
    populationAtlasTheta_nonneg P a κ lambda j z
  have h1 : 0 ≤ 1 - 2 / q := by
    rw [sub_nonneg, div_le_one hqpos]
    linarith
  have hpow : populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) ≤
      U ^ (1 - 2 / q) :=
    Real.rpow_le_rpow htheta (hthetaU j z) h1
  have hthetaU' : populationAtlasTheta P a κ lambda j z ≤ U := hthetaU j z
  have hmul1 : Cb * populationAtlasTheta P a κ lambda j z ^ (1 - 2 / q) ≤
      Cb * U ^ (1 - 2 / q) :=
    mul_le_mul_of_nonneg_left hpow hCb
  have hmul2 : |t| * G * populationAtlasTheta P a κ lambda j z ≤ |t| * G * U := by
    have hcoef : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG
    calc |t| * G * populationAtlasTheta P a κ lambda j z
        = (|t| * G) * populationAtlasTheta P a κ lambda j z := by ring
      _ ≤ (|t| * G) * U := mul_le_mul_of_nonneg_left hthetaU' hcoef
  linarith

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The corrected population-root bound retains the inverse density kinetic
weight. Its probe contribution is independent of density. -/
theorem abs_populationAtlasIntegrand_stationary_le
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    {G Cb : ℝ} (hG : 0 ≤ G) (hCb : 0 ≤ Cb)
    (hK : ∀ j z w, w ∈ Cw j z → 0 ≤ K j z w)
    (hP : ∀ j z w, w ∈ Cw j z → |Ppr j z w| ≤ G)
    (hcomp : ∀ j z, ∃ w ∈ Cw j z, K j z w ≤ Cb)
    {q t : ℝ} (hq : 2 < q) (j : ℕ) (z : Z) :
    |populationAtlasIntegrand P a κ lambda (stationaryPressureFamily K Ppr Cw j) j q t z| ≤
      Cb * populationAtlasTheta P a κ lambda j z ^ (-2 / q) + |t| * G := by
  apply abs_populationAtlasIntegrand_le P a κ lambda
    (stationaryPressureFamily K Ppr Cw j) hCb hG
    (fun z w ↦ abs_stationaryPressureFamily_le K Ppr Cw hK hP hcomp j z w)
    (by linarith) z

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The norm of a single piece integral is bounded by `B` times the piece mass. -/
theorem norm_integral_populationSeedRootPiece_le
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    (I : ℕ → Z → ℝ → ℝ) {q t B : ℝ}
    (hbound : ∀ j (z : Z),
      |populationAtlasIntegrand P a κ lambda (I j) j q t z| ≤ B)
    (j : ℕ) :
    ‖∫ z in populationSeedRootPiece P a κ lambda j,
      populationAtlasIntegrand P a κ lambda (I j) j q t z ∂lambda‖ ≤
      B * (lambda (populationSeedRootPiece P a κ lambda j)).toReal := by
  have h := norm_integral_le_of_norm_le_const
    (μ := lambda.restrict (populationSeedRootPiece P a κ lambda j))
    (f := fun z ↦ populationAtlasIntegrand P a κ lambda (I j) j q t z)
    (C := B) (Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact hbound j z)
  rwa [Measure.real, Measure.restrict_apply_univ] at h

/- The full-atlas summability and pressure bound are supplied by
`summable_populationAtlasIntegral_of_haar_majorant` and
`abs_populationAtlasPressure_le_haar_majorant` in the imported atlas module,
applied to `stationaryPressureFamily K Ppr Cw`. An upper bound on theta alone
only bounds the Haar integrand; it cannot bound the singular root integrand. -/

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Finite weighted-sum approximation of the atlas integrand built from the
stationary pressure family, on a compact original intensity core. -/
theorem PopulationSeedIntensityCore.exists_weighted_sum_approximation_stationary
    [PseudoMetricSpace Z] [PolishSpace Z] [BorelSpace Z]
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    [IsFiniteMeasure lambda]
    {j : ℕ} {H : Set Z} {εcore : ℝ≥0∞}
    (D : PopulationSeedIntensityCore P a κ lambda j H εcore)
    (K : ℕ → Z → W → ℝ) (Ppr : ℕ → Z → W → ℝ) (Cw : ℕ → Z → Set W)
    {q t η : ℝ} (hq : 2 < q) (hη : 0 < η)
    (hcont : ContinuousOn
      (fun p : Z × ℝ ↦ stationaryPressureFamily K Ppr Cw j p.1 p.2)
      (D.roots ×ˢ univ)) :
    ∃ δ > 0, ∀ {centers : Set Z} {U : Z → Set Z}
      (Q : FiniteRootNeighborhoodPartition D.roots centers U),
      (∀ i : Fin Q.count, Q.center i ∈ D.roots) →
      (∀ (i : Fin Q.count) (z : Z), z ∈ Q.cell i →
        dist z (Q.center i) < δ) →
      |∫ z in D.roots,
          populationAtlasIntegrand P a κ lambda (stationaryPressureFamily K Ppr Cw j) j q t z
            ∂lambda -
        ∑ i : Fin Q.count, (lambda (Q.cell i)).toReal *
          populationAtlasIntegrand P a κ lambda (stationaryPressureFamily K Ppr Cw j) j q t
            (Q.center i)|
        ≤ η * (lambda D.roots).toReal :=
  D.exists_weighted_sum_approximation P a κ lambda
    (stationaryPressureFamily K Ppr Cw j) hq hη hcont

end PopulationInstantiation

end OTSelector.Reconstruction
