import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Atoms
import Mathlib.Probability.IdentDistrib
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Sequences
import OTSelector.MeasureTheory.HaarNullNormalDirections
import OTSelector.Probability.InvariantEventSigma
import OTSelector.Probability.StationaryL2Foundation

/-!
Conditions: The displayed commuting real linear isometric representation on a real Hilbert space; the orientation conclusions use a finite-dimensional inner-product translation space, dimension>2, Haar measure and a countable centered observable family.

Objects: Closed translation-fixed subspaces and commuting projections, orthogonal hyperplane-invariant components, countably many nonzero projections and an orthonormal orientation avoiding all of them; Koopman specialization for stationary L2 observations.

Proof detail: Projection uniqueness gives commutation; distinct hyperplanes span the full translation space, so centered projected components are orthogonal. A finite Bessel bound makes the nonzero family countable, and the proved Haar-null orientation argument avoids its hyperplanes; conditional zero expectation supplies centering in the Koopman case.

References: Sheldon Axler: Section 8B, Definition 8.34, p. 227; Theorem 8.37 and proof, p. 228; Sheldon Axler: Section 8C, Theorem 8.57 (Bessel inequality) and proof, pp. 241–242.
Relation: A locally combined invariant-projection/orientation argument. The cited Hilbert results supply projection uniqueness and Bessel estimates, not a verbatim spectral theorem; no spectral measure or separability of the Hilbert space is assumed.
-/


/-! Direct Hilbert-space orientation of invariant hyperplane components.
For a commuting isometric representation of a real vector space, projection
onto the invariants of any spatial subspace commutes with every translation.
A centered observable has orthogonal invariant projections for distinct
hyperplanes, and only countably many of those projections can be nonzero.
No spectral measure or separability hypothesis enters this argument. -/

open Set Function Filter Submodule
open scoped InnerProductSpace Topology BigOperators
noncomputable section

namespace OTSelector.Probability

variable {F H : Type*} [AddCommGroup F] [Module ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The joint fixed subspace of all translations in a specified spatial
linear subspace. Its carrier keeps the whole translation family. -/
def translationFixedSubspace (U : F → H ≃ₗᵢ[ℝ] H) (A : Submodule ℝ F) :
    Submodule ℝ H where
  carrier := {x | ∀ a ∈ A, U a x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy a ha
    simp only [map_add, hx a ha, hy a ha]
  smul_mem' := by
    intro c x hx a ha
    simp only [map_smul, hx a ha]

omit [CompleteSpace H] in
/-- Joint invariants form a closed Hilbert subspace even for an uncountable
spatial family of translations. -/
theorem isClosed_translationFixedSubspace
    (U : F → H ≃ₗᵢ[ℝ] H) (A : Submodule ℝ F) :
    IsClosed (translationFixedSubspace U A : Set H) := by
  change IsClosed {x | ∀ a ∈ A, U a x = x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun _ ↦
    isClosed_eq (U a).continuous continuous_id

instance translationFixedSubspace_completeSpace
    (U : F → H ≃ₗᵢ[ℝ] H) (A : Submodule ℝ F) :
    CompleteSpace (translationFixedSubspace U A) :=
  (isClosed_translationFixedSubspace U A).completeSpace_coe

omit [CompleteSpace H] in
/-- Orthogonal projection components of one vector have countable support.
Only the Bessel bound for this particular vector is used; the ambient Hilbert
space need not be separable. -/
theorem countable_nonzero_of_pairwise_orthogonal_projections
    {ι : Type*} (x : H) (p : ι → H)
    (horth : Pairwise (fun i j ↦ ⟪p i, p j⟫_ℝ = 0))
    (halign : ∀ i, ⟪x, p i⟫_ℝ = ‖p i‖ ^ 2) :
    {i | p i ≠ 0}.Countable := by
  classical
  have hnorm (s : Finset ι) : ‖∑ i ∈ s, p i‖ ^ 2 = ∑ i ∈ s, ‖p i‖ ^ 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, norm_add_sq_real, hs]
      have hcross : ⟪p i, ∑ j ∈ s, p j⟫_ℝ = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth (fun h ↦ hi (h ▸ hj))
      rw [hcross]
      ring
  have hbound (s : Finset ι) : ∑ i ∈ s, ‖p i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have hsum : ⟪x, ∑ i ∈ s, p i⟫_ℝ = ∑ i ∈ s, ‖p i‖ ^ 2 := by
      simp_rw [inner_sum, halign]
    have hnonneg : 0 ≤ ‖x - ∑ i ∈ s, p i‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, hnorm, hsum] at hnonneg
    linarith
  have hsum : Summable (fun i ↦ ‖p i‖ ^ 2) :=
    summable_of_sum_le (fun _ ↦ sq_nonneg _) hbound
  simpa only [Function.support, ne_eq, sq_eq_zero_iff, norm_eq_zero] using
    hsum.countable_support

variable (U : F → H ≃ₗᵢ[ℝ] H)
  (hadd : ∀ a b x, U a (U b x) = U (a + b) x)
include hadd

omit [Module ℝ F] [CompleteSpace H] in
private theorem translation_commute (a b : F) (x : H) :
    U a (U b x) = U b (U a x) := by
  rw [hadd, hadd, add_comm a b]

omit [CompleteSpace H] in
/-- Every spatial translation maps each subgroup-invariant subspace onto
itself. Surjectivity follows from the actual isometry equivalence. -/
theorem map_translationFixedSubspace (A : Submodule ℝ F) (b : F) :
    (translationFixedSubspace U A).map (U b).toLinearEquiv.toLinearMap =
      translationFixedSubspace U A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ a ha
    change U a (U b y) = U b y
    rw [translation_commute U hadd, hy a ha]
  · intro hx
    refine ⟨(U b).symm x, ?_, (U b).apply_symm_apply x⟩
    intro a ha
    apply (U b).injective
    rw [← translation_commute U hadd, (U b).apply_symm_apply, hx a ha]

/-- Projection onto the invariants of a spatial subspace commutes with EVERY
translation, using the abelian representation law. -/
theorem translation_starProjection_commute
    (A : Submodule ℝ F) (b : F) (x : H) :
    U b ((translationFixedSubspace U A).starProjection x) =
      (translationFixedSubspace U A).starProjection (U b x) := by
  have h := Submodule.starProjection_map_apply (U b)
    (translationFixedSubspace U A) (U b x)
  simpa only [map_translationFixedSubspace U hadd, (U b).symm_apply_apply] using h.symm

/-- Successive invariant projections lie in both invariant subspaces. -/
theorem starProjection_mem_translationFixedSubspace_inf
    (A B : Submodule ℝ F) (x : H) :
    (translationFixedSubspace U A).starProjection
      ((translationFixedSubspace U B).starProjection x) ∈
        translationFixedSubspace U A ⊓ translationFixedSubspace U B := by
  refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  intro b hb
  rw [translation_starProjection_commute U hadd]
  congr 1
  exact (Submodule.starProjection_apply_mem (translationFixedSubspace U B) x) b hb

omit [CompleteSpace H] in
/-- Invariance on two spatial subspaces is invariance on their linear sum. -/
theorem translationFixedSubspace_inf_eq_sup (A B : Submodule ℝ F) :
    translationFixedSubspace U A ⊓ translationFixedSubspace U B =
      translationFixedSubspace U (A ⊔ B) := by
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩ v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [← hadd, hxB b hb, hxA a ha]
  · intro hx
    exact ⟨fun a ha ↦ hx a (Submodule.mem_sup_left ha),
      fun b hb ↦ hx b (Submodule.mem_sup_right hb)⟩

/-- For a centered observable, projections onto two invariant subspaces whose
spatial sum is the whole parameter space have zero product. -/
theorem starProjection_translationFixedSubspace_comp_eq_zero
    (A B : Submodule ℝ F) (hAB : A ⊔ B = ⊤) (x : H)
    (hx : ∀ y ∈ translationFixedSubspace U ⊤, ⟪x, y⟫_ℝ = 0) :
    (translationFixedSubspace U A).starProjection
      ((translationFixedSubspace U B).starProjection x) = 0 := by
  let y := (translationFixedSubspace U A).starProjection
    ((translationFixedSubspace U B).starProjection x)
  have hy := starProjection_mem_translationFixedSubspace_inf U hadd A B x
  have hyA : y ∈ translationFixedSubspace U A := hy.1
  have hyB : y ∈ translationFixedSubspace U B := hy.2
  have hyall : y ∈ translationFixedSubspace U ⊤ := by
    rw [← hAB, ← translationFixedSubspace_inf_eq_sup U hadd]
    exact hy
  have horthA := Submodule.starProjection_inner_eq_zero
    (K := translationFixedSubspace U A)
    ((translationFixedSubspace U B).starProjection x) y hyA
  have horthB := Submodule.starProjection_inner_eq_zero
    (K := translationFixedSubspace U B) x y hyB
  have hxy := hx y hyall
  rw [inner_sub_left] at horthA horthB
  have hyy : ⟪y, y⟫_ℝ = 0 := by
    dsimp only [y] at *
    linarith
  exact inner_self_eq_zero.1 hyy

/-- Distinct hyperplane-invariant components of one centered observable are
orthogonal. The full joint invariant component is removed only once. -/
theorem inner_starProjection_translationFixedSubspace_eq_zero
    (A B : Submodule ℝ F) (hAB : A ⊔ B = ⊤) (x : H)
    (hx : ∀ y ∈ translationFixedSubspace U ⊤, ⟪x, y⟫_ℝ = 0) :
    ⟪(translationFixedSubspace U A).starProjection x,
      (translationFixedSubspace U B).starProjection x⟫_ℝ = 0 := by
  rw [Submodule.inner_starProjection_left_eq_right,
    starProjection_translationFixedSubspace_comp_eq_zero U hadd A B hAB x hx]
  exact inner_zero_right _

/-- For ONE centered observable, only countably many spatial hyperplanes
can have a nonzero invariant component. Different maximal proper spatial
subspaces span the whole parameter space, so their projected components are
pairwise orthogonal. No separability of the ambient Hilbert space is required. -/
theorem countable_nonzero_hyperplane_invariant_projections
    (x : H)
    (hx : ∀ y ∈ translationFixedSubspace U ⊤, ⟪x, y⟫_ℝ = 0) :
    {A : {A : Submodule ℝ F // IsCoatom A} |
      (translationFixedSubspace U A.1).starProjection x ≠ 0}.Countable := by
  apply countable_nonzero_of_pairwise_orthogonal_projections x
    (fun A : {A : Submodule ℝ F // IsCoatom A} ↦
      (translationFixedSubspace U A.1).starProjection x)
  · intro A B hAB
    apply inner_starProjection_translationFixedSubspace_eq_zero U hadd A.1 B.1
      (A.2.sup_eq_top_of_ne B.2 (fun h ↦ hAB (Subtype.ext h))) x hx
  · intro A
    have h := Submodule.starProjection_inner_eq_zero
      (K := translationFixedSubspace U A.1) x
      ((translationFixedSubspace U A.1).starProjection x)
      (Submodule.starProjection_apply_mem _ _)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    exact sub_eq_zero.1 h

/-- A countable family of centered currents has one countable set of bad
hyperplanes, so a common orientation can be chosen for the whole family. -/
theorem countable_nonzero_hyperplane_invariant_projections_family
    {ι : Type*} [Countable ι] (x : ι → H)
    (hx : ∀ i y, y ∈ translationFixedSubspace U ⊤ → ⟪x i, y⟫_ℝ = 0) :
    {A : {A : Submodule ℝ F // IsCoatom A} |
      ∃ i, (translationFixedSubspace U A.1).starProjection (x i) ≠ 0}.Countable := by
  simpa only [Set.iUnion_ofPred] using Set.countable_iUnion
    (fun i ↦ countable_nonzero_hyperplane_invariant_projections U hadd (x i) (hx i))

omit hadd

section SpatialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A maximal proper spatial subspace is the orthogonal hyperplane of an
actual unit normal, selected from its nontrivial orthogonal complement. -/
theorem exists_unit_normal_of_isCoatom
    (A : Submodule ℝ E) (hA : IsCoatom A) :
    ∃ n : Metric.sphere (0 : E) 1, A = (ℝ ∙ (n : E))ᗮ := by
  have horth : Aᗮ ≠ ⊥ := by
    intro h
    exact hA.ne_top ((Submodule.orthogonal_eq_bot_iff).1 h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  let n : E := ‖v‖⁻¹ • v
  have hnorm : ‖n‖ = 1 := by
    simpa only [n, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm] using
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
  have hnorth : n ∈ Aᗮ := Aᗮ.smul_mem _ hv
  have hsub : A ≤ (ℝ ∙ n)ᗮ := by
    intro a ha
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hnorth a ha
  have hproper : (ℝ ∙ n)ᗮ ≠ ⊤ := by
    intro h
    have hn : n ∈ (ℝ ∙ n)ᗮ := by rw [h]; trivial
    have hzero := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hn
    rw [real_inner_self_eq_norm_sq, hnorm] at hzero
    norm_num at hzero
  exact ⟨⟨n, by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩,
    ((hA.le_iff_eq hproper).1 hsub).symm⟩

omit [FiniteDimensional ℝ E] in
/-- The hyperplane perpendicular to a genuine unit normal is maximal proper. -/
theorem isCoatom_orthogonal_span_unit (n : Metric.sphere (0 : E) 1) :
    IsCoatom (ℝ ∙ (n : E))ᗮ := by
  have hn : ‖(n : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using n.property
  have heq : (ℝ ∙ (n : E))ᗮ = LinearMap.ker (innerSL ℝ (n : E)).toLinearMap := by
    ext x
    exact Submodule.mem_orthogonal_singleton_iff_inner_right
  rw [heq]
  apply LinearMap.isCoatom_ker_of_surjective
  intro r
  refine ⟨r • (n : E), ?_⟩
  change ⟪(n : E), r • (n : E)⟫_ℝ = r
  rw [inner_smul_right, real_inner_self_eq_norm_sq, hn]
  ring

/-- A countable family of centered observables has one actual orthonormal
spatial frame whose EVERY face-tangent hyperplane has zero invariant
projection for every observable. The auxiliary Dirac measures encode only
the countable bad hyperplanes; no spectral measure is assumed or constructed. -/
theorem exists_orthonormalBasis_hyperplane_invariant_projections_eq_zero
    [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Countable ι]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ E)
    (U : E → H ≃ₗᵢ[ℝ] H) (hadd : ∀ a b x, U a (U b x) = U (a + b) x)
    (x : ι → H)
    (hx : ∀ j y, y ∈ translationFixedSubspace U ⊤ → ⟪x j, y⟫_ℝ = 0) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E, ∀ i j,
      (translationFixedSubspace U (ℝ ∙ b i)ᗮ).starProjection (x j) = 0 := by
  classical
  let Bad : Set {A : Submodule ℝ E // IsCoatom A} :=
    {A | ∃ j, (translationFixedSubspace U A.1).starProjection (x j) ≠ 0}
  have hBad : Bad.Countable :=
    countable_nonzero_hyperplane_invariant_projections_family U hadd x hx
  let _ : Countable Bad := hBad.to_subtype
  choose n hn using fun A : Bad ↦ exists_unit_normal_of_isCoatom A.1.1 A.1.2
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_all_measure_normalLines_eq_zero μ hdim
    (fun A : Bad ↦ MeasureTheory.Measure.dirac (n A : E))
  refine ⟨b, fun i j ↦ ?_⟩
  by_contra hbad
  let ni : Metric.sphere (0 : E) 1 :=
    ⟨b i, by simpa only [Metric.mem_sphere, dist_zero_right] using b.norm_eq_one i⟩
  let A : {A : Submodule ℝ E // IsCoatom A} :=
    ⟨(ℝ ∙ b i)ᗮ, isCoatom_orthogonal_span_unit ni⟩
  let a : Bad := ⟨A, ⟨j, hbad⟩⟩
  have horth : (ℝ ∙ (n a : E))ᗮ = (ℝ ∙ b i)ᗮ := (hn a).symm
  have hspan : ℝ ∙ (n a : E) = ℝ ∙ b i := by
    simpa only [Submodule.orthogonal_orthogonal] using
      congrArg (fun W : Submodule ℝ E ↦ Wᗮ) horth
  have hmem : (n a : E) ∈ ((ℝ ∙ b i : Set E) \ {0}) := by
    refine ⟨?_, ?_⟩
    · rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    · have hnunit : ‖(n a : E)‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using (n a).property
      intro hz
      have hz' : (n a : E) = 0 := Set.mem_singleton_iff.1 hz
      have hz'' : (0 : ℝ) = 1 := by simpa only [hz', norm_zero] using hnunit
      exact zero_ne_one hz''
  have hone := MeasureTheory.Measure.dirac_apply_of_mem hmem
  exact zero_ne_one ((hb i a).symm.trans hone)

end SpatialGeometry

section Koopman

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : MeasureTheory.Measure Ω) (T : F → Ω → Ω)
  (hT : ∀ a, MeasureTheory.MeasurePreserving (T a) P P)
  (hzero : T 0 = id) (haddT : ∀ a b ω, T a (T b ω) = T (a + b) ω)

/-- The actual measure-preserving translation action gives a genuine
surjective L² linear isometry, with inverse given by the opposite translation. -/
def stationaryKoopman (a : F) :
    MeasureTheory.Lp ℝ 2 P ≃ₗᵢ[ℝ] MeasureTheory.Lp ℝ 2 P where
  toLinearEquiv :=
    { MeasureTheory.Lp.compMeasurePreservingₗ ℝ (T a) (hT a) with
      invFun := MeasureTheory.Lp.compMeasurePreserving (T (-a)) (hT (-a))
      left_inv := by
        intro f
        change MeasureTheory.Lp.compMeasurePreserving (T (-a)) (hT (-a))
          (MeasureTheory.Lp.compMeasurePreserving (T a) (hT a) f) = f
        rw [compMeasurePreserving_add P T hT haddT, neg_add_cancel]
        simpa only [hzero] using MeasureTheory.Lp.compMeasurePreserving_id_apply f
      right_inv := by
        intro f
        change MeasureTheory.Lp.compMeasurePreserving (T a) (hT a)
          (MeasureTheory.Lp.compMeasurePreserving (T (-a)) (hT (-a)) f) = f
        rw [compMeasurePreserving_add P T hT haddT, add_neg_cancel]
        simpa only [hzero] using MeasureTheory.Lp.compMeasurePreserving_id_apply f }
  norm_map' := fun f ↦ MeasureTheory.Lp.norm_compMeasurePreserving f (hT a)

omit [Module ℝ F] in
/-- The genuine Koopman isometries retain the original exact additive cocycle. -/
theorem stationaryKoopman_add (a b : F) (f : MeasureTheory.Lp ℝ 2 P) :
    stationaryKoopman P T hT hzero haddT a
      (stationaryKoopman P T hT hzero haddT b f) =
        stationaryKoopman P T hT hzero haddT (a + b) f := by
  exact compMeasurePreserving_add P T hT haddT f a b

end Koopman

section ActualL2Orientation

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

/-- Countably many genuine stationary centered L² observables admit one
actual common frame with zero face-tangent invariant components. The input is
the original law, its actual translations, and its actual conditional means;
no unitary representation or frequency measure must be supplied separately. -/
theorem exists_orthonormalBasis_koopman_hyperplane_projections_eq_zero
    {ι : Type*} [Countable ι]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ E)
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure P]
    (T : E → Ω → Ω) (hT : ∀ a, MeasureTheory.MeasurePreserving (T a) P P)
    (hzero : T 0 = id) (haddT : ∀ a b ω, T a (T b ω) = T (a + b) ω)
    (f : ι → MeasureTheory.Lp ℝ 2 P)
    (hf : ∀ j, MeasureTheory.condExp (aeInvariantEventSigma P T) P (f j) =ᵐ[P]
      fun _ ↦ 0) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E, ∀ i j,
      (translationFixedSubspace (stationaryKoopman P T hT hzero haddT)
        (ℝ ∙ b i)ᗮ).starProjection (f j) = 0 := by
  apply exists_orthonormalBasis_hyperplane_invariant_projections_eq_zero μ hdim
    (stationaryKoopman P T hT hzero haddT)
    (stationaryKoopman_add P T hT hzero haddT) f
  intro j g hg
  apply inner_eq_zero_of_condExp_aeInvariantEventSigma_eq_zero P T hT (f j) g (hf j)
  intro a
  exact hg a (by trivial)

end ActualL2Orientation

end OTSelector.Probability
