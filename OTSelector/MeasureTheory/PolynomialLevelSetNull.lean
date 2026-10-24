import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.MvPolynomial

/-!
## Lemma skeleton

* **Conditions:** The coordinate dimension n is any natural number; polynomials have real coefficients in Fin n variables. At the chosen real level h, polynomial evaluation differs from h somewhere; a separate public corollary assumes the polynomial is nonconstant. For products: the two measures are SFinite, the uncurried real-valued function is measurable, and each section is null. For marked polynomial families: joint evaluation is measurable and every mark has some coordinate value whose evaluation differs from h.
* **Objects:** A multivariate polynomial p, its evaluation map and the level set {x | eval x p = h}. A polynomial in one distinguished variable whose coefficients are polynomials in the remaining variables, with its leading coefficient. A measurable family p(a) over an arbitrary marked measure space and the resulting level set in product space.
* **Proof detail:** Subtract the level h, split off one variable, and use induction to make the leading coefficient nonzero almost everywhere. Each remaining nonzero univariate slice has finitely many roots and hence zero Lebesgue measure. Transfer through the finite-product coordinate equivalence and apply the nonnegative product integral formula. Apply the same null-section argument to a fixed polynomial or a jointly measurable polynomial family.

## Mathematical sources

* Boris S. Mityagin, *The Zero Set of a Real Analytic Function*, arXiv:1512.07276v1 (22 December 2015), Proposition 0 on p. 1; proof on pp. 1-3. Published in Mathematical Notes 107 (2020), pp. 529-530..
  https://arxiv.org/pdf/1512.07276#page=1
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144.
  https://measure.axler.net/MIRA.pdf#page=144

**Relationship to the sources:** The polynomial null-level conclusion is a specialization of Mityagin Proposition 0 after subtracting h. This formalization uses an independent algebraic induction rather than that paper's analytic proof. The product statements combine the scalar result with Tonelli, with SFinite generality beyond the cited textbook statement.
-/

/-!
# Level sets of polynomial functions are Lebesgue-null

The differentiability theorem of the paper uses the fact that every level set of
a nonconstant polynomial in finitely many real variables has Lebesgue measure
zero (equation `highd-diffuse-levelsets`).  The proof is by induction on the
number of variables: decompose the polynomial as a polynomial in the last
variable, use Fubini, and apply the one-dimensional finite-root property to the
a.e. nonzero slices.

We prove the slightly sharper statement that the level set of a polynomial
function which is not identically equal to the level value is null.  This covers
both nonconstant polynomials and constant polynomials with a different value,
and avoids a separate treatment of the constant case in the induction.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OTSelector

/-- **Level sets of polynomial functions.**  If a multivariate polynomial with
real coefficients does not take the value `h` identically, then its `h`-level
set has Lebesgue measure zero. -/
theorem volume_setOf_mvPolynomial_eval_eq_zero_aux (n : ℕ) :
    ∀ (p : MvPolynomial (Fin n) ℝ) (h : ℝ),
      (∃ x : Fin n → ℝ, MvPolynomial.eval x p ≠ h) →
      volume {x : Fin n → ℝ | MvPolynomial.eval x p = h} = 0 := by
  induction n with
  | zero =>
      intro p h hp
      obtain ⟨x0, hx0⟩ := hp
      have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x p = h} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' : x = x0 := funext fun i => i.elim0
        exact hx0 (by rw [← hx']; exact hx)
      rw [hempty, measure_empty]
  | succ n ih =>
      intro p h hp
      classical
      -- Shift the level value to zero.
      set q : MvPolynomial (Fin (n + 1)) ℝ := p - MvPolynomial.C h with hq
      have hqeval : ∀ x, MvPolynomial.eval x q = MvPolynomial.eval x p - h := by
        intro x
        simp [hq]
      have hq0 : q ≠ 0 := by
        intro hzero
        obtain ⟨x, hx⟩ := hp
        have h0 : MvPolynomial.eval x q = 0 := by rw [hzero]; simp
        rw [hqeval x] at h0
        exact hx (sub_eq_zero.mp h0)
      have hset : {x : Fin (n + 1) → ℝ | MvPolynomial.eval x p = h}
          = {x | MvPolynomial.eval x q = 0} := by
        ext x
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hqeval x, sub_eq_zero]
      rw [hset]
      -- Split off the last variable.
      set P : Polynomial (MvPolynomial (Fin n) ℝ) := MvPolynomial.finSuccEquiv ℝ n q
        with hPdef
      have hP0 : P ≠ 0 := by
        intro hzero
        apply hq0
        have hsym : (MvPolynomial.finSuccEquiv ℝ n).symm P = q := by simp [hPdef]
        rw [hzero] at hsym
        simpa using hsym.symm
      -- The leading coefficient controls the slices.
      set r : MvPolynomial (Fin n) ℝ := P.leadingCoeff with hrdef
      have hr0 : r ≠ 0 := by
        intro hzero
        exact hP0 (Polynomial.leadingCoeff_eq_zero.mp (by simpa [hrdef] using hzero))
      have hrex : ∃ s : Fin n → ℝ, MvPolynomial.eval s r ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hr0 (MvPolynomial.funext fun s => by simpa using hcon s)
      -- The a.e. nonvanishing of the leading coefficient holds by induction.
      obtain ⟨s0, hs0⟩ := hrex
      have hrnull : volume {s : Fin n → ℝ | MvPolynomial.eval s r = 0} = 0 :=
        ih r 0 ⟨s0, hs0⟩
      -- Transfer the level set to the product `ℝ × (Fin n → ℝ)`.
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hmp : MeasurePreserving e volume (volume.prod volume) :=
        volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      set S : Set (Fin (n + 1) → ℝ) := {x | MvPolynomial.eval x q = 0} with hSdef
      have hSmeas : MeasurableSet S :=
        (isClosed_eq (MvPolynomial.continuous_eval q) continuous_const).measurableSet
      set T : Set (ℝ × (Fin n → ℝ)) := e.symm ⁻¹' S with hTdef
      have hTmeas : MeasurableSet T := hSmeas.preimage e.symm.measurable
      have hvol : volume S = volume.prod volume T := by
        rw [← hmp.map_eq]
        rw [Measure.map_apply hmp.measurable hTmeas]
        congr 1
        ext x
        simp [T]
      -- Slice over the tail variables; a.e. slice is a nonzero univariate
      -- polynomial, so its root set is finite.
      have hfiber : ∀ s : Fin n → ℝ,
          (fun a : ℝ => (a, s)) ⁻¹' T =
            {a : ℝ | Polynomial.eval a (P.map (MvPolynomial.eval s)) = 0} := by
        intro s
        ext a
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, T, S, e,
          MeasurableEquiv.piFinSuccAbove_symm_apply]
        have hcons : (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) 0) (a, s) =
            Fin.cons a s := by
          rw [Fin.insertNthEquiv_zero]
          ext i
          exact Fin.consEquiv_apply (fun _ : Fin (n + 1) => ℝ) (a, s) i
        rw [hcons, MvPolynomial.eval_eq_eval_mv_eval' s a q, ← hPdef]
      have hae : (fun s : Fin n → ℝ =>
          volume ((fun a : ℝ => (a, s)) ⁻¹' T)) =ᵐ[volume] 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hrnull] with s hs
        have hrs : MvPolynomial.eval s r ≠ 0 := by simpa using hs
        have hlead : (P.map (MvPolynomial.eval s)).leadingCoeff ≠ 0 := by
          rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (MvPolynomial.eval s)
            (by simpa [hrdef] using hrs)]
          simpa [hrdef] using hrs
        have hmap0 : P.map (MvPolynomial.eval s) ≠ 0 := by
          intro hzero
          rw [hzero] at hlead
          simp at hlead
        have hfin : Set.Finite
            {a : ℝ | Polynomial.eval a (P.map (MvPolynomial.eval s)) = 0} := by
          simpa only [Polynomial.IsRoot.def] using
            Polynomial.finite_setOfPred_isRoot hmap0
        rw [hfiber s]
        exact hfin.measure_zero volume
      have hTnull : (volume.prod volume) T = 0 := by
        rw [Measure.prod_apply_symm hTmeas]
        rw [lintegral_eq_zero_iff (measurable_measure_prodMk_right hTmeas)]
        exact hae
      rw [hvol, hTnull]

/-- **Level sets of nonconstant polynomials.**  Every level set of a
nonconstant multivariate polynomial with real coefficients is Lebesgue-null.
This is equation `highd-diffuse-levelsets` of the paper. -/
theorem volume_setOf_mvPolynomial_eval_eq_of_not_isConstant
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (h : ℝ)
    (hp : p ∉ Set.range (MvPolynomial.C : ℝ → MvPolynomial (Fin n) ℝ)) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = h} = 0 := by
  apply volume_setOf_mvPolynomial_eval_eq_zero_aux n p h
  by_contra hcon
  push Not at hcon
  have hpC : p = MvPolynomial.C h := by
    apply MvPolynomial.funext
    intro x
    simpa using hcon x
  exact hp ⟨h, hpC.symm⟩

/-- **Null sections give a null product set.**  If every section `{x | f x a = h}`
over the second variable is `μ`-null, then the whole level set is null for the
product measure.  This is the Fubini step taking the pointwise level-set result
to the product law `dx α(da)` of the paper. -/
theorem measure_prod_setOf_eq_zero_of_forall_section
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (μ : Measure X) [SFinite μ] (α : Measure A) [SFinite α]
    (f : X → A → ℝ) (h : ℝ)
    (hm : Measurable (Function.uncurry f))
    (hsec : ∀ a, μ {x | f x a = h} = 0) :
    μ.prod α {z : X × A | f z.1 z.2 = h} = 0 := by
  have hmeas : MeasurableSet {z : X × A | f z.1 z.2 = h} :=
    hm (measurableSet_singleton h)
  rw [Measure.prod_apply_symm hmeas]
  rw [lintegral_eq_zero_iff (measurable_measure_prodMk_right hmeas)]
  filter_upwards with a
  exact hsec a

/-- **Product level sets, constant polynomial.**  For a fixed polynomial the
product law `volume × α` of the level set is null, for any mark law `α`. -/
theorem volume_prod_setOf_mvPolynomial_eval_eq_zero_of_const
    {n : ℕ} {A : Type*} [MeasurableSpace A] (α : Measure A) [SFinite α]
    (p : MvPolynomial (Fin n) ℝ) (h : ℝ)
    (hp : ∃ x : Fin n → ℝ, MvPolynomial.eval x p ≠ h) :
    (volume.prod α) {z : (Fin n → ℝ) × A | MvPolynomial.eval z.1 p = h} = 0 := by
  have hm : Measurable fun z : (Fin n → ℝ) × A => MvPolynomial.eval z.1 p :=
    (MvPolynomial.continuous_eval p).measurable.comp measurable_fst
  exact measure_prod_setOf_eq_zero_of_forall_section volume α
    (fun x _ => MvPolynomial.eval x p) h hm
    (fun _ => volume_setOf_mvPolynomial_eval_eq_zero_aux n p h hp)

/-- **Product level sets, measurable polynomial family.**  If the polynomial
may depend measurably on the mark and each mark slice is not identically equal
to the level value, then the `volume × α` level set is null.  This is equation
`highd-diffuse-levelsets` in its product-law form. -/
theorem volume_prod_setOf_mvPolynomial_eval_eq_zero
    {n : ℕ} {A : Type*} [MeasurableSpace A] (α : Measure A) [SFinite α]
    (p : A → MvPolynomial (Fin n) ℝ) (h : ℝ)
    (hm : Measurable fun z : (Fin n → ℝ) × A => MvPolynomial.eval z.1 (p z.2))
    (hp : ∀ a, ∃ x : Fin n → ℝ, MvPolynomial.eval x (p a) ≠ h) :
    (volume.prod α) {z : (Fin n → ℝ) × A | MvPolynomial.eval z.1 (p z.2) = h} = 0 := by
  exact measure_prod_setOf_eq_zero_of_forall_section volume α
    (fun x a => MvPolynomial.eval x (p a)) h hm
    (fun a => volume_setOf_mvPolynomial_eval_eq_zero_aux n (p a) h (hp a))

end OTSelector
