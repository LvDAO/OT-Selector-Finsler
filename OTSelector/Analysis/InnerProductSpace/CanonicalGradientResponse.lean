import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Analysis.InnerProductSpace.CanonicalGradientResponse

## Lemma skeleton

* **Conditions:** Complete real Hilbert spaces H,K and an actual linear gradient map; response identities require the supplied norm factorization bound for the potential map.

* **Objects:** The genuine closed gradient range and a canonical bounded linear adjoint response to every input in K.

* **Proof detail:** Take the closure of the gradient range, factor the gradient into it with dense range, continuously extend the bounded potential map to that closure, and take its Hilbert adjoint. Extend a sharp pairing bound from the dense gradients to the closure to bound the response norm.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62): Section 1.4, Theorem 1.4.13, p. 53.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61): Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=63): Section 1.4, Exercise 1.4.15, p. 54.

Source relation (composition): The construction has Mathlib’s totalized extension convention; the stated representation and bounds use hbound. No unsupported boundedness of arbitrary potential maps is claimed.
-/

/-! A canonical continuous linear Hilbert response for an actual dense gradient space. -/
open Set Function
open scoped InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction

section GradientClosure
variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The actual closed Hilbert gradient space is the topological closure of the original
smooth gradients, rather than an assumed dense representation. -/
def originalGradientClosure (grad : V →ₗ[ℝ] H) : Submodule ℝ H :=
  grad.range.topologicalClosure

/-- The original gradient as a map into its genuine closed range. -/
def originalDenseGradient (grad : V →ₗ[ℝ] H) : V →ₗ[ℝ] originalGradientClosure grad where
  toFun v := ⟨grad v, grad.range.le_topologicalClosure ⟨v, rfl⟩⟩
  map_add' v w := Subtype.ext (grad.map_add v w)
  map_smul' c v := Subtype.ext (grad.map_smul c v)

/-- Original gradients are dense in their actual closed range, internally from closure. -/
theorem denseRange_originalDenseGradient (grad : V →ₗ[ℝ] H) :
    DenseRange (originalDenseGradient grad) := by
  change DenseRange (Set.inclusion (subset_closure : Set.range grad ⊆ closure (Set.range grad)) ∘
    Set.rangeFactorization grad)
  exact ((denseRange_inclusion_iff subset_closure).mpr subset_rfl).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

/-- The actual closed gradient space is complete when the original ambient Hilbert space is. -/
theorem completeSpace_originalGradientClosure [CompleteSpace H] (grad : V →ₗ[ℝ] H) :
    CompleteSpace (originalGradientClosure grad) :=
  inferInstanceAs (CompleteSpace grad.range.topologicalClosure)

attribute [instance] completeSpace_originalGradientClosure

end GradientClosure

variable {V H K : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Extend the actual potential map from a dense gradient space, then take its genuine
Hilbert adjoint. This constructs one linear continuous response for every input at once. -/
def originalCanonicalGradientResponse (grad : V →ₗ[ℝ] H) (potential : V →ₗ[ℝ] K) :
    K →L[ℝ] originalGradientClosure grad :=
  (potential.extendOfNorm (originalDenseGradient grad)).adjoint

/-- The canonical response realizes the original potential pairing on every actual test. -/
theorem inner_originalCanonicalGradientResponse_grad
    (grad : V →ₗ[ℝ] H) (potential : V →ₗ[ℝ] K)
    (hbound : ∃ C : ℝ, ∀ v, ‖potential v‖ ≤ C * ‖grad v‖) (f : K) (v : V) :
    ⟪originalCanonicalGradientResponse grad potential f, originalDenseGradient grad v⟫_ℝ =
      ⟪f, potential v⟫_ℝ := by
  rw [originalCanonicalGradientResponse, ContinuousLinearMap.adjoint_inner_left,
    LinearMap.extendOfNorm_eq (denseRange_originalDenseGradient grad) hbound]

/-- A sharper bound on the actual input's test pairings yields that same bound for the
canonical response norm. The global potential extension need not have this sharper norm. -/
theorem norm_originalCanonicalGradientResponse_le
    (grad : V →ₗ[ℝ] H) (potential : V →ₗ[ℝ] K)
    (hbound : ∃ C : ℝ, ∀ v, ‖potential v‖ ≤ C * ‖grad v‖)
    (f : K) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ v, |⟪f, potential v⟫_ℝ| ≤ C * ‖grad v‖) :
    ‖originalCanonicalGradientResponse grad potential f‖ ≤ C := by
  let j := originalCanonicalGradientResponse grad potential f
  have hclosed : IsClosed {z : originalGradientClosure grad | |⟪j, z⟫_ℝ| ≤ C * ‖z‖} :=
    isClosed_le (continuous_const.inner continuous_id).abs (continuous_const.mul continuous_norm)
  have hmem : ∀ y ∈ Set.range (originalDenseGradient grad), |⟪j, y⟫_ℝ| ≤ C * ‖y‖ := by
    rintro y ⟨v, rfl⟩
    rw [show ⟪j, originalDenseGradient grad v⟫_ℝ = ⟪f, potential v⟫_ℝ from
      inner_originalCanonicalGradientResponse_grad grad potential hbound f v]
    exact hpair v
  have hall (z : originalGradientClosure grad) : |⟪j, z⟫_ℝ| ≤ C * ‖z‖ :=
    (denseRange_originalDenseGradient grad).induction hmem hclosed z
  have hh := hall j
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
  change ‖j‖ ≤ C
  nlinarith [norm_nonneg j]

end OTSelector.Reconstruction
