import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Homeomorph.Defs

/-!
# Regular surfaces

A subset `S ⊆ ℝ³` is a *regular surface* if, for each `p ∈ S`, there exists an
open neighborhood `V ⊆ ℝ³` of `p` and a map `x : U → V ∩ S` from an open set
`U ⊆ ℝ²` onto `V ∩ S` such that

1. `x` is smooth (differentiable of all orders),
2. `x` is a homeomorphism onto `V ∩ S` (equipped with the subspace topology),
3. for each `q ∈ U`, the differential `dx_q : ℝ² → ℝ³` is injective.

Reference: do Carmo, *Differential Geometry of Curves and Surfaces*, §2.2.
-/

open Set

/-- A *parametrization* of `S ⊆ ℝ³` around `p` is the data appearing in
do Carmo's definition: an open `U ⊆ ℝ²`, an open neighborhood `V` of `p` in
`ℝ³`, and a map `x : ℝ² → ℝ³` satisfying the three conditions of a regular
surface, with image exactly `V ∩ S`. -/
structure RegularSurface.Parametrization (S : Set (Fin 3 → ℝ)) (p : Fin 3 → ℝ) where
  /-- The parameter domain `U ⊆ ℝ²`. -/
  U : Set (Fin 2 → ℝ)
  /-- The ambient neighborhood `V ⊆ ℝ³` of `p`. -/
  V : Set (Fin 3 → ℝ)
  /-- The coordinate map `x : ℝ² → ℝ³`. -/
  x : (Fin 2 → ℝ) → (Fin 3 → ℝ)
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  mem_V : p ∈ V
  /-- `x` maps `U` onto `V ∩ S`. -/
  mapsTo : MapsTo x U (V ∩ S)
  surjOn : SurjOn x U (V ∩ S)
  /-- (1) `x` is smooth on `U`. -/
  contDiffOn : ContDiffOn ℝ ⊤ x U
  /-- (2) `x` restricts to a homeomorphism `U ≃ₜ V ∩ S`. -/
  homeomorph : U ≃ₜ (V ∩ S : Set (Fin 3 → ℝ))
  homeomorph_apply : ∀ q : U, (homeomorph q : Fin 3 → ℝ) = x q
  /-- (3) The differential `dx_q : ℝ² → ℝ³` is injective at every `q ∈ U`. -/
  fderiv_injective : ∀ q ∈ U, Function.Injective (fderiv ℝ x q)

/-- A subset `S ⊆ ℝ³` is a *regular surface* if every point of `S` admits a
parametrization in the sense of do Carmo. -/
def RegularSurface (S : Set (Fin 3 → ℝ)) : Prop :=
  ∀ p ∈ S, Nonempty (RegularSurface.Parametrization S p)

/-- Condition (3) of `RegularSurface.Parametrization` — injectivity of the
differential `dx_q : ℝ² → ℝ³` — is implied by the non-vanishing of one of the
three `2 × 2` Jacobian minors at `q`.

If `x : ℝ² → ℝ³` has components `x¹, x², x³`, the three minors are the
determinants `∂(xⁱ, xʲ)/∂(u, v)` for `i ≠ j`; here we phrase the criterion for
an arbitrary pair of rows `i, j : Fin 3` (do Carmo, §2.2). -/
lemma RegularSurface.fderiv_injective_of_jacobian_ne_zero
    {x : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {q : Fin 2 → ℝ} (i j : Fin 3)
    (h : fderiv ℝ x q (Pi.single 0 1) i * fderiv ℝ x q (Pi.single 1 1) j ≠
         fderiv ℝ x q (Pi.single 0 1) j * fderiv ℝ x q (Pi.single 1 1) i) :
    Function.Injective (fderiv ℝ x q) := by
  have key : ∀ v : Fin 2 → ℝ, fderiv ℝ x q v = 0 → v = 0 := by
    intro v hv
    have hv_decomp :
        v 0 • (Pi.single 0 1 : Fin 2 → ℝ) +
          v 1 • (Pi.single 1 1 : Fin 2 → ℝ) = v := by
      funext k; fin_cases k <;> simp
    have hsum :
        v 0 • fderiv ℝ x q (Pi.single 0 1) +
          v 1 • fderiv ℝ x q (Pi.single 1 1) = 0 := by
      rw [← map_smul, ← map_smul, ← map_add, hv_decomp]; exact hv
    have hi : v 0 * fderiv ℝ x q (Pi.single 0 1) i +
              v 1 * fderiv ℝ x q (Pi.single 1 1) i = 0 := by
      have := congrFun hsum i; simpa using this
    have hj : v 0 * fderiv ℝ x q (Pi.single 0 1) j +
              v 1 * fderiv ℝ x q (Pi.single 1 1) j = 0 := by
      have := congrFun hsum j; simpa using this
    have hdet :
        fderiv ℝ x q (Pi.single 0 1) i * fderiv ℝ x q (Pi.single 1 1) j -
          fderiv ℝ x q (Pi.single 0 1) j * fderiv ℝ x q (Pi.single 1 1) i ≠ 0 :=
      sub_ne_zero.mpr h
    have hv0 : v 0 = 0 := by
      have hprod :
          v 0 *
            (fderiv ℝ x q (Pi.single 0 1) i * fderiv ℝ x q (Pi.single 1 1) j -
              fderiv ℝ x q (Pi.single 0 1) j * fderiv ℝ x q (Pi.single 1 1) i)
            = 0 := by
        linear_combination
          fderiv ℝ x q (Pi.single 1 1) j * hi -
            fderiv ℝ x q (Pi.single 1 1) i * hj
      exact (mul_eq_zero.mp hprod).resolve_right hdet
    have hv1 : v 1 = 0 := by
      have hprod :
          v 1 *
            (fderiv ℝ x q (Pi.single 0 1) i * fderiv ℝ x q (Pi.single 1 1) j -
              fderiv ℝ x q (Pi.single 0 1) j * fderiv ℝ x q (Pi.single 1 1) i)
            = 0 := by
        linear_combination
          fderiv ℝ x q (Pi.single 0 1) i * hj -
            fderiv ℝ x q (Pi.single 0 1) j * hi
      exact (mul_eq_zero.mp hprod).resolve_right hdet
    funext k; fin_cases k
    · exact hv0
    · exact hv1
  intro u v huv
  have hsub : fderiv ℝ x q (u - v) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr huv
  exact sub_eq_zero.mp (key _ hsub)
