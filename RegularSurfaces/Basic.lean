import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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



/-! ## The unit sphere `S² ⊆ ℝ³` is a regular surface

We exhibit, for each `p ∈ S²`, a `RegularSurface.Parametrization` using one of
the six "hemisphere charts" obtained by projecting onto the two coordinates
orthogonal to whichever axis-component of `p` is non-zero. -/

namespace RegularSurface

open Real Set

/-- The unit `2`-sphere `S² = {p ∈ ℝ³ : p₀² + p₁² + p₂² = 1}`. -/
def unitSphere : Set (Fin 3 → ℝ) := {p | p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1}

/-- The open unit disk in `ℝ²`. -/
def openUnitDisk : Set (Fin 2 → ℝ) := {uv | uv 0 ^ 2 + uv 1 ^ 2 < 1}

lemma isOpen_openUnitDisk : IsOpen openUnitDisk := by
  refine isOpen_lt (Continuous.add ?_ ?_) continuous_const
  · exact (continuous_apply 0).pow 2
  · exact (continuous_apply 1).pow 2

/-- The complement of `1 - u² - v²` is positive precisely on the open unit disk. -/
lemma one_sub_sq_pos_of_mem_openUnitDisk {uv : Fin 2 → ℝ} (h : uv ∈ openUnitDisk) :
    0 < 1 - uv 0 ^ 2 - uv 1 ^ 2 := by
  have : uv 0 ^ 2 + uv 1 ^ 2 < 1 := h
  linarith

/-- The upper-hemisphere chart `(u, v) ↦ (u, v, √(1 - u² - v²))`. -/
noncomputable def upperHemiChart (uv : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![uv 0, uv 1, Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2)]

/-- The open upper-half space `{q | q 2 > 0}` in `ℝ³`. -/
def upperHalf : Set (Fin 3 → ℝ) := {q | 0 < q 2}

lemma isOpen_upperHalf : IsOpen upperHalf :=
  isOpen_lt continuous_const (continuous_apply 2)

@[simp] lemma upperHemiChart_zero (uv : Fin 2 → ℝ) : upperHemiChart uv 0 = uv 0 := rfl
@[simp] lemma upperHemiChart_one (uv : Fin 2 → ℝ) : upperHemiChart uv 1 = uv 1 := rfl
@[simp] lemma upperHemiChart_two (uv : Fin 2 → ℝ) :
    upperHemiChart uv 2 = Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2) := rfl

lemma mapsTo_upperHemiChart :
    MapsTo upperHemiChart openUnitDisk (upperHalf ∩ unitSphere) := by
  intro uv huv
  have hpos : 0 < 1 - uv 0 ^ 2 - uv 1 ^ 2 := one_sub_sq_pos_of_mem_openUnitDisk huv
  refine ⟨?_, ?_⟩
  · show 0 < upperHemiChart uv 2
    simp only [upperHemiChart_two]
    exact Real.sqrt_pos.mpr hpos
  · show upperHemiChart uv 0 ^ 2 + upperHemiChart uv 1 ^ 2 + upperHemiChart uv 2 ^ 2 = 1
    simp only [upperHemiChart_zero, upperHemiChart_one, upperHemiChart_two,
      Real.sq_sqrt hpos.le]
    ring

lemma surjOn_upperHemiChart :
    SurjOn upperHemiChart openUnitDisk (upperHalf ∩ unitSphere) := by
  rintro q ⟨hq_pos, hq_sphere⟩
  refine ⟨![q 0, q 1], ?_, ?_⟩
  · show ![q 0, q 1] 0 ^ 2 + ![q 0, q 1] 1 ^ 2 < 1
    have hq2_sq_pos : 0 < q 2 ^ 2 := pow_pos hq_pos 2
    have hs : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 = 1 := hq_sphere
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · show upperHemiChart ![q 0, q 1] = q
    funext k
    fin_cases k
    · simp
    · simp
    · have hsum : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 = 1 := hq_sphere
      have heq : 1 - q 0 ^ 2 - q 1 ^ 2 = q 2 ^ 2 := by linarith
      show Real.sqrt (1 - ![q 0, q 1] 0 ^ 2 - ![q 0, q 1] 1 ^ 2) = q 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [heq, Real.sqrt_sq hq_pos.le]

lemma contDiffOn_upperHemiChart :
    ContDiffOn ℝ ⊤ upperHemiChart openUnitDisk := by
  apply contDiffOn_pi'
  intro i
  fin_cases i
  · show ContDiffOn ℝ ⊤ (fun uv : Fin 2 → ℝ => upperHemiChart uv 0) openUnitDisk
    simp only [upperHemiChart_zero]
    fun_prop
  · show ContDiffOn ℝ ⊤ (fun uv : Fin 2 → ℝ => upperHemiChart uv 1) openUnitDisk
    simp only [upperHemiChart_one]
    fun_prop
  · show ContDiffOn ℝ ⊤ (fun uv : Fin 2 → ℝ => upperHemiChart uv 2) openUnitDisk
    simp only [upperHemiChart_two]
    intro uv huv
    have hne : 1 - uv 0 ^ 2 - uv 1 ^ 2 ≠ 0 :=
      (one_sub_sq_pos_of_mem_openUnitDisk huv).ne'
    have hsqrt : ContDiffAt ℝ ⊤ Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2) :=
      Real.contDiffAt_sqrt hne
    have hpoly : ContDiffAt ℝ ⊤ (fun w : Fin 2 → ℝ => 1 - w 0 ^ 2 - w 1 ^ 2) uv := by
      fun_prop
    exact (hsqrt.comp uv hpoly).contDiffWithinAt

end RegularSurface

example : RegularSurface RegularSurface.unitSphere := by
  sorry
