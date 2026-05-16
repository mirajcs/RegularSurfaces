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

/-! ### Generic hemisphere chart

We treat all six hemispheres uniformly by parametrising the chart by an axis
`i : Fin 3` and a sign `s ∈ {-1, +1}`. The chart places `s · √(1 - u² - v²)`
at position `i` and `u, v` at the remaining two positions (in
increasing-index order), via `Fin.insertNth`. -/

/-- The hemisphere chart for axis `i` and sign `s`. -/
noncomputable def axHemiChart (i : Fin 3) (s : ℝ) (uv : Fin 2 → ℝ) : Fin 3 → ℝ :=
  Fin.insertNth i (s * Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2)) uv

@[simp] lemma axHemiChart_apply_same (i : Fin 3) (s : ℝ) (uv : Fin 2 → ℝ) :
    axHemiChart i s uv i = s * Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2) := by
  simp [axHemiChart]

@[simp] lemma axHemiChart_apply_succAbove (i : Fin 3) (s : ℝ) (uv : Fin 2 → ℝ) (j : Fin 2) :
    axHemiChart i s uv (i.succAbove j) = uv j := by
  simp [axHemiChart]

/-- The open half-space `{q | 0 < s · q i}` (for `s = ±1` this is the open
hemisphere `q i > 0` or `q i < 0`, respectively). -/
def axHalf (i : Fin 3) (s : ℝ) : Set (Fin 3 → ℝ) := {q | 0 < s * q i}

lemma isOpen_axHalf (i : Fin 3) (s : ℝ) : IsOpen (axHalf i s) :=
  isOpen_lt continuous_const (continuous_const.mul (continuous_apply i))

/-- For `s² = 1`, the sum of the squared coordinates of the chart's output
equals 1: a direct computation using `Fin.sum_univ_succAbove`. -/
lemma sum_sq_axHemiChart (i : Fin 3) (s : ℝ) {uv : Fin 2 → ℝ}
    (huv : uv ∈ openUnitDisk) :
    axHemiChart i s uv 0 ^ 2 + axHemiChart i s uv 1 ^ 2 + axHemiChart i s uv 2 ^ 2 =
      s ^ 2 * (1 - uv 0 ^ 2 - uv 1 ^ 2) + uv 0 ^ 2 + uv 1 ^ 2 := by
  have hpos : 0 ≤ 1 - uv 0 ^ 2 - uv 1 ^ 2 := (one_sub_sq_pos_of_mem_openUnitDisk huv).le
  rw [show axHemiChart i s uv 0 ^ 2 + axHemiChart i s uv 1 ^ 2 + axHemiChart i s uv 2 ^ 2 =
        ∑ k, (axHemiChart i s uv k) ^ 2 from
      (Fin.sum_univ_three (fun k => (axHemiChart i s uv k) ^ 2)).symm,
      Fin.sum_univ_succAbove (fun k => (axHemiChart i s uv k) ^ 2) i,
      Fin.sum_univ_two]
  simp only [axHemiChart_apply_same, axHemiChart_apply_succAbove]
  rw [mul_pow, Real.sq_sqrt hpos]
  ring

/-- If `s² = 1`, the equation `0 < s * x` forces `s = 1 ∧ 0 < x` or
`s = -1 ∧ x < 0`; in either case `s · √(x²) = x`. -/
lemma sign_mul_sqrt_sq {s x : ℝ} (hs : s ^ 2 = 1) (hsx : 0 < s * x) :
    s * Real.sqrt (x ^ 2) = x := by
  have hcases : s = 1 ∨ s = -1 := by
    have h : (s - 1) * (s + 1) = 0 := by nlinarith [hs]
    rcases mul_eq_zero.mp h with h | h
    · left; linarith
    · right; linarith
  rcases hcases with rfl | rfl
  · rw [one_mul] at hsx
    rw [Real.sqrt_sq hsx.le, one_mul]
  · rw [neg_one_mul, neg_pos] at hsx
    rw [Real.sqrt_sq_eq_abs, abs_of_neg hsx, neg_one_mul, neg_neg]

lemma mapsTo_axHemiChart (i : Fin 3) {s : ℝ} (hs : s ^ 2 = 1) :
    MapsTo (axHemiChart i s) openUnitDisk (axHalf i s ∩ unitSphere) := by
  intro uv huv
  refine ⟨?_, ?_⟩
  · show 0 < s * axHemiChart i s uv i
    rw [axHemiChart_apply_same,
      show s * (s * Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2)) =
          s ^ 2 * Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2) by ring, hs, one_mul]
    exact Real.sqrt_pos.mpr (one_sub_sq_pos_of_mem_openUnitDisk huv)
  · show axHemiChart i s uv 0 ^ 2 + axHemiChart i s uv 1 ^ 2 + axHemiChart i s uv 2 ^ 2 = 1
    rw [sum_sq_axHemiChart i s huv, hs]; ring

/-- The continuous linear projection `ℝ³ → ℝ²` sending `q` to its two
coordinates other than `i` (in increasing-index order). -/
def axProjCLM (i : Fin 3) : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin 2 => ContinuousLinearMap.proj (i.succAbove j))

@[simp] lemma axProjCLM_apply (i : Fin 3) (q : Fin 3 → ℝ) (j : Fin 2) :
    axProjCLM i q j = q (i.succAbove j) := rfl

lemma axProjCLM_axHemiChart (i : Fin 3) (s : ℝ) (uv : Fin 2 → ℝ) :
    axProjCLM i (axHemiChart i s uv) = uv := by
  funext j; simp

lemma surjOn_axHemiChart (i : Fin 3) {s : ℝ} (hs : s ^ 2 = 1) :
    SurjOn (axHemiChart i s) openUnitDisk (axHalf i s ∩ unitSphere) := by
  rintro q ⟨hq_half, hq_sphere⟩
  have hhalf : (0 : ℝ) < s * q i := hq_half
  have hsum : q i ^ 2 + (q (i.succAbove 0) ^ 2 + q (i.succAbove 1) ^ 2) = 1 := by
    have hs1 : ∑ k, q k ^ 2 = 1 := by rw [Fin.sum_univ_three]; exact hq_sphere
    rw [Fin.sum_univ_succAbove (fun k => q k ^ 2) i, Fin.sum_univ_two] at hs1
    exact hs1
  have hqi_ne : q i ≠ 0 := fun h0 => by rw [h0, mul_zero] at hhalf; exact lt_irrefl 0 hhalf
  have hqi_sq_pos : 0 < q i ^ 2 := by positivity
  refine ⟨axProjCLM i q, ?_, ?_⟩
  · show axProjCLM i q 0 ^ 2 + axProjCLM i q 1 ^ 2 < 1
    simp only [axProjCLM_apply]; linarith
  · funext k
    by_cases hk : k = i
    · rw [hk, axHemiChart_apply_same]
      show s * Real.sqrt (1 - axProjCLM i q 0 ^ 2 - axProjCLM i q 1 ^ 2) = q i
      simp only [axProjCLM_apply]
      have hrad : 1 - q (i.succAbove 0) ^ 2 - q (i.succAbove 1) ^ 2 = q i ^ 2 := by linarith
      rw [hrad]; exact sign_mul_sqrt_sq hs hhalf
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      rw [axHemiChart_apply_succAbove]; rfl

lemma contDiffOn_axHemiChart (i : Fin 3) (s : ℝ) :
    ContDiffOn ℝ ⊤ (axHemiChart i s) openUnitDisk := by
  apply contDiffOn_pi'
  intro k
  by_cases hk : k = i
  · rw [hk]
    have h : (fun uv : Fin 2 → ℝ => axHemiChart i s uv i) =
        fun uv => s * Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2) := by
      funext uv; exact axHemiChart_apply_same i s uv
    rw [h]
    intro uv huv
    have hne : 1 - uv 0 ^ 2 - uv 1 ^ 2 ≠ 0 := (one_sub_sq_pos_of_mem_openUnitDisk huv).ne'
    have hsqrt : ContDiffAt ℝ ⊤ Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2) :=
      Real.contDiffAt_sqrt hne
    have hpoly : ContDiffAt ℝ ⊤ (fun w : Fin 2 → ℝ => 1 - w 0 ^ 2 - w 1 ^ 2) uv := by fun_prop
    exact (contDiffAt_const.mul (hsqrt.comp uv hpoly)).contDiffWithinAt
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    have h : (fun uv : Fin 2 → ℝ => axHemiChart i s uv (i.succAbove j)) = (fun uv => uv j) := by
      funext uv; rw [axHemiChart_apply_succAbove]
    rw [h]; fun_prop

lemma continuous_axHemiChart (i : Fin 3) (s : ℝ) : Continuous (axHemiChart i s) := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = i
  · rw [hk]
    have h : (fun uv : Fin 2 → ℝ => axHemiChart i s uv i) =
        fun uv => s * Real.sqrt (1 - uv 0 ^ 2 - uv 1 ^ 2) := by
      funext uv; exact axHemiChart_apply_same i s uv
    rw [h]; exact continuous_const.mul (Real.continuous_sqrt.comp (by fun_prop))
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    have h : (fun uv : Fin 2 → ℝ => axHemiChart i s uv (i.succAbove j)) = fun uv => uv j := by
      funext uv; rw [axHemiChart_apply_succAbove]
    rw [h]; fun_prop

/-- The homeomorphism between the open unit disk and the open hemisphere
`axHalf i s ∩ unitSphere` for `s² = 1`. -/
noncomputable def axHemiHomeomorph (i : Fin 3) {s : ℝ} (hs : s ^ 2 = 1) :
    (openUnitDisk : Set (Fin 2 → ℝ)) ≃ₜ ((axHalf i s ∩ unitSphere) : Set (Fin 3 → ℝ)) where
  toFun uv := ⟨axHemiChart i s uv.val, mapsTo_axHemiChart i hs uv.property⟩
  invFun q := ⟨axProjCLM i q.val, by
    obtain ⟨hq_half, hq_sphere⟩ := q.property
    have hhalf : (0 : ℝ) < s * q.val i := hq_half
    have hsum : q.val i ^ 2 + (q.val (i.succAbove 0) ^ 2 + q.val (i.succAbove 1) ^ 2) = 1 := by
      have hs1 : ∑ k, q.val k ^ 2 = 1 := by rw [Fin.sum_univ_three]; exact hq_sphere
      rw [Fin.sum_univ_succAbove (fun k => q.val k ^ 2) i, Fin.sum_univ_two] at hs1
      exact hs1
    have hqi_ne : q.val i ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hhalf; exact lt_irrefl 0 hhalf
    have hqi_sq_pos : 0 < q.val i ^ 2 := by positivity
    show axProjCLM i q.val 0 ^ 2 + axProjCLM i q.val 1 ^ 2 < 1
    simp only [axProjCLM_apply]; linarith⟩
  left_inv := by
    rintro ⟨uv, _⟩
    apply Subtype.ext
    exact axProjCLM_axHemiChart i s uv
  right_inv := by
    rintro ⟨q, hq_half, hq_sphere⟩
    apply Subtype.ext
    have hhalf : (0 : ℝ) < s * q i := hq_half
    have hsum : q i ^ 2 + (q (i.succAbove 0) ^ 2 + q (i.succAbove 1) ^ 2) = 1 := by
      have hs1 : ∑ k, q k ^ 2 = 1 := by rw [Fin.sum_univ_three]; exact hq_sphere
      rw [Fin.sum_univ_succAbove (fun k => q k ^ 2) i, Fin.sum_univ_two] at hs1
      exact hs1
    show axHemiChart i s (axProjCLM i q) = q
    funext k
    by_cases hk : k = i
    · rw [hk, axHemiChart_apply_same]
      show s * Real.sqrt (1 - axProjCLM i q 0 ^ 2 - axProjCLM i q 1 ^ 2) = q i
      simp only [axProjCLM_apply]
      have hrad : 1 - q (i.succAbove 0) ^ 2 - q (i.succAbove 1) ^ 2 = q i ^ 2 := by linarith
      rw [hrad]; exact sign_mul_sqrt_sq hs hhalf
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      rw [axHemiChart_apply_succAbove]; rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_axHemiChart i s).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (axProjCLM i).continuous.comp continuous_subtype_val

lemma fderiv_injective_axHemiChart (i : Fin 3) (s : ℝ) {q : Fin 2 → ℝ}
    (hq : q ∈ openUnitDisk) : Function.Injective (fderiv ℝ (axHemiChart i s) q) := by
  have hdiff : DifferentiableAt ℝ (axHemiChart i s) q :=
    ((contDiffOn_axHemiChart i s).contDiffAt
      (isOpen_openUnitDisk.mem_nhds hq)).differentiableAt (by decide)
  have hchain : (axProjCLM i).comp (fderiv ℝ (axHemiChart i s) q) =
      ContinuousLinearMap.id ℝ (Fin 2 → ℝ) := by
    have hHFD : HasFDerivAt (fun uv => axProjCLM i (axHemiChart i s uv))
        ((axProjCLM i).comp (fderiv ℝ (axHemiChart i s) q)) q :=
      (axProjCLM i).hasFDerivAt.comp q hdiff.hasFDerivAt
    have hcomp_id : (fun uv => axProjCLM i (axHemiChart i s uv)) = id := by
      funext uv; exact axProjCLM_axHemiChart i s uv
    rw [hcomp_id] at hHFD
    exact hHFD.unique (hasFDerivAt_id q)
  refine Function.LeftInverse.injective
    (f := fderiv ℝ (axHemiChart i s) q) (g := axProjCLM i) ?_
  intro v
  have := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => L v) hchain
  simpa using this

/-- The hemisphere parametrization at any point `p ∈ S²` with `0 < s · p i`,
for `s² = 1`. This covers all six hemispheres uniformly. -/
noncomputable def axHemiParam {i : Fin 3} {s : ℝ} (hs : s ^ 2 = 1)
    {p : Fin 3 → ℝ} (_hp : p ∈ unitSphere) (hp_half : 0 < s * p i) :
    Parametrization unitSphere p where
  U := openUnitDisk
  V := axHalf i s
  x := axHemiChart i s
  isOpen_U := isOpen_openUnitDisk
  isOpen_V := isOpen_axHalf i s
  mem_V := hp_half
  mapsTo := mapsTo_axHemiChart i hs
  surjOn := surjOn_axHemiChart i hs
  contDiffOn := contDiffOn_axHemiChart i s
  homeomorph := axHemiHomeomorph i hs
  homeomorph_apply := by intro q; rfl
  fderiv_injective := fun _ hq => fderiv_injective_axHemiChart i s hq

/-- The unit sphere `S² ⊆ ℝ³` is a regular surface. For any `p ∈ S²`, at
least one coordinate `p i` is non-zero (else the sphere equation would fail),
and we use `axHemiParam` with `s = sign (p i)`. -/
theorem unitSphere_isRegular : RegularSurface unitSphere := by
  intro p hp
  have hs1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hsneg1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
  rcases lt_trichotomy (p 2) 0 with h2 | h2 | h2
  · refine ⟨axHemiParam (i := 2) (s := -1) hsneg1 hp ?_⟩
    show 0 < (-1 : ℝ) * p 2; linarith
  · rcases lt_trichotomy (p 1) 0 with h1 | h1 | h1
    · refine ⟨axHemiParam (i := 1) (s := -1) hsneg1 hp ?_⟩
      show 0 < (-1 : ℝ) * p 1; linarith
    · have hp0_sq : p 0 ^ 2 = 1 := by
        have hs : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := hp
        rw [h1, h2] at hs; linarith
      have hp0_ne : p 0 ≠ 0 := fun h0 => by rw [h0] at hp0_sq; norm_num at hp0_sq
      rcases hp0_ne.lt_or_gt with h0 | h0
      · refine ⟨axHemiParam (i := 0) (s := -1) hsneg1 hp ?_⟩
        show 0 < (-1 : ℝ) * p 0; linarith
      · refine ⟨axHemiParam (i := 0) (s := 1) hs1 hp ?_⟩
        show 0 < (1 : ℝ) * p 0; linarith
    · refine ⟨axHemiParam (i := 1) (s := 1) hs1 hp ?_⟩
      show 0 < (1 : ℝ) * p 1; linarith
  · refine ⟨axHemiParam (i := 2) (s := 1) hs1 hp ?_⟩
    show 0 < (1 : ℝ) * p 2; linarith

end RegularSurface
