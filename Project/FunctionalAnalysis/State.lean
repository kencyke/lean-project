import Mathlib.Algebra.QuadraticDiscriminant

import Project.FunctionalAnalysis.CStarAlgebra
import Project.FunctionalAnalysis.Complex

open NotMathlib
open scoped ComplexConjugate NNReal

class State {A} (ω: A → ℂ) [CStarAlgebra A] extends Norm (A → ℂ) where
  linear_add: ∀ (x y : A), ω (x + y) = ω x + ω y
  linear_mul: ∀ (x : A) (c : ℂ), ω (c • x) = c •  ω x
  positive : ∀ a : A, ∃ r : ℝ≥0, ω (star a * a) = r
  norm_def : ‖ω‖ = sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖ω a‖ / ‖a‖ }
  norm_one: ‖ω‖ = 1
  -- involutive: ∀ (x : A), star ω (x) = conj ω (star x)

namespace State

variable {A} [CStarAlgebra A]
variable (x y a b: A)
variable (x₁ x₂ y₁ y₂ : A)
variable (ω: A → ℂ) [State ω]
variable (z c: ℂ)

lemma map_add : ω (x + y) = ω x + ω y := State.linear_add x y

lemma map_smul : ω (z • x) = z • ω x := State.linear_mul x z

lemma star_as_conj : star z = conj z := rfl

lemma star_mul_self_eq_normSq : star z * z = ‖z‖^2 := Complex.conj_mul' z

lemma quadratic_expansion : ω (star (z • x + y) * (z • x + y)) =
  ‖z‖^2 * ω (star x * x) + conj z * ω (star x * y) + z * ω (star y * x) + ω (star y * y) := by
  have hstar : star (z • x + y) = conj z • star x + star y := by simp
  rw [hstar]
  simp [add_mul, mul_add, map_add, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← Complex.conj_mul']
  ring

theorem conj_sym : ω (star y * x) = conj (ω (star x * y)) := by
  set β : ℂ := ω (star x * y)
  set γ : ℂ := ω (star y * x)
  have quad_real : ∀ t : A, (ω (star t * t)).im = 0 := by
    intro t
    rcases State.positive (ω := ω) t with ⟨r, hr⟩
    simp [hr]
  have sum_im_zero : (β + γ).im = 0 := by
    have hE := quadratic_expansion (ω := ω) (x := x) (y := y) (z := (1 : ℂ))
    have eqim := congrArg Complex.im hE
    have : (ω (star ((1 : ℂ) • x + y) * ((1 : ℂ) • x + y))).im = 0 := quad_real ((1 : ℂ) • x + y)
    have : (ω (star x * x) + β + γ + ω (star y * y)).im = 0 := by
      simpa [norm_one] using eqim.symm.trans this
    simpa [quad_real x, quad_real y] using this
  have diff_re_zero : γ.re = β.re := by
    have hE := quadratic_expansion (ω := ω) (x := x) (y := y) (z := Complex.I)
    have eqim := congrArg Complex.im hE
    have : (ω (star (Complex.I • x + y) * (Complex.I • x + y))).im = 0 := quad_real (Complex.I • x + y)
    have h := eqim.symm.trans this
    have : -β.re + γ.re = 0 := by simpa [norm_one, quad_real x, quad_real y, Complex.conj_I] using h
    linarith
  have im_eq : γ.im = -β.im := by
    have : β.im + γ.im = 0 := by simpa using sum_im_zero
    linarith
  exact Complex.ext diff_re_zero im_eq

noncomputable def positive_real (a : A) : ℝ≥0 :=
  Classical.choose (State.positive (ω := ω) a)

lemma ω_spec : ω (star a * a) = positive_real ω a :=
  Classical.choose_spec (State.positive (ω := ω) a)

lemma conj_linear_combination_real:
    (conj z) * ω (star x * y) + z * ω (star y * x)
      = Complex.ofReal (2 * (z * ω (star y * x)).re) := by
  set β := ω (star x * y)
  set γ := ω (star y * x)
  have hγβ : γ = conj β := conj_sym (ω := ω) (x := x) (y := y)
  -- Both real and imaginary parts
  refine Complex.ext ?_ ?_
  · -- Real part calculation
    simp [Complex.add_re, Complex.mul_re, hγβ, two_mul]
  · -- Imaginary part is zero
    simp [Complex.add_im, Complex.mul_im, hγβ]
    ring

open ComplexOrder in
theorem cauchy_schwarz_ineq : ‖ω (star y * x)‖^2 ≤ (ω (star x * x)) * (ω (star y * y)) := by
  have quad_nonneg : ∀ t : ℝ,
      0 ≤ (positive_real ω x) * (t * t) + (2 * ‖ω (star y * x)‖ ) * t + (positive_real ω y) := by
    intro t
    obtain ⟨γ, hγ_norm, hγ_phase⟩ := complex_phase_alignment (ω (star y * x))
    let s : A := (t * γ) • x + y
    have hexp2 : (ω (star s * s)).re = (positive_real ω x) * (t * t) + (2 * ‖ω (star y * x)‖ ) * t + (positive_real ω y) := by
      have hquad := quadratic_expansion (ω := ω) (x := x) (y := y) (z := (t * γ))
      have h1 : (‖(t : ℂ) * γ‖^2 : ℂ) = (t^2 : ℂ) := by
        rw [Complex.norm_mul, hγ_norm, mul_one, Complex.norm_real, pow_two, pow_two]
        norm_cast
        exact abs_mul_abs_self t
      have h2 : conj (t * γ) * ω (star x * y) + (t * γ) * ω (star y * x) = 2 * t * ‖ω (star y * x)‖ := by
        have : (t * γ) * ω (star y * x) = t * (γ * ω (star y * x)) := by ring
        rw [conj_linear_combination_real, this, hγ_phase]
        norm_cast
        ring
      have hequiv : ω (star s * s) = (t^2 : ℂ) * ω (star x * x) + 2 * t * ‖ω (star y * x)‖ + ω (star y * y) := by
        unfold s
        rw [hquad, h1, ← h2]
        ring
      simp only [congrArg Complex.re hequiv, ω_spec (ω := ω) x, ω_spec (ω := ω) y,
                 Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
                 mul_zero, pow_two, Complex.re_ofNat]
      ring
    rw [← hexp2, ω_spec (ω := ω) s]
    exact (positive_real ω s).property
  have : (2 * ‖ω (star y * x)‖) ^ 2 ≤ 4 * (positive_real ω x) * (positive_real ω y) := by
    have := discrim_le_zero quad_nonneg
    rw [discrim] at this
    linarith
  have : ‖ω (star y * x)‖ ^ 2 ≤ (positive_real ω x) * (positive_real ω y) := by
    have : (2 * ‖ω (star y * x)‖) ^ 2 = 4 * ‖ω (star y * x)‖ ^ 2 := by ring
    linarith
  rw [ω_spec (ω := ω) x, ω_spec (ω := ω) y]
  norm_cast

open ComplexOrder in
lemma continuous_ineq : ‖ω (star b * a * b)‖ ≤ ‖a‖ * ω (star b * b) := by sorry

lemma kernel_degenerate_left (hx : ω (star x * x) = 0) : ω (star a * x) = 0 := by
  have := cauchy_schwarz_ineq (ω := ω) (x := x) (y := a)
  rw [hx, zero_mul] at this
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (by exact_mod_cast this) (sq_nonneg _)))

lemma kernel_degenerate_right (hx : ω (star x * x) = 0) : ω (star x * a) = 0 := by
  rw [conj_sym (ω := ω) (x := a) (y := x), kernel_degenerate_left (ω := ω) (x := x) (a := a) hx, map_zero]

lemma kernel_closed_under_add (hx : ω (star x * x) = 0) (hy : ω (star y * y) = 0) : ω (star (x + y) * (x + y)) = 0 := by
  calc ω (star (x + y) * (x + y))
      = ω (star x * x + star x * y + star y * x + star y * y) := by
          rw [star_add, add_mul, mul_add, mul_add]
          ac_rfl
    _ = ω (star x * x) + ω (star x * y) + ω (star y * x) + ω (star y * y) := by
          rw [map_add (ω := ω) (x := star x * x + star x * y + star y * x) (y := star y * y)]
          rw [map_add (ω := ω) (x := star x * x + star x * y) (y := star y * x)]
          rw [map_add (ω := ω) (x := star x * x) (y := star x * y)]
    _ = 0 := by
          rw [hx, hy, kernel_degenerate_left (ω := ω) (x := y) (a := x) hy, kernel_degenerate_left (ω := ω) (x := x) (a := y) hx]
          ring

lemma kernel_closed_under_smul (hx : ω (star x * x) = 0) : ω (star (c • x) * (c • x)) = 0 := by
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, star_as_conj,
      map_smul (ω := ω) (x := star x * x) (z := conj c * c), hx, smul_zero]

lemma kernel_closed_under_left_mul (hx : ω (star x * x) = 0) : ω (star (a * x) * (a * x)) = 0 := by
  have : star (a * x) * (a * x) = star (star a * a * x) * x := by
    rw [star_mul, star_mul, star_mul, star_star]; ac_rfl
  rw [this]; exact kernel_degenerate_left (ω := ω) (x := x) (a := star a * a * x) hx

lemma equiv_left (x₁ x₂ y : A) (hx : ω (star (x₁ - x₂) * (x₁ - x₂)) = 0) : ω (star x₁ * y) = ω (star x₂ * y) := by
  have hcs := cauchy_schwarz_ineq (ω := ω) (x := y) (y := x₁ - x₂)
  have h0 : ω (star (x₁ - x₂) * y) = 0 := by
    have : (‖ω (star (x₁ - x₂) * y)‖ : ℝ)^2 ≤ 0 := by rw [hx, mul_zero] at hcs; exact_mod_cast hcs
    simpa [sq_eq_zero_iff] using le_antisymm this (sq_nonneg _)
  calc ω (star x₁ * y)
      = ω (star (x₂ + (x₁ - x₂)) * y) := by rw [add_sub_cancel]
    _ = ω (star x₂ * y + star (x₁ - x₂) * y) := by rw [star_add, add_mul]
    _ = ω (star x₂ * y) + ω (star (x₁ - x₂) * y) := map_add (ω := ω) _ _
    _ = ω (star x₂ * y) := by rw [h0, add_zero]

lemma equiv_right (x y₁ y₂ : A) (hy : ω (star (y₁ - y₂) * (y₁ - y₂)) = 0) : ω (star x * y₁) = ω (star x * y₂) := by
  have hzero : ω (star x * (y₁ - y₂)) = 0 :=
    kernel_degenerate_left (ω := ω) (x := y₁ - y₂) (a := x) hy
  have hmul : star x * y₁ = star x * y₂ + star x * (y₁ - y₂) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, mul_add]
  calc
    ω (star x * y₁) = ω (star x * y₂ + star x * (y₁ - y₂)) := by rw [hmul]
    _ = ω (star x * y₂) + ω (star x * (y₁ - y₂)) := map_add (ω := ω) _ _
    _ = ω (star x * y₂) := by rw [hzero, add_zero]

def Nω : Ideal A where
  carrier := { x : A | ω (star x * x) = 0 }
  zero_mem' := by
    change ω (star (0 : A) * (0 : A)) = 0
    have hω0 : ω (0 : A) = 0 := by
      simpa using (map_smul (ω := ω) (x := (0 : A)) (z := (0 : ℂ)))
    simpa [star_zero, zero_mul] using hω0
  add_mem' := by
    intro x y hx hy
    exact kernel_closed_under_add (ω := ω) (x := x) (y := y) hx hy
  neg_mem' := by
    intro x hx
    change ω (star x * x) = 0 at hx
    change ω (star (-x) * (-x)) = 0
    simp only [star_neg, neg_mul_neg]
    exact hx
  mul_mem' := by
    intro a x hx
    exact kernel_closed_under_left_mul (ω := ω) (a := a) (x := x) hx
  smul_mem' := by
    intro c x hx
    exact kernel_closed_under_smul (ω := ω) (c := c) (x := x) hx

end State
