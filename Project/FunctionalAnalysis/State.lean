import Mathlib.Algebra.QuadraticDiscriminant

import Project.FunctionalAnalysis.CStarAlgebra

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
variable (x y: A)
variable (ω: A → ℂ) [State ω]
variable (z: ℂ)

@[simp]
lemma map_add : ω (x + y) = ω x + ω y := State.linear_add x y

@[simp]
lemma map_smul : ω (z • x) = z • ω x := State.linear_mul x z

@[simp]
lemma star_as_conj : star z = conj z := rfl

@[simp]
lemma star_mul_self_eq_normSq : star z * z = ‖z‖^2 := Complex.conj_mul' z

@[simp]
lemma quadratic_expansion : ω (star (z • x + y) * (z • x + y)) =
  ‖z‖^2 * ω (star x * x) + conj z * ω (star x * y) + z * ω (star y * x) + ω (star y * y) := by
  have hstar : star (z • x + y) = conj z • star x + star y := by simp
  rw [hstar]
  simp [add_mul, mul_add, map_add, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← Complex.conj_mul']
  ring

@[simp]
theorem conj_sym : ω (star y * x) = conj (ω (star x * y)) := by
  set β : ℂ := ω (star x * y)
  set γ : ℂ := ω (star y * x)
  have im_pos : ∀ t : A, (ω (star t * t)).im = 0 := by
    intro t
    rcases (State.positive (ω := ω) t) with ⟨r, hr⟩
    simp [hr]
  have hIm_sum_zero : (β + γ).im = 0 := by
    have hE := quadratic_expansion (ω := ω) (x := x) (y := y) (z := (1 : ℂ))
    have eqim := congrArg Complex.im hE
    have : Complex.im (ω (star ((1 : ℂ) • x + y) * ((1 : ℂ) • x + y))) = 0 := im_pos ((1 : ℂ) • x + y)
    have : Complex.im (ω (star x * x) + β + γ + ω (star y * y)) = 0 := by
      simpa [norm_one] using eqim.symm.trans this
    simpa [im_pos x, im_pos y] using this
  have hre_eq : γ.re = β.re := by
    have hE := quadratic_expansion (ω := ω) (x := x) (y := y) (z := Complex.I)
    have eqim := congrArg Complex.im hE
    have : Complex.im (ω (star (Complex.I • x + y) * (Complex.I • x + y))) = 0 := im_pos (Complex.I • x + y)
    have h := eqim.symm.trans this
    have : -β.re + γ.re = 0 := by simpa [norm_one, im_pos x, im_pos y, Complex.conj_I] using h
    linarith
  have him_eq : γ.im = -β.im := by
    have : β.im + γ.im = 0 := by simpa using hIm_sum_zero
    linarith
  exact Complex.ext hre_eq him_eq

noncomputable def positive_real (a : A) : ℝ≥0 :=
  Classical.choose (State.positive (ω := ω) a)

lemma ω_spec (a : A) : ω (star a * a) = positive_real ω a :=
  Classical.choose_spec (State.positive (ω := ω) a)

lemma phase_alignment (ω: A → ℂ) [State ω] : ∃ γ : ℂ, ‖γ‖ = 1 ∧ γ * ω (star y * x) = ‖ω (star y * x)‖ := by
  by_cases h : ω (star y * x) = 0
  · use 1
    constructor
    norm_num
    rw [h]
    norm_num
  · set z := ω (star y * x)
    use conj z / ‖z‖
    simp [norm_eq_zero.not.2 h]
    field_simp [norm_eq_zero.not.2 h]
    rw [Complex.conj_mul', pow_two]

lemma conj_linear_combination_real:
    (conj z) * ω (star x * y) + z * ω (star y * x)
      = Complex.ofReal (2 * (z * ω (star y * x)).re) := by
  set β : ℂ := ω (star x * y)
  set γ : ℂ := ω (star y * x)
  have hγβ : γ = conj β := conj_sym (ω := ω) (x := x) (y := y)
  refine Complex.ext ?hre_eq ?him_eq
  · -- Real part
    have hsum_re : ((conj z) * β + z * γ).re = 2 * (z.re * β.re + z.im * β.im) := by
      simp [Complex.add_re, Complex.mul_re, hγβ, two_mul]
    have hre2 : 2 * (z.re * β.re + z.im * β.im) = 2 * (z * γ).re := by
      simp [Complex.mul_re, hγβ]
    simp [hsum_re, hre2]
  · -- Imaginary part is zero on both sides
    have : ((conj z) * β + z * γ).im = 0 := by
      simp [Complex.add_im, Complex.mul_im, hγβ]
      ring
    simpa using this

open ComplexOrder in
theorem cauchy_schwarz_ineq : ‖ω (star y * x)‖^2 ≤ (ω (star x * x)) * (ω (star y * y)) := by
  have quad_nonneg : ∀ t : ℝ,
      0 ≤ (positive_real ω x) * (t * t) + (2 * ‖ω (star y * x)‖ ) * t + (positive_real ω y) := by
    intro t
    obtain ⟨γ, hγ_norm, hγ_phase⟩ := phase_alignment ω (x := x) (y := y)
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

end State
