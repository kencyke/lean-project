import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Star.Basic

open Complex
open scoped ComplexConjugate
open scoped NNReal

/-- Predicate for expressing that a complex number is a nonnegative real -/
def IsNNReal (c : ℂ) : Prop :=
  c.im = 0 ∧ ∃ r : ℝ≥0, c = r

/-- Custom operator ⪯ for our positivity condition -/
infix:50 " ≧ " => fun c _ => IsNNReal c

class State {A} (ω: A → ℂ) [CStarAlgebra A] where
  /-- Linearity: ω(cx + dy) = cω(x) + dω(y) for c,d ∈ ℂ and x,y ∈ A -/
  linear_add: ∀ (x y : A), ω (x + y) = ω x + ω y
  linear_mul: ∀ (x : A) (c : ℂ), ω (c • x) = c •  ω x
  /-- Positivity: ω(a* a) is a nonnegative real for all a ∈ A -/
  nonnegative_real : ∀ a : A, ω (star a * a) ≧ 0
  /-- Unital property: ω(1) = 1, i.e., A should contain a unit element -/
  unital : ω 1 = 1

variable {A} (a b : A) [CStarAlgebra A]
variable (ω : A → ℂ) [State ω]

lemma star_as_conj (z : ℂ) : star z = conj z := by rfl

lemma star_mul_self_eq_normSq (z : ℂ) : star z * z = ‖z‖^2 := by
  rw [star_as_conj, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

lemma nonnegative_real (z : ℂ) : ω (star (z • a + b) * (z • a + b)) ≧ 0 :=
  State.nonnegative_real (z • a + b)

lemma quadratic_expansion (z : ℂ) : ω (star (z • a + b) * (z • a + b)) =
    ‖z‖^2 * ω (star a * a) + conj z * ω (star a * b) + z * ω (star b * a) + ω (star b * b) := by
  rw [star_add, star_smul, add_mul, mul_add, mul_add, ← add_assoc]
  simp [State.linear_add, State.linear_mul, ← star_mul_self_eq_normSq]
  ring

lemma cauchy_schwarz_eq : ω (star a * b) = conj (ω (star b * a)) := by
  have real_parts_equal : (ω (star a * b)).re = (ω (star b * a)).re := by
    have h1 := quadratic_expansion a b ω I
    have h2 : (ω (star (I • a + b) * (I • a + b))).im = 0 := by
      have h := nonnegative_real a b ω I
      exact h.1
    have h3 : ω (star (I • a + b) * (I • a + b)) = ω (star a * a) + (-I) * ω (star a * b) + I * ω (star b * a) + ω (star b * b) := by
      rw [h1]; simp only [Complex.norm_I, Complex.conj_I, neg_mul]; norm_cast; ring
    rw [h3] at h2
    have real_aa : (ω (star a * a)).im = 0 := by
      have h := @State.nonnegative_real A ω _ _ a
      exact h.1
    have real_bb : (ω (star b * b)).im = 0 := by
      have h := @State.nonnegative_real A ω _ _ b
      exact h.1
    simp [Complex.add_im, Complex.mul_im, real_aa, real_bb] at h2
    linarith [h2]
  have imag_parts_cancel : (ω (star a * b)).im + (ω (star b * a)).im = 0 := by
    have h1 := quadratic_expansion a b ω (1:ℂ)
    have h2 : (ω (star ((1:ℂ) • a + b) * ((1:ℂ) • a + b))).im = 0 := by
      have h := nonnegative_real a b ω (1:ℂ)
      exact h.1
    have h3 : ω (star ((1:ℂ) • a + b) * ((1:ℂ) • a + b)) = ω (star a * a) + ω (star a * b) + ω (star b * a) + ω (star b * b) := by
      rw [h1]; simp only [map_one, one_mul]; norm_cast; ring
    rw [h3] at h2
    have real_aa : (ω (star a * a)).im = 0 := by
      have h := @State.nonnegative_real A ω _ _ a
      exact h.1
    have real_bb : (ω (star b * b)).im = 0 := by
      have h := @State.nonnegative_real A ω _ _ b
      exact h.1
    simp [Complex.add_im, real_aa, real_bb] at h2
    exact h2
  apply Complex.ext
  · rw [Complex.conj_re, real_parts_equal]
  · rw [Complex.conj_im]
    linarith [imag_parts_cancel]

noncomputable def ωnn (ω : A → ℂ) [State ω] (x : A): ℝ≥0 :=
  Classical.choose (State.nonnegative_real (ω := ω) x).2

lemma cauchy_schwarz_ineq : ‖ω (star b * a)‖^2 ≤ (ωnn ω a) * (ωnn ω b) := by
  sorry
