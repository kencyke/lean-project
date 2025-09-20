import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.QuadraticDiscriminant

open scoped ComplexConjugate
open scoped NNReal

namespace Algebra

/- A Banach space is a complete normed space. -/
class BanachSpace (𝕜 H : Type*) [RCLike 𝕜] extends SeminormedAddCommGroup H, NormedSpace 𝕜 H, CompleteSpace H

/--
A Banach algebra is a complex Banach space A together with algebraic conditions such that
- Associativity: (xy)z = x(yz)
- Left distributivity: x(y + z) = xy + xz
- Right distributivity: (x + y)z = xz + yz
- Scalar multiplication: c(xy) = (cx)y = x(cy)
for ∀x,y,z : A, ∀c : ℂ, together with the submultiplicativity of the norm: ‖xy‖ ≤ ‖x‖‖y‖.
-/
class BanachAlgebra (A : Type*) extends BanachSpace ℂ A, NonUnitalNormedRing A, SMulCommClass ℂ A A, IsScalarTower ℂ A A

section BanachAlgebra

variable {A : Type*} [BanachAlgebra A]
variable {x y z : A}
variable {c : ℂ}

lemma _mul_assoc: (x * y) * z = x * (y * z) := by simpa using (mul_assoc x y z)
lemma _mul_add : x * (y + z) = x * y + x * z := by simpa using mul_add x y z
lemma _add_mul : (x + y) * z = x * z + y * z := by simpa using add_mul x y z
lemma _smul_mul : c • (x * y) = (c • x) * y := by simpa using (smul_mul_assoc c x y).symm
lemma _mul_smul : c • (x * y) = x * (c • y) := by simpa using (mul_smul_comm (s := c) (x := x) (y := y)).symm
lemma _norm_mul_le : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by simpa using (norm_mul_le x y)

end BanachAlgebra

/-- A C*-algebra is a involutive Banach algebra and the anti-linear involution: x ↦ x⋆ with ‖x⋆ * y‖ = ‖x⋆‖ * ‖y‖ -/
class CStarAlgebra (A : Type*) extends BanachAlgebra A, StarRing A, CStarRing A, StarModule ℂ A

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
variable {x y : A}
variable (c : ℂ)

lemma star_star_eq : star (star x) = x := by simp
lemma star_add_eq : star (x + y) = star x + star y := by simp
lemma star_smul_eq : star (c • x) = (conj c) • star x := by simp
lemma star_mul_eq : star (x * y) = star y * star x := by simp
lemma norm_star_eq : ‖star x‖ = ‖x‖ := by simp
lemma cstar_identity : ‖star x * x‖ = ‖x‖ ^ 2 := by
  simpa [pow_two] using (CStarRing.norm_star_mul_self (x := x))

end CStarAlgebra

/-- A Hilbert space over a field 𝕜 -/
class HilbertSpace (𝕜 H : Type*) [RCLike 𝕜] extends NormedAddCommGroup H, InnerProductSpace 𝕜 H, CompleteSpace H

abbrev BoundedLinearOperator (H : Type*) [HilbertSpace ℂ H] := H →L[ℂ] H
notation:50 "𝓑(" H ")" => BoundedLinearOperator H

class PositiveLinearFunctional {A} (ω: A → ℂ) [CStarAlgebra A] extends Norm (A → ℂ) where
  /-- Linearity: ω(cx + dy) = cω(x) + dω(y) for c,d ∈ ℂ and x,y ∈ A -/
  linear_add: ∀ (x y : A), ω (x + y) = ω x + ω y
  linear_mul: ∀ (x : A) (c : ℂ), ω (c • x) = c •  ω x
  /-- Positivity: ω(a* a) is a nonnegative real for all a ∈ A -/
  positive : ∀ a : A, ∃ r : ℝ≥0, ω (star a * a) = r
  /-- Definition of the norm of the state: ‖ω‖ = sup_{a ≠ 0} (‖ω a‖ / ‖a‖). -/
  norm_def : ‖ω‖ = sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖ω a‖ / ‖a‖ }
  -- involutive: ∀ (x : A), star ω (x) = conj ω (star x)

section PositiveLinearFunctional

variable {A} [CStarAlgebra A]
variable (ω: A → ℂ) [PositiveLinearFunctional ω]

@[simp] theorem norm_def : ‖ω‖ = sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖ω a‖ / ‖a‖ } :=
  PositiveLinearFunctional.norm_def (ω := ω)

end PositiveLinearFunctional

class State {A} (ω: A -> ℂ) [CStarAlgebra A] extends PositiveLinearFunctional ω where
  norm_one: ‖ω‖ = 1

section State

variable {A} [CStarAlgebra A]
variable (x y a b: A)
variable (ω: A → ℂ) [State ω]
variable (z: ℂ)

@[simp] lemma map_add : ω (x + y) = ω x + ω y := PositiveLinearFunctional.linear_add x y

@[simp] lemma map_smul : ω (z • x) = z • ω x := PositiveLinearFunctional.linear_mul x z

@[simp] lemma star_as_conj : star z = conj z := by rfl

@[simp] lemma star_mul_self_eq_normSq : star z * z = ‖z‖^2 := by
  rw [star_as_conj, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

@[simp] lemma quadratic_expansion : ω (star (z • a + b) * (z • a + b)) =
  (‖z‖^2) * ω (star a * a) + (conj z) * ω (star a * b) + z * ω (star b * a) + ω (star b * b) := by
  have hstar : star (z • a + b) = (conj z) • star a + star b := by
    simp [star_add, star_smul, star_as_conj]
  have hz : (conj z) * z = ‖z‖^2 := by
    simpa [star_as_conj] using (star_mul_self_eq_normSq (z := z))
  have h1prod : ((conj z) • star a) * (z • a) = ((conj z) * z) • (star a * a) := by
    calc
      ((conj z) • star a) * (z • a)
          = (conj z) • (star a * (z • a)) := by simpa using (smul_mul_assoc (conj z) (star a) (z • a))
      _   = (conj z) • (z • (star a * a)) := by
            simpa using congrArg (fun t => (conj z) • t) (mul_smul_comm (x := star a) (s := z) (y := a))
      _   = ((conj z) * z) • (star a * a) := by simp [smul_smul]
  have h2prod : ((conj z) • star a) * b = (conj z) • (star a * b) := by
    simpa using (smul_mul_assoc (conj z) (star a) b)
  have h3prod : (star b) * (z • a) = z • (star b * a) := by
    simpa using (mul_smul_comm (x := star b) (s := z) (y := a))
  calc
    ω (star (z • a + b) * (z • a + b))
        = ω ((((conj z) • star a) + star b) * ((z • a) + b)) := by simp [hstar]
    _   = ω ((((conj z) • star a) * (z • a)) + (((conj z) • star a) * b) + ((star b) * (z • a)) + (star b * b)) := by
            simp [add_mul, mul_add, add_comm, add_left_comm, add_assoc]
    _   = (‖z‖^2) * ω (star a * a) + (conj z) * ω (star a * b) + z * ω (star b * a) + ω (star b * b) := by
            simp [map_add, map_smul, h1prod, h2prod, h3prod, hz, add_comm, add_left_comm, mul_comm]

@[simp] theorem conj_sym : ω (star y * x) = conj (ω (star x * y)) := by
  -- abbreviations
  set β : ℂ := ω (star x * y)
  set γ : ℂ := ω (star y * x)
  -- diagonal terms have zero imaginary part by positivity
  have hx_im0 : (ω (star x * x)).im = 0 := by
    rcases (PositiveLinearFunctional.positive (ω := ω) x) with ⟨r, hr⟩; simp [hr]
  have hy_im0 : (ω (star y * y)).im = 0 := by
    rcases (PositiveLinearFunctional.positive (ω := ω) y) with ⟨r, hr⟩; simp [hr]
  -- tiny helper
  have im_pos : ∀ t : A, (ω (star t * t)).im = 0 :=
    by intro t; rcases (PositiveLinearFunctional.positive (ω := ω) t) with ⟨r, hr⟩; simp [hr]
  -- z = 1 ⇒ Im(β + γ) = 0
  have hIm_sum_zero : (β + γ).im = 0 := by
    have hE := quadratic_expansion (ω := ω) (a := x) (b := y) (z := (1 : ℂ))
    have eqim := congrArg Complex.im hE
    have : Complex.im (ω (star ((1 : ℂ) • x + y) * ((1 : ℂ) • x + y))) = 0 := im_pos ((1 : ℂ) • x + y)
    have : Complex.im ((‖(1 : ℂ)‖ ^ 2) * ω (star x * x) + (conj (1 : ℂ)) * β + (1 : ℂ) * γ + ω (star y * y)) = 0 :=
      eqim.symm.trans this
    simpa [norm_one, hx_im0, hy_im0] using this
  -- z = I ⇒ -Re β + Re γ = 0
  have hre_eq : γ.re = β.re := by
    have hE := quadratic_expansion (ω := ω) (a := x) (b := y) (z := (Complex.I : ℂ))
    have eqim := congrArg Complex.im hE
    have : Complex.im (ω (star ((Complex.I : ℂ) • x + y) * ((Complex.I : ℂ) • x + y))) = 0 := im_pos ((Complex.I : ℂ) • x + y)
    have h := eqim.symm.trans this
    have h' : -β.re + γ.re = 0 := by simpa [norm_one, one_mul, hx_im0, hy_im0, Complex.conj_I] using h
    have : γ.re - β.re = 0 := by simpa [sub_eq_add_neg, add_comm] using h'
    exact sub_eq_zero.mp this
  -- deduce γ.im = -β.im
  have him_eq : γ.im = -β.im := by
    have hsum : β.im + γ.im = 0 := by simpa using hIm_sum_zero
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hsum)
  -- assemble
  refine Complex.ext ?hre ?him
  · simpa using hre_eq
  · simpa using him_eq

theorem cauchy_schwarz_ineq : ‖ω (star y * x)‖^2 ≤ ‖ω (star x * x)‖ * ‖ω (star y * y)‖ := by
  sorry

end State


end Algebra
