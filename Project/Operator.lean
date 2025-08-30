import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

open scoped ComplexConjugate
open scoped NNReal

namespace Algebra

/- A Banach space is a complete normed space. -/
class BanachSpace (𝕜 H : Type*) [RCLike 𝕜] extends NormedAddCommGroup H, NormedSpace 𝕜 H, CompleteSpace H

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

end Algebra
