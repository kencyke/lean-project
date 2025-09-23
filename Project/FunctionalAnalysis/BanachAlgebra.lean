import Mathlib.Analysis.Complex.Basic

class BanachSpace (𝕜 H : Type*) [RCLike 𝕜] extends SeminormedAddCommGroup H, NormedSpace 𝕜 H, CompleteSpace H
class BanachAlgebra (A : Type*) extends BanachSpace ℂ A, NonUnitalNormedRing A, SMulCommClass ℂ A A, IsScalarTower ℂ A A

variable {A : Type*} [BanachAlgebra A]
variable {x y z : A}
variable {c : ℂ}

lemma _mul_assoc: (x * y) * z = x * (y * z) := mul_assoc x y z
lemma _mul_add : x * (y + z) = x * y + x * z := mul_add x y z
lemma _add_mul : (x + y) * z = x * z + y * z := add_mul x y z
lemma _smul_mul : c • (x * y) = (c • x) * y := (smul_mul_assoc c x y).symm
lemma _mul_smul : c • (x * y) = x * (c • y) := (mul_smul_comm c x y).symm
lemma _norm_mul_le : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le x y
