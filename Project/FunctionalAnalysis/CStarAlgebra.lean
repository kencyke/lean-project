import Project.FunctionalAnalysis.BanachAlgebra
import Project.FunctionalAnalysis.Ideal

open scoped ComplexConjugate

namespace NotMathlib

class CStarAlgebra (A : Type*) extends BanachAlgebra A, StarRing A, CStarRing A, StarModule ℂ A

variable {A : Type*} [CStarAlgebra A]
variable {x y : A}
variable (c : ℂ)

lemma star_star_eq : star (star x) = x := star_star x
lemma star_add_eq : star (x + y) = star x + star y := star_add x y
lemma star_smul_eq : star (c • x) = (conj c) • star x := star_smul c x
lemma star_mul_eq : star (x * y) = star y * star x := star_mul x y
lemma norm_star_eq : ‖star x‖ = ‖x‖ := norm_star x
lemma cstar_identity : ‖star x * x‖ = ‖x‖ ^ 2 := by simp [CStarRing.norm_star_mul_self, pow_two]

end NotMathlib
