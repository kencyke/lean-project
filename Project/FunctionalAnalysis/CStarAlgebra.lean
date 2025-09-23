import Project.FunctionalAnalysis.BanachAlgebra
import Project.FunctionalAnalysis.Ideal
import Mathlib.Analysis.Normed.Group.Quotient

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

/-- https://en.wikipedia.org/wiki/Algebra_over_a_field#Subalgebras_and_ideals -/
class LeftKernel (A : Type*) [CStarAlgebra A] extends Ideal A, Submodule ℂ A
class RightKernel (A : Type*) [CStarAlgebra A] extends Ideal Aᵐᵒᵖ, Submodule ℂ Aᵐᵒᵖ

-- Provide a `Membership` instance so that we can write `x ∈ I` for a `LeftKernel`.
instance (A : Type*) [CStarAlgebra A] : Membership A (LeftKernel A) where
  mem I x := x ∈ I.toSubmodule

lemma LeftKernel.mem_toSubmodule {A : Type*} [CStarAlgebra A]
  (I : LeftKernel A) (x : A) : (x ∈ I : Prop) ↔ x ∈ I.toSubmodule := Iff.rfl

instance hasQuotientLeftKernel (A : Type*) [CStarAlgebra A] : HasQuotient A (LeftKernel A) where
  quotient' I := A ⧸ I.toSubmodule

instance (A : Type*) [CStarAlgebra A] (I : LeftKernel A) : AddCommGroup (A ⧸ I) :=
  Submodule.Quotient.addCommGroup I.toSubmodule

instance (A : Type*) [CStarAlgebra A] (I : LeftKernel A) : Module ℂ (A ⧸ I) :=
  Submodule.Quotient.module I.toSubmodule

end NotMathlib
