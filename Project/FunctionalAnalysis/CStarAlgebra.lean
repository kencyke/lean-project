import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.RepresentationTheory.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

import Project.FunctionalAnalysis.BanachAlgebra
import Project.FunctionalAnalysis.HilbertSpace

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

/-- An approximate identity in a C*-algebra is a net {eλ}λ∈Λ satisfying:
    AI-1. eλ ≥ 0 for all λ,
    AI-2. ∥eλ∥ ≤ 1 for all λ,
    AI-3. λ ≤ µ implies eλ ≤ eµ and
    AI-4. for all a ∈ A, limλ eλa = a = limλ aeλ. -/
structure ApproximateIdentity (Λ : Type*) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    [PartialOrder A] [TopologicalSpace A] where
  /-- The net of elements indexed by Λ -/
  e : Λ → A
  /-- AI-1: Each element is nonnegative -/
  nonneg : ∀ i, 0 ≤ e i
  /-- AI-2: Each element has norm at most 1 -/
  norm_le_one : ∀ i, ‖e i‖ ≤ 1
  /-- AI-3: The net is monotone -/
  monotone : Monotone e
  /-- AI-4: Left convergence to the identity -/
  left_converge : ∀ a : A, Filter.Tendsto (fun i => e i * a) Filter.atTop (nhds a)
  /-- AI-4: Right convergence to the identity -/
  right_converge : ∀ a : A, Filter.Tendsto (fun i => a * e i) Filter.atTop (nhds a)

variable {H : Type*} [HilbertSpace ℂ H]
variable {hH : HilbertSpace ℂ H}

noncomputable instance : BanachAlgebra (𝓑(H)) where
  toSeminormedAddCommGroup := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    infer_instance
  toNormedSpace := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    infer_instance
  toCompleteSpace := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    infer_instance
  eq_of_dist_eq_zero := fun {x y} h => by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact eq_of_dist_eq_zero h
  left_distrib := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact mul_add
  right_distrib := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact add_mul
  zero_mul := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact zero_mul
  mul_zero := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact mul_zero
  norm_mul_le := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact norm_mul_le
  smul_comm := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact SMulCommClass.smul_comm
  smul_assoc := by
    letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
    letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
    letI : CompleteSpace H := hH.toCompleteSpace
    exact IsScalarTower.smul_assoc

noncomputable instance : CStarAlgebra (𝓑(H)) where
  toStarRing := BoundedLinearOperator.instStarRing
  toCStarRing := BoundedLinearOperator.instCStarRing
  toStarModule := BoundedLinearOperator.instStarModule

abbrev CStarRepresentation := A →⋆ₙₐ[ℂ] 𝓑(H)

class Ideal (A : Type*) [CStarAlgebra A] extends AddSubgroup A, SubMulAction ℂ A where
  mul_mem' : ∀ (a : A) {x : A}, x ∈ carrier → a * x ∈ carrier

def idealQuotientRel (I : Ideal A) : Setoid A :=
  QuotientAddGroup.leftRel I.toAddSubgroup

instance hasQuotient : HasQuotient A (Ideal A) where
  quotient' I := Quotient (idealQuotientRel I)

instance : SetLike (Ideal A) A where
  coe I := I.carrier
  coe_injective' p q h := by
    cases p
    cases q
    congr
    ext x
    simpa [AddSubgroup.mem_carrier] using Set.ext_iff.mp h x

instance : Membership A (Ideal A) := SetLike.instMembership

instance  (I : Ideal A) : AddCommGroup (A ⧸ I) := QuotientAddGroup.Quotient.addCommGroup I.toAddSubgroup

instance  (I : Ideal A) : Module ℂ (A ⧸ I) where
  smul c := Quotient.map' (c • ·) fun x y h =>
    QuotientAddGroup.leftRel_apply.mpr <| by
      simpa using I.smul_mem' c (QuotientAddGroup.leftRel_apply.mp h)
  one_smul a := Quotient.inductionOn' a fun x => congr_arg Quotient.mk'' (one_smul ℂ x)
  mul_smul c₁ c₂ a := Quotient.inductionOn' a fun x => congr_arg Quotient.mk'' (mul_smul c₁ c₂ x)
  smul_zero c := congr_arg Quotient.mk'' (smul_zero c : c • (0 : A) = 0)
  smul_add c a b := Quotient.inductionOn₂' a b fun x y =>
    congr_arg Quotient.mk'' (smul_add c x y)
  add_smul c₁ c₂ a := Quotient.inductionOn' a fun x =>
    congr_arg Quotient.mk'' (add_smul c₁ c₂ x)
  zero_smul a := Quotient.inductionOn' a fun x => congr_arg Quotient.mk'' (zero_smul ℂ x)

/-!  NOTE: The generic seminormed instance for the quotient is disabled so that, in the GNS
construction, we can endow the quotient with the seminorm coming directly from the GNS
inner product (via `InnerProductSpace.Core`).  If needed elsewhere, this can be reinstated
or given lower priority. -/
-- noncomputable instance  (I : Ideal A) : SeminormedAddCommGroup (A ⧸ I) :=
--   QuotientAddGroup.instSeminormedAddCommGroup I.toAddSubgroup

end NotMathlib
