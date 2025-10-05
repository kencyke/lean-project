import Mathlib.Analysis.InnerProductSpace.Completion

import Project.FunctionalAnalysis.State
import Project.FunctionalAnalysis.HilbertSpace
import Project.FunctionalAnalysis.CStarAlgebra

open NotMathlib
open scoped ComplexConjugate NNReal

variable {A} [NotMathlib.CStarAlgebra A]
variable (ω: A → ℂ) [State ω]

local notation "Nω" => (State.Nω (ω := ω))

/-!
We can define an inner product on A/Nω by  ⟪[x], [y]⟫ := ω (star x * y) where [x] = x + Nω.
-/
def innerQuot (xq yq : A ⧸ Nω) : ℂ :=
  Quotient.liftOn₂' xq yq (fun x y => ω (star x * y))
    (fun x₁ y₁ x₂ y₂ (hx : idealQuotientRel (State.Nω ω) x₁ x₂) (hy : idealQuotientRel (State.Nω ω) y₁ y₂) => by
      rw [idealQuotientRel, QuotientAddGroup.leftRel_apply] at hx hy
      -- hx : -x₁ + x₂ ∈ Nω, hy : -y₁ + y₂ ∈ Nω
      show ω (star x₁ * y₁) = ω (star x₂ * y₂)
      have hx' : ω (star (x₂ - x₁) * (x₂ - x₁)) = 0 := by
        simp only [sub_eq_neg_add]
        exact hx
      have hy' : ω (star (y₂ - y₁) * (y₂ - y₁)) = 0 := by
        simp only [sub_eq_neg_add]
        exact hy
      calc ω (star x₁ * y₁)
          = ω (star x₂ * y₁) := (State.equiv_left ω x₂ x₁ y₁ hx').symm
        _ = ω (star x₂ * y₂) := (State.equiv_right ω x₂ y₂ y₁ hy').symm)

instance instInnerProductSpaceCore : InnerProductSpace.Core ℂ (A ⧸ Nω) where
  inner := innerQuot ω
  conj_inner_symm := fun x y => Quotient.inductionOn₂' x y fun a b => by
    unfold innerQuot
    simp only [Quotient.liftOn₂'_mk'']
    rw [State.conj_sym ω (x := b) (y := a)]
  re_inner_nonneg := fun x => Quotient.inductionOn' x fun a => by
    unfold innerQuot
    simp only [Quotient.liftOn₂'_mk'']
    obtain ⟨r, hr⟩ := State.positive (ω := ω) a
    rw [hr]
    exact r.property
  add_left := fun x y z => Quotient.inductionOn₃' x y z fun a b c => by
    unfold innerQuot
    show Quotient.liftOn₂' (Quotient.mk'' (a + b)) (Quotient.mk'' c) _ _ = _
    simp only [Quotient.liftOn₂'_mk'']
    rw [star_add, add_mul]
    exact State.map_add (ω := ω) (x := star a * c) (y := star b * c)
  smul_left := fun x y c => Quotient.inductionOn₂' x y fun a b => by
    unfold innerQuot
    show Quotient.liftOn₂' (Quotient.mk'' (c • a)) (Quotient.mk'' b) _ _ = _
    simp only [Quotient.liftOn₂'_mk'']
    rw [star_smul, smul_mul_assoc]
    exact State.map_smul (ω := ω) (x := star a * b) (z := conj c)
  definite := fun x hx => Quotient.inductionOn' x (fun a ha => by
    unfold innerQuot at ha
    simp only [Quotient.liftOn₂'_mk''] at ha
    exact Quotient.sound' (by
      rw [idealQuotientRel, QuotientAddGroup.leftRel_apply]
      show -a + 0 ∈ (State.Nω ω).toAddSubgroup
      simp only [add_zero, neg_mem_iff]
      exact ha)) hx

noncomputable instance instNormedAddCommGroup_GNS : NormedAddCommGroup (A ⧸ Nω) :=
  (InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := A ⧸ Nω))

noncomputable instance instInnerProductSpace_GNS : InnerProductSpace ℂ (A ⧸ Nω) :=
  InnerProductSpace.ofCore (instInnerProductSpaceCore (ω := ω))

abbrev Hω := UniformSpace.Completion (A ⧸ Nω)
local notation "Hω" => (Hω (ω := ω))

instance instCompleteSpace : CompleteSpace Hω := inferInstance

noncomputable instance instHilbertSpace_GNS : NotMathlib.HilbertSpace ℂ Hω := {}


/-!
we define the representation πω by defining the action of πω(A) on
the dense subset Hω of Hω. Let [B] := B + Nω ∈ Hω, then we define πω(A)[B] := [AB].
For all B ∈ A we have
‖πω(A)[B]‖_Hω^2 = ⟪[AB], [AB]⟫ = ω(B*A*AB) ≤ ‖A‖ω(B*B) = ‖A‖‖[B]‖_Hω^2.
Hence πω(A) is bounded on a dense subset of Hω.
Check that πω(A) is linear on this dense subset, hence it can be extended to a bounded operator on Hω.
From the definition of πω it is apparent that πω(AB) = πω(A)πω(B) and πω(A∗) = πω(A)∗.
Hence we again denote by πω(A) such that πω: A →⋆ₙₐ[ℂ] 𝓑(H).
-/
