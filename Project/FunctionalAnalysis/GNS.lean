import Mathlib.Analysis.InnerProductSpace.Completion

import Project.FunctionalAnalysis.State
import Project.FunctionalAnalysis.HilbertSpace
import Project.FunctionalAnalysis.Ideal
import Project.FunctionalAnalysis.CStarAlgebra

open NotMathlib
open scoped ComplexConjugate NNReal

variable {A} {ω : A → ℂ} [CStarAlgebra A] [State ω]

def Nω : LeftKernel A where
  carrier := { x : A | ω (star x * x) = 0 }
  zero_mem' := by
    change ω (star (0 : A) * (0 : A)) = 0
    have hω0 : ω (0 : A) = 0 := by
      simpa using (State.map_smul (ω := ω) (x := (0 : A)) (z := (0 : ℂ)))
    simpa [star_zero, zero_mul] using hω0
  add_mem' := by
    intro x y hx hy
    exact State.kernel_closed_under_add (ω := ω) (x := x) (y := y) hx hy
  neg_mem' := by
    intro x hx
    change ω (star x * x) = 0 at hx
    change ω (star (-x) * (-x)) = 0
    simp only [star_neg, neg_mul_neg]
    exact hx
  mul_mem' := by
    intro a x hx
    exact State.kernel_closed_under_left_mul (ω := ω) (a := a) (x := x) hx
  smul_mem' := by
    intro c x hx
    exact State.kernel_closed_under_smul (ω := ω) (c := c) (x := x) hx

local notation "Nω" => (Nω (ω := ω))

/- Define the inner product on the quotient: ⟪[x],[y]⟫ := ω (star x * y) -/
def innerQuot (xq yq : A ⧸ Nω) : ℂ :=
  Quot.liftOn xq
    (fun x =>
      Quot.liftOn yq (fun y => ω (star x * y))
        (fun y₁ y₂ hy => by
      -- hy : y₁ ∼ y₂
          have hy' : y₁ - y₂ ∈ Nω := by
            -- Use the known definition of the equivalence relation
            simpa [Submodule.quotientRel_def] using hy
          exact State.equiv_right (ω := ω) x y₁ y₂ hy'))
    (fun x₁ x₂ hx => by
  -- hx : x₁ ∼ x₂ ⇒ values agree for all y
      refine Quot.induction_on yq (fun y => ?_)
      have hx' : x₁ - x₂ ∈ Nω := by
        simpa [Submodule.quotientRel_def] using hx
      exact State.equiv_left (ω := ω) x₁ x₂ y hx')

lemma innerQuot_mk (a b : A) : innerQuot (ω := ω) (Quot.mk _ a) (Quot.mk _ b) = ω (star a * b) := rfl

instance instInnerProductSpaceCore : InnerProductSpace.Core ℂ (A ⧸ Nω) :=
  { toCore :=
    { toInner := ⟨innerQuot⟩
      conj_inner_symm := by
        intro x y
        refine Quot.inductionOn x (fun a => ?_)
        refine Quot.inductionOn y (fun b => ?_)
        show conj (innerQuot (ω := ω) (Quot.mk _ b) (Quot.mk _ a)) = innerQuot (ω := ω) (Quot.mk _ a) (Quot.mk _ b)
        rw [innerQuot_mk]
        exact (State.conj_sym (ω := ω) (x := b) (y := a)).symm
      re_inner_nonneg := by
        intro x
        refine Quot.inductionOn x (fun a => ?_)
        show 0 ≤ RCLike.re (innerQuot (Quot.mk _ a) (Quot.mk _ a))
        rw [innerQuot_mk]
        have := State.positive (ω := ω) a
        obtain ⟨r, hr⟩ := this
        rw [hr]
        exact r.coe_nonneg
      add_left := by
        intro x y z
        refine Quot.inductionOn x (fun a => ?_)
        refine Quot.inductionOn y (fun b => ?_)
        refine Quot.inductionOn z (fun c => ?_)
        show innerQuot (Quot.mk _ (a + b)) (Quot.mk _ c) =
             innerQuot (Quot.mk _ a) (Quot.mk _ c) + innerQuot (Quot.mk _ b) (Quot.mk _ c)
        rw [innerQuot_mk, innerQuot_mk, innerQuot_mk]
        rw [star_add, add_mul]
        exact State.map_add (ω := ω) (x := star a * c) (y := star b * c)
      smul_left := by
        intro x y r
        refine Quot.inductionOn x (fun a => ?_)
        refine Quot.inductionOn y (fun b => ?_)
        show innerQuot (Quot.mk _ (r • a)) (Quot.mk _ b) = conj r * innerQuot (Quot.mk _ a) (Quot.mk _ b)
        rw [innerQuot_mk, innerQuot_mk]
        rw [star_smul, smul_mul_assoc]
        exact State.map_smul (ω := ω) (x := star a * b) (z := conj r) }
    definite := by
      intro x hx
      induction x using Quot.ind with
      | mk a =>
        have hx' : ω (star a * a) = 0 := by simp only [Inner.inner] at hx; convert hx
        apply Quot.sound
        rwa [Submodule.quotientRel_def, sub_zero] }

instance instNormedSpace : NormedSpace ℂ (A ⧸ Nω) :=
  @Submodule.Quotient.normedSpace _ _ ℂ _ _ Nω.toSubmodule ℂ _ _ _ _

instance instInnerProductSpace : InnerProductSpace ℂ (A ⧸ Nω) where
  toInner := instInnerProductSpaceCore.toInner
  conj_inner_symm := instInnerProductSpaceCore.conj_inner_symm
  add_left := instInnerProductSpaceCore.add_left
  smul_left := instInnerProductSpaceCore.smul_left
  norm_sq_eq_re_inner := by sorry

abbrev Hω := UniformSpace.Completion (A ⧸ Nω)
local notation "Hω" => (Hω (ω := ω))

instance instCompleteSpace : CompleteSpace Hω := inferInstance

noncomputable instance instHilbertSpace : NotMathlib.HilbertSpace ℂ Hω := {}
