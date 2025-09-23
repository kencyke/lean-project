import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Quotient

namespace NotMathlib

structure Ideal (R : Type u) [NonUnitalNonAssocSemiring R] : Type u extends AddSubmonoid R, SubMulAction R R

abbrev LeftIdeal (R : Type*) [NonUnitalNonAssocSemiring R] := Ideal R
abbrev RightIdeal (R : Type*) [NonUnitalNonAssocSemiring R] := Ideal Rᵐᵒᵖ

def idealQuotientRel {R : Type*} [NonUnitalNonAssocSemiring R] (I : Ideal R) : Setoid R where
  r := fun x y => ∃ (i j : R), i ∈ I.toAddSubmonoid ∧ j ∈ I.toAddSubmonoid ∧ x + i = y + j
  iseqv := {
    refl := fun x => ⟨0, 0, I.toAddSubmonoid.zero_mem, I.toAddSubmonoid.zero_mem, by simp⟩
    symm := fun h => by
      obtain ⟨i, j, hi, hj, hij⟩ := h
      exact ⟨j, i, hj, hi, hij.symm⟩
    trans := fun h₁ h₂ => by
      obtain ⟨i₁, j₁, hi₁, hj₁, h₁⟩ := h₁
      obtain ⟨i₂, j₂, hi₂, hj₂, h₂⟩ := h₂
      use i₁ + i₂, j₁ + j₂
      exact ⟨I.toAddSubmonoid.add_mem hi₁ hi₂,
             I.toAddSubmonoid.add_mem hj₁ hj₂,
             by rw [← add_assoc, h₁, add_assoc, add_comm j₁ i₂, ← add_assoc, h₂, add_assoc, add_comm j₂ j₁]⟩
  }


instance hasQuotient (R : Type*) [NonUnitalNonAssocSemiring R] : HasQuotient R (Ideal R) where
  quotient' I := Quotient (idealQuotientRel I)

end NotMathlib
