import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Quotient
import Mathlib.Analysis.RCLike.Basic

namespace NotMathlib

-- (R : Type*) [AddCommGroup R] [Mul R] ?
class Ideal (R : Type*) [NonUnitalRing R] extends AddSubgroup R where
  mul_mem' : ∀ (a : R) {x : R}, x ∈ carrier → a * x ∈ carrier

abbrev LeftIdeal (R : Type*) [NonUnitalRing R] := Ideal R
abbrev RightIdeal (R : Type*) [NonUnitalRing R] := Ideal Rᵐᵒᵖ

def idealQuotientRel {R : Type*} [NonUnitalRing R] (I : Ideal R) : Setoid R where
  r x y := x - y ∈ I.carrier
  iseqv := {
    refl := fun x => by
      show x - x ∈ I.carrier
      rw [sub_self]
      exact I.zero_mem'
    symm := fun {x y} h => by
      show y - x ∈ I.carrier
      rw [← neg_sub]
      exact I.neg_mem' h
    trans := fun {x y z} h1 h2 => by
      show x - z ∈ I.carrier
      have : x - z = (x - y) + (y - z) := by
        simp only [sub_eq_add_neg]
        rw [add_assoc, ← add_assoc (-y), add_comm (-y) y, add_neg_cancel, zero_add]
      rw [this]
      exact I.add_mem' h1 h2
  }

instance hasQuotient (R : Type*) [NonUnitalRing R] : HasQuotient R (Ideal R) where
  quotient' I := Quotient (idealQuotientRel I)

end NotMathlib
