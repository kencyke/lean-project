import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace NotMathlib

class HilbertSpace (𝕜 H : Type*) [RCLike 𝕜] extends NormedAddCommGroup H, InnerProductSpace 𝕜 H, CompleteSpace H

abbrev BoundedLinearOperator (H : Type*) [HilbertSpace ℂ H] := H →L[ℂ] H
notation:50 "𝓑(" H ")" => BoundedLinearOperator H

noncomputable instance BoundedLinearOperator.instStarRing {H : Type*} [hH : HilbertSpace ℂ H] :
    StarRing (BoundedLinearOperator H) :=
  @ContinuousLinearMap.instStarRingId ℂ H _ hH.toNormedAddCommGroup hH.toInnerProductSpace hH.toCompleteSpace

noncomputable instance BoundedLinearOperator.instCStarRing {H : Type*} [hH : HilbertSpace ℂ H] :
    CStarRing (BoundedLinearOperator H) :=
  @ContinuousLinearMap.instCStarRingId ℂ H _ hH.toNormedAddCommGroup hH.toInnerProductSpace hH.toCompleteSpace

noncomputable instance BoundedLinearOperator.instStarModule {H : Type*} [hH : HilbertSpace ℂ H] :
    StarModule ℂ (BoundedLinearOperator H) := by
  letI : NormedAddCommGroup H := hH.toNormedAddCommGroup
  letI : InnerProductSpace ℂ H := hH.toInnerProductSpace
  letI : CompleteSpace H := hH.toCompleteSpace
  infer_instance

end NotMathlib
