import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.LinearMap

namespace NotMathlib

class HilbertSpace (𝕜 H : Type*) [RCLike 𝕜] extends NormedAddCommGroup H, InnerProductSpace 𝕜 H, CompleteSpace H

abbrev BoundedLinearOperator (H : Type*) [HilbertSpace ℂ H] := H →L[ℂ] H
notation:50 "𝓑(" H ")" => BoundedLinearOperator H

end NotMathlib
