import Project.FunctionalAnalysis.State
import Project.FunctionalAnalysis.HilbertSpace
import Project.FunctionalAnalysis.Ideal

open NotMathlib
open scoped ComplexConjugate NNReal

variable {A} {ω : A → ℂ} [CStarAlgebra A] [State ω]

def Nω : Set A := { x : A | ω (star x * x) = 0 }
local notation "NωS" => (Nω (ω := ω))

-- Closed under addition: if x,y ∈ Nω then x + y ∈ Nω
lemma Nω_closed_under_add {x y : A} (hx : x ∈ NωS) (hy : y ∈ NωS) : x + y ∈ NωS := by
  have h_expand : star (x + y) * (x + y) = star x * x + star x * y + star y * x + star y * y := by
    rw [star_add, add_mul, mul_add, mul_add]
    ac_rfl
  have h_omega : ω (star (x + y) * (x + y)) = ω (star x * x) + ω (star x * y) + ω (star y * x) + ω (star y * y) := by
    rw [h_expand]
    simp only [State.map_add]
  have hx_zero : ω (star x * x) = 0 := hx
  have hy_zero : ω (star y * y) = 0 := hy
  -- Use Cauchy-Schwarz to show cross terms vanish when diagonal terms are zero
  have hyx_zero : ω (star y * x) = 0 := by
    have hcs := State.cauchy_schwarz_ineq (ω := ω) (x := x) (y := y)
    have h_bound : (‖ω (star y * x)‖ : ℝ)^2 ≤ 0 := by
      rw [hx_zero, zero_mul] at hcs
      exact_mod_cast hcs
    have h_nonneg : 0 ≤ (‖ω (star y * x)‖ : ℝ)^2 := sq_nonneg _
    have h_eq : (‖ω (star y * x)‖ : ℝ)^2 = 0 := le_antisymm h_bound h_nonneg
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h_eq)
  have hxy_zero : ω (star x * y) = 0 := by
    have h_conj := State.conj_sym (ω := ω) (x := y) (y := x)
    rw [h_conj]
    rw [hyx_zero]
    rw [map_zero]
  change ω (star (x + y) * (x + y)) = 0
  rw [h_omega, hx_zero, hy_zero, hxy_zero, hyx_zero]
  rw [zero_add, zero_add, zero_add]

-- Closed under left multiplication: if x ∈ Nω then a * x ∈ Nω for all a
lemma Nω_closed_under_left_mul {a x : A} (hx : x ∈ NωS) : a * x ∈ NωS := by
  -- We want to show ω(star(a*x) * (a*x)) = 0
  -- Note: star(a*x) = star(x) * star(a), so star(a*x) * (a*x) = star(x) * star(a) * a * x
  -- Use Cauchy-Schwarz: |ω(star z * x)|² ≤ ω(star x * x) * ω(star z * z)
  -- With z = star(a) * a * x, since ω(star x * x) = 0, we get the result
  have h_cs := State.cauchy_schwarz_ineq (ω := ω) (x := x) (y := (star a) * a * x)
  have h_bound : (‖ω (star ((star a) * a * x) * x)‖ : ℝ)^2 ≤ 0 := by
    rw [hx, zero_mul] at h_cs
    exact_mod_cast h_cs
  have h_nonneg : 0 ≤ (‖ω (star ((star a) * a * x) * x)‖ : ℝ)^2 := sq_nonneg _
  have h_eq : (‖ω (star ((star a) * a * x) * x)‖ : ℝ)^2 = 0 := le_antisymm h_bound h_nonneg
  have h_zero : ω (star ((star a) * a * x) * x) = 0 := by
    have h_cast : ‖ω (star ((star a) * a * x) * x)‖ = 0 := by
      rw [← sq_eq_zero_iff]
      exact_mod_cast h_eq
    exact norm_eq_zero.mp h_cast
  have h_eq_expr : star ((star a) * a * x) * x = star (a * x) * (a * x) := by
    calc star ((star a) * a * x) * x
      = (star x * star ((star a) * a)) * x := by simp [star_mul, mul_assoc]
    _ = (star x * (star a * a)) * x := by simp [star_mul, star_star]
    _ = star x * ((star a * a) * x) := by simp [mul_assoc]
    _ = (star x * star a) * (a * x) := by simp [mul_assoc]
    _ = star (a * x) * (a * x) := by simp [star_mul]
  change ω (star (a * x) * (a * x)) = 0
  rw [← h_eq_expr]
  exact h_zero

def Nω_is_left_ideal : LeftIdeal A where
  carrier := NωS
  zero_mem' := by
    change ω (star (0 : A) * (0 : A)) = 0
    have hω0 : ω (0 : A) = 0 := by
      simpa using (State.map_smul (ω := ω) (x := (0 : A)) (z := (0 : ℂ)))
    simpa [star_zero, zero_mul] using hω0
  add_mem' := by
    intro x y hx hy
    exact Nω_closed_under_add (ω := ω) hx hy
  smul_mem' := by
    intro a x hx
    simpa using (Nω_closed_under_left_mul (ω := ω) (a := a) hx)

local notation "Nω" => (Nω_is_left_ideal (ω := ω))

/- Define the inner product on the quotient: (ηωx | ηωy) := ω (star x * y) -/
noncomputable def innerQuot (ηωx ηωy : A ⧸ Nω) : ℂ := sorry
