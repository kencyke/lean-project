import Mathlib.Analysis.Complex.Basic

open scoped ComplexConjugate

lemma complex_phase_alignment (c : ℂ) : ∃ γ : ℂ, ‖γ‖ = 1 ∧ γ * c = ‖c‖ := by
  classical
  by_cases h : c = 0
  · refine ⟨1, ?_, ?_⟩
    · simp
    · simp [h]
  · refine ⟨conj c / ‖c‖, ?_, ?_⟩
    · simp [norm_eq_zero.not.2 h]
    · field_simp [norm_eq_zero.not.2 h]
      simp [Complex.conj_mul', pow_two]
