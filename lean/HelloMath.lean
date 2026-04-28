import Mathlib

theorem hello : 1 + 1 = 2 := by rfl

example : (1 : ℕ) + 1 = 2 := by rfl

example (n : ℕ) : n + 0 = n := by simp

example : ∀ n : ℕ, n + 0 = n := by intro n; simp
