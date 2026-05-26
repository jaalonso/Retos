import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a : ℕ → ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  -- Pedimos a ha que trabaje con ε/2, que es > 0
  have hε2 : ε / 2 > 0 := by linarith
  obtain ⟨N, hN⟩ := ha (ε / 2) hε2
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  -- Reescribimos b n usando hb
  rw [hb n]
  -- ⊢ |2 * a n - 2 * L| < ε
  have : 2 * a n - 2 * L = 2 * (a n - L) := by ring
  -- this : 2 * a n - 2 * L = 2 * (a n - L)
  rw [this, abs_mul, abs_of_pos (by norm_num : (2 : ℝ) > 0)]
  -- ⊢ 2 * |a n - L| < ε
  -- Ahora usamos que |a n - L| < ε/2
  have haN := hN n hn
  -- haN : |a n - L| < ε / 2
  linarith
