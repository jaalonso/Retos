import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℕ → ℝ)
variable (L : ℝ)

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
  have hε2 : ε / 2 > 0 := by linarith
  rcases ha (ε / 2) hε2 with ⟨N, hN⟩
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  specialize hN n hn
  -- hN : |a n - L| < ε / 2
  calc |b n - 2 * L|
       = |2 * a n - 2 * L| := by rw [hb n]
     _ = |2 * (a n - L)|   := by ring_nf
     _ = 2 * |a n - L|     := by norm_num
     _ < 2 * (ε / 2)       := by gcongr
     _ = ε                 := by ring
