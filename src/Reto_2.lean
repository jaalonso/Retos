-- Reto_2.lean
-- Soluciones de 2º reto (17 de mayo de 2026).
-- La sucesión 1, -1, 1, -1,... no esconvergente.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- En el reto de esta semana continuamos explorando la convergencia de
-- sucesiones, retomando el trabajo de la semana anterior. El problema
-- consiste en demostrar que la sucesión definida por 1, -1, 1, -1,,,,
-- no converge. Para ello, se propone completar la siguiente
-- demostración en Lean 4:
--    import Mathlib.Data.Real.Basic
--    import Mathlib.Tactic
--
--    variable {a : ℕ → ℝ}
--
--    def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
--
--    def SucConv (a : ℕ → ℝ) : Prop :=
--      ∃ L, LimSuc a L
--
--    example
--      (ha : ∀ n, a n = (-1) ^ n)
--      : ¬ SucConv a :=
--    by sorry
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea a la sucesión definida por a(n) = (-1)^n. Supongamos que a es
-- convergente. Entonces, existe un L tal que a converge L. Por tanto,
-- existe un N ∈ ℕ tal que,
--    ∀n ≥ N, |a(n) - L| < 1/2                                      (1)
-- Entonces,
--    2 = |2|
--      = |(1 - L) + (1 + L)|
--      = |(1 - L) + (-1)(-1 - L)|
--      ≤ |1 - L| + |(-1)(-1 - L)|
--      = |1 - L| + |-1 - L|
--      = |(-1)^{2N} - L| + |(-1)^{2N+1} - L|
--      = |a(2N) - L| + |a(2N+1) - L|
--      < 1/2 + 1/2                            [por (1), 2N ≥ N y 2N+1 ≥ N]
--      = 1
-- Luego, 2 < 1 que es una contradicción.

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a : ℕ → ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

def SucConv (a : ℕ → ℝ) : Prop :=
  ∃ L, LimSuc a L

-- 1ª demostración
-- ===============

namespace Solucion1

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a :=
by
  intro h
  -- h : SucConv a
  -- ⊢ False
  choose L hL using h
  -- L : ℝ
  -- hL : LimSuc a L
  choose N hN using hL (1/2) (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1 / 2
  have h1 : (2:ℝ) < 1 := calc
    2 = |2|                                        := by grind
    _ = |(1 - L) + (1 + L)|                        := by grind
    _ = |(1 - L) + (-1)*(-1 - L)|                  := by grind
    _ ≤ |1 - L| + |(-1)*(-1 - L)|                  := by grind
    _ = |1 - L| + |-1 - L|                         := by grind
    _ = |(-1:ℝ)^(2*N) - L| + |(-1:ℝ)^(2*N+1) - L|  := by
          have h2 : (-1:ℝ)^(2*N) = 1    := by simp
          have h3 : (-1:ℝ)^(2*N+1) = -1 := by grind
          rw [h2, h3]
    _ = |a (2*N) - L| + |a (2*N+1) - L|            := by simp [*]
    _ < 1/2 + 1/2                                  := by grind
    _ = 1                                          := by grind
  linarith

end Solucion1

-- 2ª demostración (refactorización de la 1ª)
-- ==========================================

namespace Solucion2

variable {x y z x' y' : ℝ}
variable {m n k : ℕ}
variable (f : ℝ → ℝ)

lemma L1 : (1 - x) + (1 + x) = 2 := by
  calc (1 - x) + (1 + x)
       = 1 + 1             := sub_add_add_cancel 1 1 x
     _ = 2                 := one_add_one_eq_two

lemma L2 : (-1:ℝ) * -1 = 1 := by
  calc (-1:ℝ) * -1
       = 1 * 1   := neg_mul_neg 1 1
     _ = 1       := one_mul 1

lemma L3 : -1 * -x = x := by
  calc -1 * -x
       = -(1 * -x) := neg_mul 1 (-x)
     _ = - -x      := congr_arg (- ·) (one_mul (-x))
     _ = x         := neg_neg x

lemma L4 : -1 * (-1 - x) = 1 + x := by
  calc -1 * (-1 - x)
       = -1 * (-1 + -x)     := congr_arg (-1 * ·) (sub_eq_add_neg (-1) x)
     _ = -1 * -1 + -1 * -x  := left_distrib (-1) (-1) (-x)
     _ = 1 + -1 * -x        := congr_arg (· + (-1)*(-x)) L2
     _ = 1 + x              := congr_arg ( 1 + ·) L3

lemma L5 : |-1 * (-1 - x)| = |-1 - x| := by
  calc |-1 * (-1 - x)|
       = |-1| * |-1 - x| := abs_mul (-1) (-1 - x)
     _ = |1| * |-1 - x|  := congrArg (· * |-1 - x|) (abs_neg 1)
     _ = 1 * |-1 - x|    := congrArg (· * |-1 - x|) abs_one
     _ = |-1 - x|        := one_mul |-1 - x|

lemma L6 : (-1:ℝ)^(2*n) = 1 := by
  calc (-1:ℝ)^(2*n)
       = ((-1:ℝ)^2)^n := pow_mul (-1) 2 n
     _ = (1:ℝ)^n      := congr_arg ( · ^ n) neg_one_sq
     _ = 1            := one_pow n

lemma L7 : (-1:ℝ)^(2*n+1) = -1 := by
  calc (-1:ℝ)^(2*n+1)
       = (-1)^(2*n) * -1 := pow_succ (-1) (2 * n)
     _ = 1 * -1          := congr_arg (· * -1) L6
     _ = -1              := one_mul (-1)

lemma L8 : n ≤ 2 * n := by
  calc n
       = 1 * n := (one_mul n).symm
     _ ≤ 2 * n := Nat.mul_le_mul_right n one_le_two

lemma L9
  (hN : ∀ n ≥ N, |a n - x| < 1 / 2)
  : |a (2*N) - x| < 1 / 2 :=
hN (2*N) L8

lemma L10 : n ≤ 2 * n + 1 := by
  calc n
       ≤ 2 * n     := L8
     _ ≤ 2 * n + 1 := Nat.le_add_right (2 * n) 1

lemma L11
  (hN : ∀ n ≥ N, |a n - x| < 1 / 2)
  : |a (2*N+1) - x| < 1 / 2 :=
hN (2*N+1) L10

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a :=
by
  intro h
  -- h : SucConv a
  -- ⊢ False
  choose L hL using h
  -- L : ℝ
  -- hL : LimSuc a L
  choose N hN using hL (1/2) one_half_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1 / 2
  have h1 : (2:ℝ) < 1 := by calc
    2 = |2| :=
          abs_two.symm
    _ = |(1 - L) + (1 + L)| :=
          congrArg abs L1.symm
    _ = |(1 - L) + (-1)*(-1 - L)| :=
          congr_arg (abs ((1 - L) + ·)) L4.symm
    _ ≤ |1 - L| + |(-1)*(-1 - L)| :=
          abs_add_le (1 - L) (-1 * (-1 - L))
    _ = |1 - L| + |-1 - L| :=
          congr_arg (|1 - L| + ·) L5
    _ = |(-1:ℝ)^(2*N) - L| + |(-1:ℝ)^(2*N+1) - L|  :=
          congrArg₂ (|· - L| + |· - L|) L6.symm L7.symm
    _ = |a (2*N) - L| + |a (2*N+1) - L| :=
          congrArg₂ (· + ·)
            (congrArg (|· - L|) (ha (2*N)).symm)
            (congrArg (|· - L|) (ha (2*N+1)).symm)
    _ < 1 / 2 + 1 / 2 :=
          add_lt_add (L9 hN) (L11 hN)
    _ = 1 := add_halves 1
  have h2 : (1:ℝ) < 1 := lt_trans one_lt_two h1
  exact (lt_irrefl 1) h2

end Solucion2

-- 3ª demostración
-- ===============

namespace Solucion3

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a :=
by
  change SucConv a → False
  -- ⊢ SucConv a → False
  intro h
  -- h : SucConv a
  -- ⊢ False
  change ∃ L, LimSuc a L at h
  -- h : ∃ L, LimSuc a L
  choose L hL using h
  -- L : ℝ
  -- hL : LimSuc a L
  change ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε at hL
  -- hL : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε
  specialize hL (1/2)
  -- hL : 1 / 2 > 0 → ∃ N, ∀ n ≥ N, |a n - L| < 1 / 2
  have h0 : (0 : ℝ) < 1/2 := by norm_num
  specialize hL h0
  -- hL : ∃ N, ∀ n ≥ N, |a n - L| < 1 / 2
  choose N hN using hL
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1 / 2
  have h2N : N ≤ 2 * N := by bound
  have h2Np1 : N ≤ 2 * N + 1 := by bound
  have h1 : |a (2 * N) - L| < 1 / 2 := by apply hN (2 * N) h2N
  have h2 : |a (2 * N + 1) - L| < 1 / 2 := by apply hN (2 * N + 1) h2Np1
  have h3 : a (2 * N) = (-1) ^ (2 * N) := by apply ha (2 * N)
  have h4 : a (2 * N + 1) = (-1) ^ (2 * N + 1) := by apply ha (2 * N + 1)
  rewrite [h3] at h1
  -- h1 : |(-1) ^ (2 * N) - L| < 1 / 2
  rewrite [h4] at h2
  -- h2 : |(-1) ^ (2 * N + 1) - L| < 1 / 2
  have h5 : (-1 : ℝ) ^ (2 * N) = 1 := by bound
  rewrite [h5] at h1
  -- h1 : |1 - L| < 1 / 2
  have h6 : (-1 : ℝ) ^ (2 * N + 1) = -1 := by grind
  rewrite [h6] at h2
  -- h2 : |-1 - L| < 1 / 2
  have h7 : (2 : ℝ) = |2| := by norm_num
  have h8 : |(2 : ℝ)| = |1 - (-1)| := by ring_nf
  have h9 : |1 - (-1)| = |(1 - L) + (L - (-1))| := by noncomm_ring
  have h10 : |(1 - L) + (L - (-1))| ≤ |(1 - L)| + |(L - (-1))| :=
    abs_add_le (1 - L) (L - -1)
  have h11 : |(L - (-1))| = |-((-1) - L)| := by ring_nf
  have h12 : |-((-1) - L)| = |((-1) - L)| := by apply abs_neg
  have h13 : (2 : ℝ) < 1/2 + 1/2 := by
    linarith [h8, h9, h10, h11, h12, h7, h1, h2]
  norm_num at h13

end Solucion3

-- 4ª solución (de Esteban Martínez Vañó)
-- ======================================

namespace Solucion4

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a :=
by
  intro a_conv
  -- a_conv : SucConv a
  -- ⊢ False
  rcases a_conv with ⟨L, a_lim⟩
  -- L : ℝ
  -- a_lim : LimSuc a L
  have eps_one := a_lim 1 (by norm_num)
  -- eps_one : ∃ N, ∀ n ≥ N, |a n - L| < 1
  rcases eps_one with ⟨N, hN⟩
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  by_cases hL: (L ≤ 0)
  · -- hL : L ≤ 0
    have h := hN (2*N) (by linarith)
    -- h : |a (2 * N) - L| < 1
    rw [ha, neg_one_pow_eq_pow_mod_two, Nat.mul_mod_right, pow_zero, abs_lt] at h
    -- h : -1 < 1 - L ∧ 1 - L < 1
    linarith
  · -- hL : ¬L ≤ 0
    rw [not_le] at hL
    -- hL : 0 < L
    have h := hN (2*N + 1) (by linarith)
    -- h : |a (2 * N + 1) - L| < 1
    rw [ha, neg_one_pow_eq_pow_mod_two, Nat.mul_add_mod, Nat.mod_succ, pow_one, abs_lt] at h
    -- h : -1 < -1 - L ∧ -1 - L < 1
    linarith

end Solucion4

-- 5ª solución (refactorización de la 4ª)
-- ======================================

namespace Solucion5

example
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬ SucConv a := by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : LimSuc a L
  -- ⊢ False
  obtain ⟨N, hN⟩ := hL 1 one_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  have h1 := hN (2 * N) (by omega)
  -- h1 : |a (2 * N) - L| < 1
  have h2 := hN (2 * N + 1) (by omega)
  -- h2 : |a (2 * N + 1) - L| < 1
  simp [ha, neg_one_pow_eq_pow_mod_two, abs_lt] at h1 h2
  -- h1 : L < 1 + 1 ∧ 0 < L
  -- h2 : L < 0 ∧ -1 - L < 1
  linarith

end Solucion5
