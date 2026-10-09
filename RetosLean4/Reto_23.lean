-- Reto_3.lean
-- La sucesión 1, -1, 1, -1,... no es convergente (a partir del Reto 22).
-- Sevilla, 12-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- El reto de esta semana consiste en demostrar en Lean 4, usando
-- elreto anterior, que la sucesión 1, -1, 1, -1,... no es
-- convergente. Para ello, completar la siguiente teoría:
--    import Mathlib.Data.Real.Basic
--    import Mathlib.Tactic
--
--    -- a converge a L
--    def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    -- La sucesión a es convergente
--    def SucConvergente (a : ℕ → ℝ) : Prop :=
--      ∃ L, LimSuc a L
--
--    -- φ es una función de extracción.
--    def extraccion (φ : ℕ → ℕ) : Prop :=
--      StrictMono φ
--
--    -- b es una subsucesión de a.
--    def subsucesion (b a : ℕ → ℝ) : Prop :=
--      ∃ φ, extraccion φ ∧ b = a ∘ φ
--
--    variable {a b₁ b₂ : ℕ → ℝ}
--    variable {L L₁ L₂ M : ℝ}
--
--    example
--      (hb₁ : subsucesion b₁ a)
--      (hL₁ : LimSuc b₁ L₁)
--      (hb₂ : subsucesion b₂ a)
--      (hL₂ : LimSuc b₂ L₂)
--      (h : L₁ ≠ L₂)
--      : ¬SucConvergente a :=
--    by sorry
-- ---------------------------------------------------------------

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import RetosLean4.Defs -- LimSuc, SucConvergente, extraccion, subsucesion
import RetosLean4.Reto_22 -- CS_no_convergencia

variable {a b₁ b₂ : ℕ → ℝ}
variable {L L₁ L₂ M : ℝ}

example
  (ha : ∀ n, a n = (-1)^n)
  : ¬SucConvergente a :=
by
  set φ₁ := fun n => 2 * n
  have h1 : extraccion φ₁ := by
    intro i j hij
    -- i j : ℕ
    -- hij : i < j
    -- ⊢ φ₁ i < φ₁ j
    unfold φ₁
    -- ⊢ 2 * i < 2 * j
    gcongr
  set b₁ := a ∘ φ₁ with hb₁
  have hb₁ : subsucesion b₁ a := ⟨φ₁, h1, hb₁⟩
  have hL₁ : LimSuc b₁ 1 := by sorry
  set φ₂ := fun n => 2 * n + 1
  have h2 : extraccion φ₂ := by
    intro i j hij
    -- i j : ℕ
    -- hij : i < j
    -- ⊢ φ₁ i < φ₁ j
    unfold φ₂
    -- ⊢ 2 * i + 1 < 2 * j + 1
    gcongr
  set b₂ := a ∘ φ₂ with hb₂
  have hb₂ : subsucesion b₂ a := ⟨φ₂, h2, hb₂⟩
  have hL₂ : LimSuc b₂ (-1) := by sorry
  have h3 : (1:ℝ) ≠ -1 := by norm_num
  exact CS_no_convergencia hb₁ hL₁ hb₂ hL₂ h3
