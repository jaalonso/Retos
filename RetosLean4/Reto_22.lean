-- Reto_22.lean
-- Subsucesiones con límites distintos implican no convergencia.
-- Sevilla, 5-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- El reto de esta semana consiste en demostrar en Lean 4 que si
-- una sucesión tiene dos subsucesiones con límites distintos,
-- entonces la sucesión no es convergente. Para ello, completar la
-- siguiente teoría:
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
import RetosLean4.Reto_9 -- unicidad_limite
import RetosLean4.Reto_21 -- limite_subsucesion

variable {a b₁ b₂ : ℕ → ℝ}
variable {L L₁ L₂ M : ℝ}

theorem CS_no_convergencia
  (hb₁ : subsucesion b₁ a)
  (hL₁ : LimSuc b₁ L₁)
  (hb₂ : subsucesion b₂ a)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  intro h1
  -- h1 : SucConvergente a
  -- ⊢ False
  apply h
  -- ⊢ L₁ = L₂
  obtain ⟨L, hL⟩ := h1
  -- L : ℝ
  -- hL : LimSac u L
  have h2 : LimSuc b₁ L := limite_subsucesion hb₁ hL
  have h3 : LimSuc b₂ L := limite_subsucesion hb₂ hL
  calc L₁
       = L  := unicidad_limite hL₁ h2
     _ = L₂ := unicidad_limite h3 hL₂
