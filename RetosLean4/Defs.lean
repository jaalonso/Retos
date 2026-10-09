-- Defs.lean
-- Definiciones usadas en los retos de demostración en Lean 4.
-- -----------------------------------------------------------

import Mathlib.Basic.Real.Basic

-- L es el límite de la sucesión a.
def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

-- La sucesión a es convergente.
def SucConvergente (a : ℕ → ℝ) : Prop :=
  ∃ L, LimSuc a L

-- La sucesión a está acotada.
def SucAcotada (a : ℕ → ℝ) : Prop :=
  ∃ M, ∀ n, |a n| ≤ M

-- M es una cota superior de la sucesión a.
def CotaSup (a : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ n, a n ≤ M

-- a es una sucesión de Cauchy,
def SucCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, |a p - a q| < ε

-- φ es una función de extracción.
def extraccion (φ : ℕ → ℕ):=
  StrictMono φ

-- v es una subsucesión de u.
def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ
