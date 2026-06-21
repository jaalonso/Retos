-- Reto_6.lean
-- Soluciones de 6º reto (14 de junio de 2026).
-- Teorema del emparedado: Si aₙ y cₙ convergen a L y aₙ ≤ bₙ ≤ cₙ para
--   todo n, entonces bₙ converge a L.
-- Sevilla, 14-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si las sucesiones a y c convergen a L, y b está
-- comprimida entre a y c (es decir, aₙ ≤ bₙ ≤ cₙ para todo n), entonces
-- b también converge a L.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε > 0. Tenemos que demostrar que existe un N tal que,
--    ∀ n ≥ N, |bₙ - L| < ε                                          (1)
--
-- Puesto que a y c convergen a L, existen N₁ y ℕ₂ tales que
--    ∀ n ≥ N₁, |aₙ - L| < ε                                         (2)
--    ∀ n ≥ N₂, |cₙ - L| < ε                                         (3)
-- Sea
--    N = máx(N₁, ℕ₂).                                               (4)
-- Para demostrar (1), sea n ≥ N. Por  (4), se tiene que
--    n ≥ N₁
--    n ≥ N₂
-- Luego, usando (2) y (3), se tiene que
--    |aₙ - L| < ε
--    |cₙ - L| < ε
-- de donde se deduce que
--    - ε < aₙ - L < ε                                               (5)
--    - ε < bₙ - L < ε                                               (6)
-- Luego,
--    -ε < aₙ - L   [por (5)]
--       ≤ bₙ - L   [por hipótesis de b]
--       ≤ cₙ - L   [por hipótesis de b]
--       < ε        [por (6)]
-- Por tanto,
--    -ε < bₙ - L < ε
-- y, finalmente,
--    |bₙ - L| < ε

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable {a b c : ℕ → ℝ}
variable {L : ℝ}

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  exact ⟨max Na Nc, by grind⟩

-- 2ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    calc -ε
       < a n - L := by grind
     _ ≤ b n - L := by grind
  · -- ⊢ b n - L < ε
    calc b n - L
       ≤ c n - L := by grind
     _ < ε       := by grind

-- 3ª demostración
-- ===============

example
    (ha : LimSuc a L)
    (hc : LimSuc c L)
    (hab : ∀ n, a n ≤ b n)
    (hbc : ∀ n, b n ≤ c n) :
    LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna := hNa n (le_of_max_le_left hn)
  have hnc := hNc n (le_of_max_le_right hn)
  rw [abs_lt] at hna hnc ⊢
  -- hna : -ε < a n - L ∧ a n - L < ε
  -- hnc : -ε < c n - L ∧ c n - L < ε
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  exact ⟨by linarith [hab n], by linarith [hbc n]⟩

-- 4ª demostración
-- ===============

example
    (ha : LimSuc a L)
    (hc : LimSuc c L)
    (hab : ∀ n, a n ≤ b n)
    (hbc : ∀ n, b n ≤ c n)
    : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna := hNa n (le_of_max_le_left hn)
  have hnc := hNc n (le_of_max_le_right hn)
  rw [abs_lt] at hna hnc ⊢
  -- hna : -ε < a n - L ∧ a n - L < ε
  -- hnc : -ε < c n - L ∧ c n - L < ε
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  refine ⟨?_, ?_⟩
  · -- ⊢ -ε < b n - L
    calc -ε
         < a n - L := hna.1
       _ ≤ b n - L := by linarith [hab n]
  · calc b n - L
         ≤ c n - L := by linarith [hbc n]
       _ < ε       := hnc.2

-- 5ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna : Na ≤ n := le_of_max_le_left hn
  have hnc : Nc ≤ n := le_of_max_le_right hn
  have hNa : |a n - L| < ε := hNa n hna
  have hNc : |c n - L| < ε := hNc n hnc
  rewrite [abs_lt] at hNa
  -- hNa : -ε < a n - L ∧ a n - L < ε
  rewrite [abs_lt] at hNc
  -- hNc : -ε < c n - L ∧ c n - L < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    calc -ε
       < a n - L := hNa.1
     _ ≤ b n - L := sub_le_sub_right (hab n) L
  · -- ⊢ b n - L < ε
    calc b n - L
       ≤ c n - L := sub_le_sub_right (hbc n) L
     _ < ε       := hNc.2

-- 6ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna : Na ≤ n := le_of_max_le_left hn
  have hnc : Nc ≤ n := le_of_max_le_right hn
  have hNa : |a n - L| < ε := hNa n hna
  have hNc : |c n - L| < ε := hNc n hnc
  rewrite [abs_lt] at hNa
  -- hNa : -ε < a n - L ∧ a n - L < ε
  rewrite [abs_lt] at hNc
  -- hNc : -ε < c n - L ∧ c n - L < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  split_ands
  · -- ⊢ -ε < b n - L
    have hab : a n ≤ b n := hab n
    linarith
  · -- ⊢ b n - L < ε
    have hbc : b n ≤ c n := hbc n
    linarith

-- 7ª demostración
-- ===============

example
    (ha : LimSuc a L)
    (hc : LimSuc c L)
    (hab : ∀ n, a n ≤ b n)
    (hbc : ∀ n, b n ≤ c n)
    : LimSuc b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, ?_⟩
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna : n ≥ Na := le_of_max_le_left hn
  have hnc : n ≥ Nc := le_of_max_le_right hn
  have ha' : |a n - L| < ε := hNa n hna
  have hc' : |c n - L| < ε := hNc n hnc
  rw [abs_lt] at ha' hc' ⊢
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    have h1 : -ε < a n - L := ha'.1
    have h2 : a n - L ≤ b n - L := by
      linarith [hab n]
    linarith
  · -- ⊢ b n - L < ε
    have h1 : b n - L ≤ c n - L := by
      linarith [hbc n]
    have h2 : c n - L < ε := hc'.2
    linarith

-- 8ª demostración
-- ===============

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L :=
by
  -- 1. Empezamos con la definición de límite para b
  intro ε hε

  -- 2. Obtenemos los N de las sucesiones a y c para este ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  obtain ⟨Nc, hNc⟩ := hc ε hε

  -- 3. Elegimos el máximo de ambos N
  use max Na Nc
  intro n hn

  -- 4. Extraemos las desigualdades de los valores absolutos
  -- abs_lt es una propiedad que dice: |x| < ε ↔ -ε < x < ε
  specialize hNa n (le_of_max_le_left hn)
  specialize hNc n (le_of_max_le_right hn)
  rw [abs_lt] at hNa hNc
  rw [abs_lt]

  -- 5. Demostramos las dos partes de: -ε < b n - L < ε
  constructor
  · -- Caso -ε < b n - L
    calc -ε < a n - L := hNa.1
         _  ≤ b n - L := sub_le_sub_right (hab n) L
  · -- Caso b n - L < ε
    calc b n - L ≤ c n - L := sub_le_sub_right (hbc n) L
         _       < ε       := hNc.2

-- 9ª solución
-- ===========

example
  (ha : LimSuc a L)
  (hc : LimSuc c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : LimSuc b L := by
  -- 1. Introducimos ε > 0
  intro ε hε

  -- 2. Obtenemos los índices N₁ y N₂ para las sucesiones a y c
  obtain ⟨N₁, hN₁⟩ := ha ε hε
  obtain ⟨N₂, hN₂⟩ := hc ε hε

  -- 3. Proponemos como índice el máximo de N₁ y N₂
  use max N₁ N₂

  -- 4. Tomamos un n cualquiera mayor o igual que este máximo
  intro n hn

  -- Descomponemos la condición n ≥ max N₁ N₂ en n ≥ N₁ y n ≥ N₂
  have h₁ : n ≥ N₁ := le_of_max_le_left hn
  have h₂ : n ≥ N₂ := le_of_max_le_right hn

  -- Aplicamos las hipótesis de convergencia para obtener las cotas de a y c
  have ha' : |a n - L| < ε := hN₁ n h₁
  have hc' : |c n - L| < ε := hN₂ n h₂

  -- Reescribimos los valores absolutos como desigualdades dobles (-ε < x ∧ x < ε)
  rw [abs_lt] at ha' hc'
  rw [abs_lt]

  -- Debemos probar dos cosas: -ε < b n - L  y  b n - L < ε
  constructor
  · -- Primera parte: -ε < b n - L
    -- Sabemos que a n ≤ b n, por lo tanto a n - L ≤ b n - L
    have h_ab : a n - L ≤ b n - L := sub_le_sub_right (hab n) L
    -- Como -ε < a n - L y a n - L ≤ b n - L, entonces -ε < b n - L
    exact lt_of_lt_of_le ha'.1 h_ab

  · -- Segunda parte: b n - L < ε
    -- Sabemos que b n ≤ c n, por lo tanto b n - L ≤ c n - L
    have h_bc : b n - L ≤ c n - L := sub_le_sub_right (hbc n) L
    -- Como b n - L ≤ c n - L y c n - L < ε, entonces b n - L < ε
    exact lt_of_le_of_lt h_bc hc'.2
