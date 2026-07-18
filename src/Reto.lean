-- -----------------------------------------------------------
-- Demostrar que si una sucesión aₙ converge tanto a L como a
-- M, entonces L = M.
-- -----------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

variable {a : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª demostración
-- ===============

example
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  set ε := |L - M|
  obtain ⟨k1, hk1⟩ := hL (ε/2) (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  set k := max  k1 k2
  apply lt_irrefl ε
  -- ⊢ ε < ε
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + (a k - a k)| := by grind
       _ = |(L - a k) + (a k - M)| := by grind
       _ ≤ |L - a k| + |a k - M|   := by grind
       _ = |a k - L| + |a k - M|   := by grind
       _ < ε/2 + ε/2               := by grind
       _ = ε                       := by grind

-- 2ª demostración
-- ===============

example
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  set ε := |L - M|
  have h1 : ε/2 > 0 := by positivity
  obtain ⟨k1, hk1⟩ := hL (ε/2) h1
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) h1
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  set k := max k1 k2
  have h3 : k ≥ k1 := by bound
  have h4 : k ≥ k2 := by bound
  have h5 : |a k - L| < ε/2 := hk1 k h3
  have h6 : |a k - M| < ε/2 := hk2 k h4
  apply lt_irrefl ε
  -- ⊢ ε < ε
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + (a k - a k)| := by noncomm_ring
       _ = |(L - a k) + (a k - M)| := by noncomm_ring
       _ ≤ |L - a k| + |a k - M|   := abs_add_le _ _
       _ = |a k - L| + |a k - M|   := by congr 1 ; exact abs_sub_comm L (a k)
       _ < ε/2 + ε/2               := add_lt_add h5 h6
       _ = ε                       := by ring

-- 3ª demostración
-- ===============

example
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  have h1 : 0 < ε/2 := half_pos (abs_sub_pos.mpr h)
  obtain ⟨k1, hk1⟩ := hL (ε/2) h1
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) h1
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  have h2 : k ≥ k1 := le_max_left k1 k2
  have h3 : k ≥ k2 := le_max_right k1 k2
  have h4 : |a k - L| < ε/2 := hk1 k h2
  have h5 : |a k - M| < ε/2 := hk2 k h3
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + 0|           := congrArg abs (add_zero (L - M)).symm
       _ = |(L - M) + (a k - a k)| := congrArg (|(L - M) + ·|) (sub_self (a k)).symm
       _ = |(L - a k) + (a k - M)| := congrArg abs (by ring)
       _ ≤ |L - a k| + |a k - M|   := abs_add_le (L - a k) (a k - M)
       _ = |a k - L| + |a k - M|   := congrArg (· + |a k - M|) (abs_sub_comm L (a k))
       _ < ε/2 + ε/2               := add_lt_add h4 h5
       _ = ε                       := add_halves ε
