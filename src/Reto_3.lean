-- Reto_3.lean
-- Soluciones de 2º reto (24 de mayo de 2026).
-- Si aₙ converge a L, entonces 2aₙ converge a 2L.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si aₙ converge a L, entonces 2aₙ converge a 2L.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea bₙ la suceción definida por
--    bₙ = 2aₙ                                                        (1)
-- Tenemos que demostrar que para cada ε > 0, existe un N ∈ ℕ tal que
--    ∀ n ≥ N, |bₙ - 2L| < ε                                          (2)
-- Puesto que aₙ converge a L, existe un N ∈ ℕ tal que
--    ∀ n ≥ N, |aₙ - L| < ε/2                                         (3)
-- Veamos que N también cumple (2). En efecto, sea n ≥ N. Entonces
--    |bₙ - 2L| = |2aₙ - 2L|     [por (1)]
--              = 2|aₙ - L|
--              < 2ε/2           [por (3)]
--              = ε

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (a b : ℕ → ℝ)
variable (L : ℝ)

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

-- 1ª solución
-- ===========

namespace Solucion1

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

end Solucion1

-- 2ª solución
-- ===========

namespace Solucion2

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  have hε2_pos : ε / 2 > 0 := by linarith
  rcases ha (ε / 2) hε2_pos with ⟨N, hN⟩
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  have ha_n : |a n - L| < ε / 2 := hN n hn
  have hb_eq : b n = 2 * a n := hb n
  calc
    |b n - 2 * L|
      = |2 * a n - 2 * L|     := by rw [hb_eq]
    _ = |2 * (a n - L)|       := by ring_nf
    _ = |(2 : ℝ)| * |a n - L| := by rw [abs_mul]
    _ = 2 * |a n - L|         := by norm_num
    _ < 2 * (ε / 2) := by
        apply mul_lt_mul_of_pos_left ha_n
        -- ⊢ 0 < 2
        norm_num
    _ = ε                     := by ring

end Solucion2

-- 3ª solución
-- ===========

namespace Solucion3

example
  (L : ℝ)
  (b : ℕ → ℝ)
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  unfold LimSuc at ha ⊢
  -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
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
  have h1 : b n = 2 * a n := hb n
  calc
    |b n - 2 * L|
      = |2 * a n - 2 * L| := by rw [h1]
    _ = |2 * (a n - L)|   := by ring_nf
    _ = |2| * |a n - L|   := by rw [abs_mul]
    _ = 2 * |a n - L|     := by norm_num
    _ < 2 * (ε / 2)       := by
          apply mul_lt_mul_of_pos_left
          -- ⊢ |a n - L| < ε / 2
          exact hN n hn
          -- ⊢ 0 < 2
          norm_num
    _ = ε                 := by ring

end Solucion3

-- 4ª solución
-- ===========

namespace Solucion4

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  -- Sea ε > 0
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  -- Consideramos ε/2, que también es positivo
  have hε2 : ε / 2 > 0 := by linarith
  -- Por la hipótesis de convergencia de a_n, existe un N tal que...
  rcases ha (ε / 2) hε2 with ⟨N, hN⟩
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  -- Usamos ese mismo N para la sucesión b_n
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  -- Sustituimos la definición de b_n
  rw [hb n]
  -- ⊢ |2 * a n - 2 * L| < ε
  -- Factorizamos el 2 dentro del valor absoluto: |2*a n - 2*L| = |2 * (a n - L)|
  rw [← mul_sub]
  -- ⊢ |2 * (a n - L)| < ε
  -- Usamos la propiedad del valor absoluto del producto: |x * y| = |x| * |y|
  rw [abs_mul]
  -- ⊢ |2| * |a n - L| < ε
  -- Como |2| = 2, simplificamos
  have h2 : |(2 : ℝ)| = 2 := abs_of_pos (by linarith)
  rw [h2]
  -- ⊢ 2 * |a n - L| < ε
  -- Finalmente, como |a n - L| < ε/2, entonces 2 * |a n - L| < ε
  specialize hN n hn
  -- hN : |a n - L| < ε / 2
  linarith

end Solucion4

-- 5ª solución
-- ===========

namespace Solucion5

example
  (b : ℕ → ℝ)
  (L : ℝ)
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  -- Sea ε > 0 arbitrario
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε

  -- Como ε > 0, entonces ε/2 > 0
  have hε2 : ε / 2 > 0 := half_pos hε

  -- Aplicamos la convergencia de aₙ → L con ε/2
  obtain ⟨N, hN⟩ := ha (ε / 2) hε2
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2

  -- Proponemos ese mismo N para la sucesión bₙ
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε

  -- Por la elección de N, sabemos que |a n - L| < ε/2
  have han : |a n - L| < ε / 2 := hN n hn

  -- Cadena de igualdades y desigualdades para concluir
  calc
    |b n - 2 * L| = |2 * a n - 2 * L| := by rw [hb]
    _             = |2 * (a n - L)|   := by rw [mul_sub]
    _             = |2| * |a n - L|   := by rw [abs_mul]
    _             = 2 * |a n - L|     := by rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    _             < 2 * (ε / 2)       := by gcongr
    _             = ε                 := by ring

end Solucion5

-- 6ª solución
-- ===========

namespace Solucion6

example (ha : LimSuc a L) (hb : ∀ n, b n = 2 * a n) : LimSuc b (2 * L) := by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  -- We work with ε/2 because multiplying by 2 will bring us back to ε.
  have h₁ : (ε / 2 : ℝ) > 0 := by linarith
  -- Obtain N from the hypothesis that aₙ → L using ε/2.
  obtain ⟨N, hN⟩ := ha (ε / 2) h₁
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  -- For n ≥ N we have |aₙ - L| < ε/2.
  have h₂ : |a n - L| < ε / 2 := hN n hn
  -- By hypothesis bₙ = 2·aₙ.
  have h₃ : b n = 2 * a n := hb n
  -- Compute |bₙ - 2L| = 2·|aₙ - L|.
  have h₄ : |b n - 2 * L| = 2 * |a n - L| := by
    calc
      |b n - 2 * L|
        = |(2 * a n) - 2 * L| := by rw [h₃]
      _ = |2 * (a n - L)| := by ring_nf
      _ = 2 * |a n - L| := by
            rw [abs_mul]
            -- ⊢ |2| * |a n - L| = 2 * |a n - L|
            ring_nf
  -- Finally, show that |bₙ - 2L| < ε.
  calc
    |b n - 2 * L|
      = 2 * |a n - L| := h₄
    _ < 2 * (ε / 2)   := by gcongr
    _ = ε             := by ring

end Solucion6


-- 7ª solución
-- ===========

namespace Solucion7

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < ε
  -- Elegimos ε/2 > 0 para poder regresar a ε al multiplicar por 2.
  have hε2 : (ε / 2 : ℝ) > 0 := by linarith
  -- Aplicamos la hipótesis de convergencia a ε/2.
  obtain ⟨N, hN⟩ := ha (ε / 2) hε2
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < ε / 2
  refine ⟨N, ?_⟩
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  -- Para n ≥ N se tiene |aₙ−L| < ε/2.
  have h_an : |a n - L| < ε / 2 := hN n hn
  -- La definición de bₙ.
  have hb_eq : b n = 2 * a n := hb n
  -- Calculamos |bₙ−2L| = 2·|aₙ−L|.
  have h_eq : |b n - 2 * L| = 2 * |a n - L| := by
    calc
      |b n - 2 * L|
        = |(2 * a n) - 2 * L| := by rw [hb_eq]
      _ = |2 * (a n - L)|     := by ring_nf
      _ = 2 * |a n - L|       := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  -- Con ello obtenemos la cota deseada.
  have h_lt : |b n - 2 * L| < ε := by
    calc
      |b n - 2 * L|
        = 2 * |a n - L| := h_eq
      _ < 2 * (ε / 2)   := by
            -- multiplicamos la desigualdad anterior por 2 (>0)
            apply mul_lt_mul_of_pos_left h_an
            -- ⊢ 0 < 2
            norm_num
      _ = ε             := by field_simp
  exact h_lt

end Solucion7

-- 8ª solución
-- ===========

namespace Solucion8

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

end Solucion8

-- 9ª solución
-- ===========

namespace Solucion9

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro eps epos
  -- eps : ℝ
  -- epos : eps > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < eps
  rcases ha (eps/2) (half_pos epos) with ⟨N, hN⟩
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < eps / 2
  use N
  -- ⊢ ∀ n ≥ N, |b n - 2 * L| < eps
  intro n ngeqN
  -- n : ℕ
  -- ngeqN : n ≥ N
  -- ⊢ |b n - 2 * L| < eps
  rw [hb,
      -- ⊢ |2 * a n - 2 * L| < eps
      ← mul_sub,
      -- ⊢ |2 * (a n - L)| < eps
      abs_mul,
      -- ⊢ |2| * |a n - L| < eps
      Nat.abs_ofNat]
  -- ⊢ 2 * |a n - L| < eps
  linarith [hN n ngeqN]

end Solucion9

-- 10ª solución (refactorización de la 9ª)
-- =======================================

namespace Solucion10

example
  (ha : LimSuc a L)
  (hb : ∀ n, b n = 2 * a n)
  : LimSuc b (2 * L) :=
by
  intro eps epos
  -- eps : ℝ
  -- epos : eps > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - 2 * L| < eps
  obtain ⟨N, hN⟩ := ha (eps/2) (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < eps / 2
  refine ⟨N, fun n ngeqN => by grind⟩

end Solucion10
