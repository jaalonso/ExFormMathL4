-- C04_Sets/Pset2.lean
-- Problem set 2
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study results about the universal set and the
-- empty set
--
-- It is based on [Section04functions/Sheet2.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

open Set

variable (X : Type)
variable (A B C D E : Set X)
variable (x y z : X)

open Set

-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que
--    x ∈ univ
-- ---------------------------------------------------------------------

example : x ∈ (univ : Set X) :=
by trivial

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    x ∉ ∅
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : x ∉ (∅ : Set X) :=
by
  intro h
  -- h : x ∈ ∅
  -- ⊢ False
  cases h

-- 2ª demostración
-- ===============

example : x ∉ (∅ : Set X) :=
by exact id

-- 3ª demostración
-- ===============

example : x ∉ (∅ : Set X) :=
by aesop

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    A ⊆ univ
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : A ⊆ univ :=
by
  rw [subset_def]
  -- ⊢ ∀ x ∈ A, x ∈ univ
  intro x _hxA
  -- x : X
  -- _hxA : x ∈ A
  -- ⊢ x ∈ univ
  trivial

-- 2ª demostración
-- ===============

example : A ⊆ univ :=
fun _ _ => trivial

-- 3ª demostración
-- ===============

example : A ⊆ univ :=
by aesop

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    ∅ ⊆ A
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : ∅ ⊆ A :=
by
  rw [subset_def]
  -- ⊢ ∀ x ∈ ∅, x ∈ A
  intro x hx
  -- x : X
  -- hx : x ∈ ∅
  -- ⊢ x ∈ A
  cases hx

-- 2ª demostración
-- ===============

example : ∅ ⊆ A :=
empty_subset A

-- 3ª demostración
-- ===============

example : ∅ ⊆ A :=
by aesop
