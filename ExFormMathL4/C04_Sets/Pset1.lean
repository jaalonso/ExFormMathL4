-- C04_Sets/Pset1.lean
-- Problem set 1
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study results about inclusion in sets.
--
-- It is based on [Section04functions/Sheet1.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

namespace Section4sheet1

variable (X : Type)
variable (A B C D : Set X)

theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

variable {x : X}

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Iff.rfl

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    A ⊆ A
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : A ⊆ A :=
by
  rw [subset_def]
  -- x : X
  -- ⊢ ∀ x ∈ A, x ∈ A
  intro x hx
  -- x : X
  -- hx : x ∈ A
  -- ⊢ x ∈ A
  exact hx

-- Proof 2
-- =======

example : A ⊆ A :=
by
  exact fun ⦃a⦄ a => a

-- Comentario de JA: La 2ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 3
-- =======

example : A ⊆ A :=
fun _ a => a

-- Proof 4
-- =======

example : A ⊆ A :=
by
  simp [subset_def]

-- Proof 5
-- =======

example : A ⊆ A :=
by
  simp

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    A ⊆ B → B ⊆ C → A ⊆ C
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : A ⊆ B → B ⊆ C → A ⊆ C :=
by
  intro hAsB hBsC
  -- hAsB : A ⊆ B
  -- hBsC : B ⊆ C
  -- ⊢ A ⊆ C
  rw [subset_def] at *
  -- hAsB : ∀ x ∈ A, x ∈ B
  -- hBsC : ∀ x ∈ B, x ∈ C
  -- ⊢ ∀ x ∈ A, x ∈ C
  intro x hxeA
  -- x : X
  -- hxeA : x ∈ A
  -- ⊢ x ∈ C
  apply hAsB at hxeA
  -- hxeA : x ∈ B
  apply hBsC at hxeA
  -- hxeA : x ∈ C
  exact hxeA

-- Proof 2
-- =======

example : A ⊆ B → B ⊆ C → A ⊆ C := by
  exact fun a a_1 ⦃a_2⦄ a_3 => a_1 (a a_3)

-- Proof 3
-- =======

example : A ⊆ B → B ⊆ C → A ⊆ C :=
fun a a_1 _ a_3 => a_1 (a a_3)

-- Proof 4
-- =======

example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAsB hBsC
  -- hAsB : A ⊆ B
  -- hBsC : B ⊆ C
  -- ⊢ A ⊆ C
  rw [subset_def] at *
  -- hAsB : ∀ x ∈ A, x ∈ B
  -- hBsC : ∀ x ∈ B, x ∈ C
  -- ⊢ ∀ x ∈ A, x ∈ C
  intro x hxeA
  -- x : X
  -- hxeA : x ∈ A
  -- ⊢ x ∈ C
  apply hBsC
  -- ⊢ x ∈ B
  apply hAsB
  -- ⊢ x ∈ A
  exact hxeA

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    A ⊆ A ∪ B
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : A ⊆ A ∪ B :=
by
  rw [subset_def]
  -- x : X
  -- ⊢ ∀ x ∈ A, x ∈ A ∪ B
  intro x hxeA
  -- x : X
  -- hxeA : x ∈ A
  -- ⊢ x ∈ A ∪ B
  rw [mem_union_iff]
  -- ⊢ x ∈ A ∨ x ∈ B
  left
  -- ⊢ x ∈ A
  exact hxeA

-- Proof 2
-- =======

example : A ⊆ A ∪ B :=
by
  exact Set.subset_union_left

-- Comentario de JA: La 2ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 3
-- =======

example : A ⊆ A ∪ B :=
Set.subset_union_left

-- Proof 4
-- =======

example : A ⊆ A ∪ B :=
fun _ => Or.inl

-- Proof 5
-- =======

example : A ⊆ A ∪ B :=
by simp

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    A ∩ B ⊆ A
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : A ∩ B ⊆ A :=
by
  rw [subset_def]
  -- x : X
  -- ⊢ ∀ x ∈ A ∩ B, x ∈ A
  intro x h_x_in_AyB
  -- x : X
  -- h_x_in_AyB : x ∈ A ∩ B
  -- ⊢ x ∈ A
  rw [mem_inter_iff] at h_x_in_AyB
  -- h_x_in_AyB : x ∈ A ∧ x ∈ B
  cases' h_x_in_AyB with hA hB
  -- hA : x ∈ A
  -- hB : x ∈ B
  exact hA

-- Proof 2
-- =======

example : A ∩ B ⊆ A :=
Set.inter_subset_left

-- Proof 3
-- =======

example : A ∩ B ⊆ A :=
by
  simp [subset_def, mem_inter_iff]
  -- ⊢ ∀ x ∈ A, x ∈ B → x ∈ A
  intro x hxA _hxB
  -- x : X
  -- hxA : x ∈ A
  -- _hxB : x ∈ B
  -- ⊢ x ∈ A
  exact hxA

-- Proof 4
-- =======

example : A ∩ B ⊆ A :=
fun _ => And.left

-- Proof 5
-- =======

example : A ∩ B ⊆ A :=
by simp

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    A ⊆ B → A ⊆ C → A ⊆ B ∩ C
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C :=
by
  intro h_A_in_B h_A_in_C
  -- h_A_in_B : A ⊆ B
  -- h_A_in_C : A ⊆ C
  -- ⊢ A ⊆ B ∩ C
  rw [subset_def] at *
  -- h_A_in_B : ∀ x ∈ A, x ∈ B
  -- h_A_in_C : ∀ x ∈ A, x ∈ C
  -- ⊢ ∀ x ∈ A, x ∈ B ∩ C
  intro x x_in_A
  -- x : X
  -- x_in_A : x ∈ A
  -- ⊢ x ∈ B ∩ C
  rw [mem_inter_iff]
  -- ⊢ x ∈ B ∧ x ∈ C
  constructor
  . -- ⊢ x ∈ B
    apply h_A_in_B at x_in_A
    -- x_in_A : x ∈ B
    exact x_in_A
  . -- ⊢ x ∈ C
    apply h_A_in_C at x_in_A
    -- x_in_A : x ∈ C
    exact x_in_A

-- Proof 2
-- =======

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C :=
Set.subset_inter

-- Proof 3
-- =======

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C :=
by
  intro hAsB hAsC
  -- hAsB : A ⊆ B
  -- hAsC : A ⊆ C
  -- ⊢ A ⊆ B ∩ C
  simp [subset_def, mem_inter_iff] at *
  -- hAsB : ∀ x ∈ A, x ∈ B
  -- hAsC : ∀ x ∈ A, x ∈ C
  -- ⊢ ∀ x ∈ A, x ∈ B ∧ x ∈ C
  intro x hxA
  -- x : X
  -- hxA : x ∈ A
  -- ⊢ x ∈ B ∧ x ∈ C
  specialize hAsB x hxA
  -- hAsB : x ∈ B
  specialize hAsC x hxA
  -- hAsC : x ∈ C
  exact ⟨hAsB, hAsC⟩

-- Proof 4
-- =======

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C :=
by
  intro hAsB hAsC
  -- hAsB : A ⊆ B
  -- hAsC : A ⊆ C
  -- ⊢ A ⊆ B ∩ C
  intro x hx
  -- x : X
  -- hx : x ∈ A
  -- ⊢ x ∈ B ∩ C
  constructor
  . -- ⊢ x ∈ B
    exact hAsB hx
  . -- ⊢ x ∈ C
    exact hAsC hx

-- Proof 5
-- =======

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C :=
by
  intro hAsB hAsC
  -- hAsB : A ⊆ B
  -- hAsC : A ⊆ C
  -- ⊢ A ⊆ B ∩ C
  intro x hx
  -- x : X
  -- hx : x ∈ A
  -- ⊢ x ∈ B ∩ C
  exact ⟨hAsB hx, hAsC hx⟩

-- Proof 6
-- =======

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C :=
fun hAsB hAsC _ hx => ⟨hAsB hx, hAsC hx⟩

-- Proof 6
-- =======

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C :=
by aesop

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    B ⊆ A → C ⊆ A → B ∪ C ⊆ A
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
by
  intro h_B_in_A h_C_in_A
  -- h_B_in_A : B ⊆ A
  -- h_C_in_A : C ⊆ A
  -- ⊢ B ∪ C ⊆ A
  rw [subset_def] at *
  -- h_B_in_A : ∀ x ∈ B, x ∈ A
  -- h_C_in_A : ∀ x ∈ C, x ∈ A
  -- ⊢ ∀ x ∈ B ∪ C, x ∈ A
  intro x h_x_in_B_o_C
  -- x : X
  -- h_x_in_B_o_C : x ∈ B ∪ C
  -- ⊢ x ∈ A
  rw [mem_union_iff] at h_x_in_B_o_C
  -- h_x_in_B_o_C : x ∈ B ∨ x ∈ C
  cases' h_x_in_B_o_C with h_x_in_B h_x_in_C
  . -- h_x_in_B : x ∈ B
    apply h_B_in_A at h_x_in_B
    -- h_x_in_B : x ∈ A
    exact h_x_in_B
  . -- h_x_in_C : x ∈ C
    apply h_C_in_A at h_x_in_C
    -- h_x_in_C : x ∈ A
    exact h_x_in_C

-- Proof 2
-- =======

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
  Set.union_subset

-- Proof 3
-- =======

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
by
  intro hBsA hCsA
  -- hBsA : B ⊆ A
  -- hCsA : C ⊆ A
  -- ⊢ B ∪ C ⊆ A
  simp [subset_def, mem_union_iff] at *
  -- hBsA : ∀ x ∈ B, x ∈ A
  -- hCsA : ∀ x ∈ C, x ∈ A
  -- ⊢ ∀ (x : X), x ∈ B ∨ x ∈ C → x ∈ A
  intro x hxeBoC
  -- x : X
  -- hxeBoC : x ∈ B ∨ x ∈ C
  -- ⊢ x ∈ A
  cases' hxeBoC with hxeB hxeC
  . -- hxeB : x ∈ B
    apply hBsA
    -- ⊢ x ∈ B
    exact hxeB
  . -- hxeC : x ∈ C
    apply hCsA
    -- ⊢ x ∈ C
    exact hxeC

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
by
  intro hAB hCD
  -- hAB : A ⊆ B
  -- hCD : C ⊆ D
  -- ⊢ A ∪ C ⊆ B ∪ D
  rw [subset_def] at *
  -- hAB : ∀ x ∈ A, x ∈ B
  -- hCD : ∀ x ∈ C, x ∈ D
  -- ⊢ ∀ x ∈ A ∪ C, x ∈ B ∪ D
  intro x hxAoC
  -- x : X
  -- hxAoC : x ∈ A ∪ C
  -- ⊢ x ∈ B ∪ D
  rw [mem_union_iff] at *
  -- hxAoC : x ∈ A ∨ x ∈ C
  -- ⊢ x ∈ B ∨ x ∈ D
  cases' hxAoC with hxA hxC
  . -- hxA : x ∈ A
    apply hAB at hxA
    -- hxA : x ∈ B
    left
    -- ⊢ x ∈ B
    exact hxA
  . -- hxC : x ∈ C
    apply hCD at hxC
    -- hxC : x ∈ D
    right
    -- ⊢ x ∈ D
    exact hxC

-- Proof 2
-- =======

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
  Set.union_subset_union

-- Proof 3
-- =======

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
by
  intro hAsB hCsD
  -- hAsB : A ⊆ B
  -- hCsD : C ⊆ D
  -- ⊢ A ∪ C ⊆ B ∪ D
  simp [subset_def, mem_union_iff] at *
  -- hAsB : ∀ x ∈ A, x ∈ B
  -- hCsD : ∀ x ∈ C, x ∈ D
  -- ⊢ ∀ (x : X), x ∈ A ∨ x ∈ C → x ∈ B ∨ x ∈ D
  intro x hxAoC
  -- x : X
  -- hxAoC : x ∈ A ∨ x ∈ C
  -- ⊢ x ∈ B ∨ x ∈ D
  specialize hAsB x
  -- hAsB : x ∈ A → x ∈ B
  specialize hCsD x
  -- hCsD : x ∈ C → x ∈ D
  exact Or.imp hAsB hCsD hxAoC

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that
--    A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
  intro hAB hCD
  rw [subset_def] at *
  intro x hxinAyC
  rw [mem_inter_iff] at *
  cases' hxinAyC with hxinA hxinC
  apply hAB at hxinA
  apply hCD at hxinC
  constructor
  exact hxinA
  exact hxinC

-- Proof 2 (automatic)
example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
  exact fun a a_1 => Set.inter_subset_inter a a_1

-- Proof 3 (equilibrated)
example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
  intro hAsB hCsD
  simp [subset_def, mem_inter_iff] at *
  intro x hxA hxC
  exact ⟨hAsB x hxA, hCsD x hxC⟩
