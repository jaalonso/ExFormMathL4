-- C03_Functions/Pset1.lean
-- Problem set 1: inyectivity, surjectivity, biyectivity.
-- Gabriel Sierra Gallego.
-- Seville, November 3, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with inyectivity,
-- surjectivity, biyectivity of functions.
--
-- It is based on [Section03functions/Sheet1.lean](https://tinyurl.com/2bbg8hdw)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

namespace Section3sheet1

open Function

variable (X Y Z : Type)
variable (x : X)
variable (f : X → Y)
variable (g : Y → Z)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that f is injective iff
--    ∀ a b : X, f a = f b → a = b
-- ---------------------------------------------------------------------

theorem injective_def :
  Injective f ↔ ∀ a b : X, f a = f b → a = b :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that f is surjective iff
--    ∀ b : Y, ∃ a : X, f a = b
-- ---------------------------------------------------------------------

theorem surjective_def :
  Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    id x = x
-- ---------------------------------------------------------------------

theorem id_eval : id x = x :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    (g ∘ f) x = g (f x)
-- ---------------------------------------------------------------------

theorem comp_eval : (g ∘ f) x = g (f x) :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that the identity function is injective.
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : Injective (id : X → X) :=
by
  rw [injective_def]
  -- ⊢ ∀ (a b : X), id a = id b → a = b
  intro a b hid
  -- a b : X
  -- hid : id a = id b
  -- ⊢ a = b
  rw [id_eval, id_eval] at hid
  -- hid : a = b
  exact hid

-- Proof 2
-- =======

example : Injective (id : X → X) :=
by
  simp [injective_def, id_eval]

-- Proof 3
-- =======

example : Injective (id : X → X) :=
  fun a b h => by
    rw [id_eval, id_eval] at h
    exact h

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example : Injective (id : X → X) :=
by
  intro a b h
  -- a b : X
  -- h : id a = id b
  -- ⊢ a = b
  exact h

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
-- =======

example : Injective (id : X → X) :=
fun _ _ h => h

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
-- =======

example : Injective (id : X → X) :=
injective_id

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that the identity function is surjective.
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : Surjective (id : X → X) :=
by
  rw [surjective_def]
  -- ⊢ ∀ (b : X), ∃ a, id a = b
  intro b
  -- b : X
  -- ⊢ ∃ a, id a = b
  use b
  -- ⊢ id b = b
  exact rfl

-- Proof 2
-- =======
example : Surjective (id : X → X) :=
by
  simp [surjective_def, id_eval]

-- Proof 3
-- =======
example : Surjective (id : X → X) :=
  fun b => by
    use b
    exact rfl

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example : Surjective (id : X → X) :=
by
  intro b
  -- b : X
  -- ⊢ ∃ a, id a = b
  exact ⟨b, rfl⟩

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
-- =======

example : Surjective (id : X → X) :=
fun b => ⟨b, rfl⟩

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
-- =======

example : Surjective (id : X → X) :=
surjective_id

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that if f : X → Y and g : Y → Z are injective,
-- then so is g ∘ f.
-- ---------------------------------------------------------------------



-- Proof 1
-- =======

example
  (hf : Injective f)
  (hg : Injective g)
  : Injective (g ∘ f) :=
by
  rw [injective_def] at *
  -- hf : ∀ (a b : X), f a = f b → a = b
  -- hg : ∀ (a b : Y), g a = g b → a = b
  -- ⊢ ∀ (a b : X), (g ∘ f) a = (g ∘ f) b → a = b
  intro a b h
  -- a b : X
  -- h : (g ∘ f) a = (g ∘ f) b
  -- ⊢ a = b
  rw [comp_eval, comp_eval] at h
  -- h : g (f a) = g (f b)
  apply hg at h
  -- h : f a = f b
  apply hf at h
  -- h : a = b
  exact h

-- Proof 2
-- =======

example
  (hf : Injective f)
  (hg : Injective g)
  : Injective (g ∘ f) :=
by
  exact Injective.comp hg hf

-- Comentario de JA: La 2ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 2'
-- =======

example
  (hf : Injective f)
  (hg : Injective g)
  : Injective (g ∘ f) :=
Injective.comp hg hf

-- Proof 3
-- =======

example
 (hf : Injective f)
 (hg : Injective g)
 : Injective (g ∘ f) :=
by
  simp [injective_def, comp_eval]
  -- ⊢ ∀ (a b : X), g (f a) = g (f b) → a = b
  intro a b h
  -- a b : X
  -- h : g (f a) = g (f b)
  -- ⊢ a = b
  apply hg at h
  -- h : f a = f b
  apply hf at h
  -- h : a = b
  exact h

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example
 (hf : Injective f)
 (hg : Injective g)
 : Injective (g ∘ f) :=
by
  intro a b h
  -- a b : X
  -- h : g (f a) = g (f b)
  -- ⊢ a = b
  apply hf
  -- ⊢ f a = f b
  apply hg
  -- ⊢ g (f a) = g (f b)
  exact h

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
-- =======

example
 (hf : Injective f)
 (hg : Injective g)
 : Injective (g ∘ f) :=
by
  intro a b h
  -- a b : X
  -- h : g (f a) = g (f b)
  -- ⊢ a = b
  apply hf
  -- ⊢ f a = f b
  exact hg h

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
-- =======

example
 (hf : Injective f)
 (hg : Injective g)
 : Injective (g ∘ f) :=
by
  intro a b h
  -- a b : X
  -- h : g (f a) = g (f b)
  -- ⊢ a = b
  exact hf (hg h)

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
-- =======

example
 (hf : Injective f)
 (hg : Injective g)
 : Injective (g ∘ f) :=
fun _ _ h => hf (hg h)

-- ---------------------------------------------------------------------
-- Exercise 9. Prove that if f : X → Y and g : Y → Z are surjective,
-- then so is g ∘ f.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Suppose that f : X → Y and g : Y → Z are surjective. We need to
-- prove that
--     (∀z ∈ Z)(∃x ∈ X)[g(f(x)) = z]
-- Let z ∈ Z. Since g is surjective, there exists a y ∈ Y such that
--     g(y) = z                                                      (1)
-- Since f is surjective, there exists an x ∈ X such that
--     f(x) = y                                                      (2)
-- Therefore,
--     g(f(x)) = g(y)   [by (2)]
--             = z      [by (1)]

-- Proof 1
-- =======

example
  (hf : Surjective f)
  (hg : Surjective g)
  : Surjective (g ∘ f) :=
by
  rw [surjective_def] at *
  -- hf : ∀ (b : Y), ∃ a, f a = b
  -- hg : ∀ (b : Z), ∃ a, g a = b
  -- ⊢ ∀ (b : Z), ∃ a, (g ∘ f) a = b
  intro z
  -- z : Z
  -- ⊢ ∃ a, (g ∘ f) a = z
  have h : ∃ y, g y = z := hg z
  cases' h with y hy
  -- y : Y
  -- hy : g y = z
  obtain ⟨x, hx⟩ := hf y
  -- x : X
  -- hx : f x = y
  use x
  -- ⊢ (g ∘ f) x = z
  calc
    g (f x) = g y := by rw [hx]
          _ = z   := by rw [hy]

-- Proof 2
-- =======

example
  (hf : Surjective f)
  (hg : Surjective g)
  : Surjective (g ∘ f) :=
by
  exact Surjective.comp hg hf

-- Comentario de JA: La 2ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 2a
-- ========

example
  (hf : Surjective f)
  (hg : Surjective g)
  : Surjective (g ∘ f) :=
Surjective.comp hg hf

-- Proof 3
-- =======

example
  (hf : Surjective f)
  (hg : Surjective g)
  : Surjective (g ∘ f) :=
by
  rw [surjective_def] at *
  -- hf : ∀ (b : Y), ∃ a, f a = b
  -- hg : ∀ (b : Z), ∃ a, g a = b
  -- ⊢ ∀ (b : Z), ∃ a, (g ∘ f) a = b
  simp [comp_eval]
  -- ⊢ ∀ (b : Z), ∃ a, g (f a) = b
  intro z
  -- z : Z
  -- ⊢ ∃ a, g (f a) = z
  specialize hg z
  -- hg : ∃ a, g a = z
  obtain ⟨y, hy⟩ := hg
  -- y : Y
  -- hy : g y = z
  specialize hf y
  -- hf : ∃ a, f a = y
  obtain ⟨x, hx⟩ := hf
  -- x : X
  -- hx : f x = y
  use x
  -- ⊢ g (f x) = z
  simp [hx, hy]

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example
  (hf : Surjective f)
  (hg : Surjective g)
  : Surjective (g ∘ f) :=
by
  intro z
  -- z : Z
  -- ⊢ ∃ a, g (f a) = z
  obtain ⟨y, hy⟩ := hg z
  -- y : Y
  -- hy : g y = z
  obtain ⟨x, hx⟩ := hf y
  -- x : X
  -- hx : f x = y
  use x
  -- ⊢ g (f x) = z
  calc
    g (f x) = g y := by rw [hx]
          _ = z   := by rw [hy]

-- ---------------------------------------------------------------------
-- Exercise 10. Prove that if (g ∘ f) is injective, then so is f.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- To prove that f is injective, let a and b be such that:
--    f(a) = f(b)                                                    (1)
-- and we need to prove that a = b.
--
-- From (1) we have:
--    g(f(a)) = g(f(b))
-- And, by the definition of composition,
--    (g∘f)(a) = (g∘f)(b)
-- Finally, since g∘f is injective, we have:
--    a = b

-- Proof 1
-- =======

example :
  Injective (g ∘ f) → Injective f :=
by
  rw [injective_def]
  -- ⊢ (∀ (a b : X), (g ∘ f) a = (g ∘ f) b → a = b) → Injective f
  intro h a b hab
  -- h : ∀ (a b : X), (g ∘ f) a = (g ∘ f) b → a = b
  -- a b : X
  -- hab : f a = f b
  -- ⊢ a = b
  apply h
  -- ⊢ (g ∘ f) a = (g ∘ f) b
  rw [comp_eval, comp_eval, hab]

-- Comentario de JA: La 1ª demostración se puede detallar como se
-- muestra a continuación.

-- Proof 2
-- =======

example :
  Injective (g ∘ f) → Injective f :=
by
  rw [injective_def]
  -- ⊢ (∀ (a b : X), (g ∘ f) a = (g ∘ f) b → a = b) → Injective f
  intro h a b hab
  -- h : ∀ (a b : X), (g ∘ f) a = (g ∘ f) b → a = b
  -- a b : X
  -- hab : f a = f b
  -- ⊢ a = b
  apply h
  -- ⊢ (g ∘ f) a = (g ∘ f) b
  rw [comp_eval]
  -- ⊢ g (f a) = (g ∘ f) b
  rw [comp_eval]
  -- ⊢ g (f a) = g (f b)
  rw [hab]

-- Proof 3
-- =======

example:
  Injective (g ∘ f) → Injective f :=
by
  exact fun a => Injective.of_comp a

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example:
  Injective (g ∘ f) → Injective f :=
Injective.of_comp

-- Proof 5
-- =======

example :
  Injective (g ∘ f) → Injective f :=
by
  simp [injective_def, comp_eval]
  -- ⊢ (∀ (a b : X), g (f a) = g (f b) → a = b) → ∀ (a b : X), f a = f b → a = b
  intro h a b hab
  -- a b : X
  -- hab : f a = f b
  -- ⊢ a = b
  apply h
  -- ⊢ g (f a) = g (f b)
  simp [hab]

-- Proof 6
-- =======

example : Injective (g ∘ f) → Injective f :=
by
  intro I
  intro a b h
  apply I
  exact congr_arg g h

-- Comentario de JA: La 6 demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
-- =======

example : Injective (g ∘ f) → Injective f :=
  fun I _ _ h ↦ I <| congr_arg g h

-- Proof 8
-- =======

example : Injective (g ∘ f) → Injective f :=
by
  intro I a b h
  -- I : Injective (g ∘ f)
  -- ⊢ Injective f
  -- a b : X
  -- h : f a = f b
  -- ⊢ a = b
  have h1 : g (f a) = g (f b) := congr_arg g h
  have h2 : (g ∘ f) a = (g ∘ f) b := h1
  exact I h2

-- ---------------------------------------------------------------------
-- Exercise 11. Prove that if (g ∘ f) is surjective, then so is f.
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  rw [surjective_def]
  intro h
  rw [surjective_def]
  intro z
  specialize h z
  obtain ⟨x, hx⟩ := h
  rw [comp_eval] at hx
  use (f x)

-- Proof 2 (automatic)
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  exact fun a => Surjective.of_comp a


-- Proof 3 (equilibrated)
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  simp [surjective_def, comp_eval]
  intro h z
  specialize h z
  obtain ⟨x, hx⟩ := h
  use (f x)


end Section3sheet1
