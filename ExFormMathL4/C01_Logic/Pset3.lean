-- C01_Logic/Pset3.lean
-- Problem set 3: The negation.
-- Gabriel Sierra Gallego.
-- Seville, October 22, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with the `not` in Lean4.
--
-- It is based on [Section01logic/Sheet3.lean](https://tinyurl.com/279t67ga)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

variable (P Q R : Prop)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    ¬True → False
-- ---------------------------------------------------------------------

-- Proof 1
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  change True → False at hnT
  -- hnT : True → False
  apply hnT
  -- ⊢ True
  exact True.intro

-- Proof 2
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  contradiction

-- Proof 3
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  have hT : True := True.intro
  contradiction

-- Comentario de JA: En la demostración anterior se puede evitar el uso
-- de la táctica contradiction como se muestra a continuación.

-- Proof 4
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  have hT : True := True.intro
  exact hnT hT

-- Comentario de JA: La demostración anterior se puede simplificar como
-- se muestra a continuación.

-- Proof 5
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  exact hnT True.intro

-- Comentario de JA: La demostración anterior se puede refactorizar como
-- se muestra a continuación.

-- Proof 6
example : ¬True → False :=
  fun hnT => hnT True.intro

-- Comentario de JA: Se puede demostrar automáticamente como se muestra
-- a continuación.

-- Proof 7
example : ¬True → False := by
  decide

-- Proof 8
example : ¬True → False := by
  tauto

-- Proof 9
example : ¬True → False := by
  trivial

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    False → ¬True
-- ---------------------------------------------------------------------

-- Proof 1
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  change True → False
  -- ⊢ True → False
  intro _hT
  -- _hT : True
  -- ⊢ False
  exact hF

-- Proof 2
example : False → ¬True := by
  trivial

-- Proof 3
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  tauto

-- Comentario de JA: La demostración anterior se puede simplificar como
-- se muestra a continuación.

-- Proof 4
example : False → ¬True := by
  tauto

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  intro _hT
  -- _hT : True
  -- ⊢ False
  exact hF

-- Comentario de JA: La demostración anterior se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : False → ¬True :=
  fun hF _hT => hF

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  contradiction

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    ¬False → True
-- ---------------------------------------------------------------------

-- Proof 1
example : ¬False → True := by
  intro _hnF
  -- _hnF : ¬False
  -- ⊢ True
  exact True.intro

-- Proof 2
example : ¬False → True := by
  tauto

-- Proof 3
example : ¬False → True := by
  intro _hnF
  -- _hnF : ¬False
  -- ⊢ True
  trivial

-- Comentario de JA: La demostración anterior se puede simplificar como
-- se muestra a continuación.

-- Proof 4
example : ¬False → True := by
  trivial

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : ¬False → True :=
  fun _ => True.intro

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    True → ¬False
-- ---------------------------------------------------------------------

-- Proof 1
example : True → ¬False := by
  intro _hT
  -- _hT : True
  -- ⊢ ¬False
  change False → False
  -- ⊢ False → False
  intro hF
  -- hF : False
  -- ⊢ False
  exact hF

-- Proof 2
example : True → ¬False := by
  tauto

-- Proof 3
example : True → ¬False := by
  intro _hT
  -- _hT : True
  -- ⊢ ¬False
  change False → False
  -- ⊢ False → False
  trivial

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : True → ¬False := by
  trivial

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : True → ¬False := by
  intro _hT
  -- _hT : True
  -- ⊢ ¬False
  intro hF
  -- hF : False
  -- ⊢ False
  exact hF

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : True → ¬False :=
  fun _hT hF => hF

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    False → ¬P
-- ---------------------------------------------------------------------

-- Proof 1
example : False → ¬P := by
  intro hF
  -- hF : False
  -- ⊢ ¬P
  change P → False
  -- ⊢ P → False
  intro _hP
  -- _hP : P
  -- ⊢ False
  exact hF

-- Proof 2
example : False → ¬P := by
  tauto

-- Proof 3
example : False → ¬P := by
  intro hF
  -- hF : False
  -- ⊢ ¬P
  contradiction

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : False → ¬P := by
  intro hF
  -- hF : False
  -- ⊢ ¬P
  exact False.elim hF

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : False → ¬P :=
  fun hF => False.elim hF

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    P → (¬P → False)
-- ---------------------------------------------------------------------

-- Proof 1
example : P → ¬P → False := by
  intro hP hnP
  -- hP : P
  -- hnP : ¬P
  -- ⊢ False
  change P → False at hnP
  -- hnP : P → False
  apply hnP
  -- ⊢ P
  exact hP

-- Proof 2
example : P → ¬P → False := by
  tauto

-- Proof 3
example : P → ¬P → False := by
  intro hP hnP
  contradiction

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P → ¬P → False := by
  intro hP hnP
  -- hP : P
  -- hnP : ¬P
  -- ⊢ False
  apply hnP
  -- ⊢ P
  exact hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P → ¬P → False :=
  fun hP hnP => hnP hP

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    P → ¬¬P
-- ---------------------------------------------------------------------

-- Proof 1
example : P → ¬¬P := by
  intro hP
  -- hP : P
  -- ⊢ ¬¬P
  change (P → False) → False
  -- ⊢ (P → False) → False
  intro hnP
  -- hnP : P → False
  -- ⊢ False
  have hF : False := hnP hP
  exact hF

-- Proof 2
example : P → ¬¬P := by
  tauto

-- Proof 3
example : P → ¬¬P := by
  intro hP
  -- hP : P
  -- ⊢ ¬¬P
  change (P → False) → False
  -- ⊢ (P → False) → False
  intro hnP
  -- hnP : P → False
  -- ⊢ False
  contradiction

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P → ¬¬P := by
  intro hP
  -- hP : P
  -- ⊢ ¬¬P
  intro hnP
  -- hnP : hnP : ¬P
  -- ⊢ False
  exact hnP hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P → ¬¬P :=
  fun hP hnP => hnP hP

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that
--    (P → Q) → (¬Q → ¬P)
-- -----------------------------------------------------------

-- Proof 1
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- ⊢ ¬P
  change P → False
  -- ⊢ P → False
  intro hP
  -- hP : P
  -- ⊢ False
  apply hPQ at hP
  -- hP : Q
  apply hnQ at hP
  -- hP : False
  exact hP

-- Proof 2
example : (P → Q) → ¬Q → ¬P := by
  tauto

-- Proof 3
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- hP : P
  -- ⊢ False
  apply hPQ at hP
  -- hP : Q
  contradiction

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- hP : P
  -- ⊢ False
  apply hnQ
  -- ⊢ Q
  apply hPQ
  -- ⊢ P
  exact hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (P → Q) → ¬Q → ¬P :=
  fun hPQ hnQ hP => hnQ (hPQ hP)

-- Comentario de JA: La 5ª demostración se puede detallar como se
-- muestra a continuación.

-- Proof 6
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- hP : P
  -- ⊢ False
  have hQ : Q := hPQ hP
  show False
  exact hnQ hQ

-- ---------------------------------------------------------------------
-- Exercise 9. Prove that
--    ¬¬False → False
-- ---------------------------------------------------------------------

--Proof 1
example : ¬¬False → False := by
  intro hnnF
  -- hnnF : ¬¬False
  -- ⊢ False
  change (False → False) → False at hnnF
  -- hnnF : (False → False) → False
  apply hnnF
  -- ⊢ False → False
  intro hF
  -- hF : False
  -- ⊢ False
  exact hF

-- Proof 2
example : ¬¬False → False := by
  tauto

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 3
example : ¬¬False → False := by
  intro hnnF
  -- hnnF : ¬¬False
  -- ⊢ False
  apply hnnF
  -- ⊢ False → False
  intro hF
  -- hF : False
  -- ⊢ False
  exact hF

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : ¬¬False → False :=
  fun hnnF => hnnF (fun hF => hF)

-- ---------------------------------------------------------------------
-- Exercise 10. Prove that
--    ¬¬P → P
-- ---------------------------------------------------------------------

-- Proof 1
example : ¬¬P → P := by
  intro hnnP
  -- hnnP : ¬¬P
  -- ⊢ P
  change (P → False) → False at hnnP
  -- hnnP : (P → False) → False
  by_contra hnP
  -- hnP : ¬P
  -- ⊢ False
  apply hnnP
  -- ⊢ P → False
  exact hnP

-- Proof 2
example : ¬¬P → P := by
  tauto

-- Proof 3
example : ¬¬P → P := by
  intro hnnP
  -- hnnP : ¬¬P
  -- ⊢ P
  by_contra hnP
  -- hnP : ¬P
  -- ⊢ False
  apply hnnP at hnP
  -- hnP : False
  exact hnP

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : ¬¬P → P := by
  intro hnnP
  -- hnnP : ¬¬P
  -- ⊢ P
  by_contra hnP
  -- hnP : ¬P
  -- ⊢ False
  exact hnnP hnP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : ¬¬P → P := by
  intro hnnP
  -- hnnP : ¬¬P
  -- ⊢ P
  apply Classical.byContradiction
  -- ⊢ ¬P → False
  exact hnnP

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : ¬¬P → P :=
  fun hnnP => Classical.byContradiction hnnP

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : ¬¬P → P :=
  Classical.byContradiction

-- ---------------------------------------------------------------------
-- Exercise 10. Prove that
--    (¬Q → ¬P) → (P → Q)
-- ---------------------------------------------------------------------

-- Proof 1
example : (¬Q → ¬P) → (P → Q) := by
  intro nQnP hP
  -- nQnP : ¬Q → ¬P
  -- hP : P
  -- ⊢ Q
  by_contra hnQ
  -- hnQ : ¬Q
  -- ⊢ False
  apply nQnP at hnQ
  -- hnQ : ¬P
  apply hnQ at hP
  -- hP : False
  exact hP

-- Proof 2
example : (¬Q → ¬P) → (P → Q) := by
  tauto

-- Proof 3
example : (¬Q → ¬P) → P → Q := by
  intro nQnP hP
  -- nQnP : ¬Q → ¬P
  -- hP : P
  -- ⊢ Q
  by_contra hnQ
  -- hnQ : ¬Q
  -- ⊢ False
  apply nQnP at hnQ
  -- hnQ : ¬P
  contradiction

-- Comentario de JA: Se puede evitar modificar las hipótesis como se
-- muestra a continuación.

-- Proof 4
example : (¬Q → ¬P) → P → Q := by
  intro nQnP hP
  -- nQnP : ¬Q → ¬P
  -- hP : P
  -- ⊢ Q
  by_contra hnQ
  -- hnQ : ¬Q
  -- ⊢ False
  have hnP : ¬P := nQnP hnQ
  apply hnP
  -- ⊢ P
  exact hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (¬Q → ¬P) → P → Q := by
  intro nQnP hP
  -- nQnP : ¬Q → ¬P
  -- hP : P
  -- ⊢ Q
  by_contra hnQ
  -- hnQ : ¬Q
  -- ⊢ False
  apply (nQnP hnQ)
  -- ⊢ P
  exact hP

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : (¬Q → ¬P) → P → Q := by
  intro nQnP hP
  -- nQnP : ¬Q → ¬P
  -- hP : P
  -- ⊢ Q
  apply Classical.byContradiction
  -- ⊢ ¬Q → False
  intro hnQ
  -- hnQ : ¬Q
  -- ⊢ False
  apply (nQnP hnQ)
  -- ⊢ P
  exact hP

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : (¬Q → ¬P) → P → Q :=
  fun nQnP hP => Classical.byContradiction (fun hnQ => nQnP hnQ hP)
