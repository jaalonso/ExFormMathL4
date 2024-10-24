import Mathlib.Tactic -- imports all the Lean tactics

variable (P Q R S : Prop)

-- Example 1: P → P ∨ Q

-- Detailed proof
example : P → P ∨ Q := by
  intro hP
  left
  exact hP

-- Automatic proof
example : P → P ∨ Q := by
  tauto

-- Balanced proof
example : P → P ∨ Q := by
  intro hP
  exact Or.inl hP


-- Example 2: Q → P ∨ Q

-- Detailed proof
example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ


-- Automatic proof
example : Q → P ∨ Q := by
  tauto

-- Balanced proof
example : Q → P ∨ Q := by
  intro hQ
  exact Or.inr hQ


-- Example 3: P ∨ Q → (P → R) → (Q → R) → R

-- Detailed proof
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  cases' hPoQ with hP hQ
  apply hPR at hP
  exact hP
  apply hQR at hQ
  exact hQ

-- Automatic proof
example : P ∨ Q → (P → R) → (Q → R) → R := by
  tauto

-- Balanced proof
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  cases' hPoQ with hP hQ
  exact hPR hP
  exact hQR hQ


-- Example 4: P ∨ Q → Q ∨ P

-- Detailed proof
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  right
  exact hP
  left
  exact hQ

-- Automatic proof
example : P ∨ Q → Q ∨ P := by
  tauto

-- Balanced proof
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  exact Or.inr hP
  exact Or.inl hQ


-- Example 5: (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R

-- Detailed proof
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro hPoQoR
  cases' hPoQoR with hPoQ hR
  cases' hPoQ with hP hQ
  left
  exact hP
  right
  left
  exact hQ
  right
  right
  exact hR
  intro hPoQoR
  cases' hPoQoR with hP hQoR
  left
  left
  exact hP
  cases' hQoR with hQ hR
  left
  right
  exact hQ
  right
  exact hR

-- Automatic proof
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  tauto

-- Balanced proof
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  -- Forward direction
  intro hPoQoR
  cases' hPoQoR with hPQ hR
  cases' hPQ with hP hQ
  exact Or.inl hP
  exact Or.inr (Or.inl hQ)
  exact Or.inr (Or.inr hR)
  -- Backward direction
  intro hPoQoR
  cases' hPoQoR with hP hQoR
  exact Or.inl (Or.inl hP)
  cases' hQoR with hQ hR
  exact Or.inl (Or.inr hQ)
  exact Or.inr hR


-- Example 6: (P → R) → (Q → S) → P ∨ Q → R ∨ S

-- Detailed proof
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  cases' hPoQ with hP hQ
  apply hPR at hP
  left
  exact hP
  apply hQS at hQ
  right
  exact hQ

-- Automatic proof
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  tauto

-- Balanced proof
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  cases' hPoQ with hP hQ
  exact Or.inl (hPR hP)
  exact Or.inr (hQS hQ)


-- Example 7: (P → Q) → P ∨ R → Q ∨ R

-- Detailed proof
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  cases' hPoR with hP hR
  apply hPQ at hP
  left
  exact hP
  right
  exact hR

-- Automatic proof
example : (P → Q) → P ∨ R → Q ∨ R := by
  tauto

-- Balanced proof
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  cases' hPoR with hP hR
  exact Or.inl (hPQ hP)
  exact Or.inr hR

-- Example 8: (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S)

-- Detailed proof
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPiffR hQiffS
  constructor
  intro hPoQ
  cases' hPoQ with hP hQ
  cases' hPiffR with hPR hRP
  apply hPR at hP
  left
  exact hP
  cases' hQiffS with hQS hSQ
  apply hQS at hQ
  right
  exact hQ
  intro hRoS
  cases' hRoS with hR hS
  cases' hPiffR with hPR hRP
  apply hRP at hR
  left
  exact hR
  cases' hQiffS with hQS hSQ
  apply hSQ at hS
  right
  exact hS

-- Automatic proof
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  tauto

-- Balanced proof
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
  by
  intro h1 h2
  rw [h1, h2]


-- Example 9: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q

-- Detailed proof
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hPoQ
  constructor
  intro hP
  apply hPoQ
  left
  exact hP
  intro hQ
  apply hPoQ
  right
  exact hQ
  intro hPAnQ
  intro hPoQ
  cases' hPAnQ with hP hQ
  cases' hPoQ with hP hQ
  contradiction
  contradiction


-- Automatic proof
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  tauto

-- Balanced proof
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hPoQ
  exact ⟨fun hP => hPoQ (Or.inl hP), fun hQ => hPoQ (Or.inr hQ)⟩
  intro hPynQ
  intro hPoQ
  cases' hPoQ with hP hQ
  exact hPynQ.left hP
  exact hPynQ.right hQ

-- Example 10: ¬(P ∧ Q) ↔ ¬P ∨ ¬Q

-- Detailed proof
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by

  sorry

-- Automatic proof
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  tauto

-- Balanced proof
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      exact ⟨hP, hQ⟩
    · left
      exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · contradiction
    · apply hnQ; exact hQ
