open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
lemma L1 : p ∧ q → q ∧ p := assume h : p ∧ q, and.intro (and.right h) (and.left h)

lemma L2 : p ∧ q ↔ q ∧ p := iff.intro
(assume h : p ∧ q, L1 p q h)
(assume h : q ∧ p, L1 q p h)

lemma L3 : p ∨ q → q ∨ p := assume h : p ∨ q, or.elim h
(assume hp : p, or.intro_right q hp)
(assume hq : q, or.intro_left p hq)

lemma L4 : p ∨ q ↔ q ∨ p := iff.intro
(assume h : p ∨ q, L3 p q h)
(assume h : q ∨ p, L3 q p h)

-- -- associativity of ∧ and ∨
-- example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
-- example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- -- distributivity
-- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- -- other properties
-- example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
-- example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
-- example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
-- example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
-- example : ¬(p ∧ ¬p) := sorry
-- example : p ∧ ¬q → ¬(p → q) := sorry
-- example : ¬p → (p → q) := sorry
-- example : (¬p ∨ q) → (p → q) := sorry
-- example : p ∨ false ↔ p := sorry
-- example : p ∧ false ↔ false := sorry
-- example : ¬(p ↔ ¬p) := sorry
-- example : (p → q) → (¬q → ¬p) := sorry

-- -- these require classical reasoning
-- example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
-- example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
-- example : ¬(p → q) → p ∧ ¬q := sorry
-- example : (p → q) → (¬p ∨ q) := sorry
-- example : (¬q → ¬p) → (p → q) := sorry
-- example : p ∨ ¬p := sorry
-- example : (((p → q) → p) → p) := sorry