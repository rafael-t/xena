open classical

variables p q r s : Prop

lemma L1 (h: p ∧ q) : q ∧ p := and.intro (and.right h) (and.left h)
lemma L2 : p ∧ q ↔ q ∧ p := iff.intro (L1 p q) (L1 q p)


lemma L3 (h: p ∨ q) : q ∨ p := or.elim h (or.intro_right q) (or.intro_left p)
lemma L4 : p ∨ q ↔ q ∨ p := iff.intro (L3 p q) (L3 q p)


lemma L5 (h: (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
have hpq : (p ∧ q), from and.left h,
have hp : p, from and.left hpq,
have hq : q, from and.right hpq,
have hr : r, from and.right h,
and.intro (hp)  (and.intro (hq) (hr))

lemma L6 (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := 
have hp : p, from and.left h,
have hqr : (q ∧ r), from and.right h,
have hq : q, from and.left hqr,
have hr : r, from and.right hqr,
and.intro (and.intro (hp) (hq)) (hr)

lemma L7 : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := iff.intro (L5 p q r) (L6 p q r)


lemma L8 (h: (p ∨ q) ∨ r) : p ∨ (q ∨ r) := sorry

lemma L9 (h: p ∨ (q ∨ r)) :  (p ∨ q) ∨ r := sorry

lemma L10 : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := iff.intro (L8 p q r) (L9 p q r)


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