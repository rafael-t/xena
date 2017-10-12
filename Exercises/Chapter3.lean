open classical

variables p q r s : Prop


-- commutativity of ∧ and ∨
lemma L1 (h: p ∧ q) : q ∧ p := and.intro (and.right h) (and.left h)
lemma P1 : p ∧ q ↔ q ∧ p := iff.intro (L1 p q) (L1 q p)


lemma L2 (h: p ∨ q) : q ∨ p := or.elim h (or.intro_right q) (or.intro_left p)
lemma P2 : p ∨ q ↔ q ∨ p := iff.intro (L2 p q) (L2 q p)


-- associativity of ∧ and ∨
lemma L3 (h: (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
have hpq : (p ∧ q), from and.left h,
have hp : p, from and.left hpq,
have hq : q, from and.right hpq,
have hr : r, from and.right h,
and.intro (hp)  (and.intro (hq) (hr))

lemma L4 (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := 
have hp : p, from and.left h,
have hqr : (q ∧ r), from and.right h,
have hq : q, from and.left hqr,
have hr : r, from and.right hqr,
and.intro (and.intro (hp) (hq)) (hr)

lemma P3 : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := iff.intro (L3 p q r) (L4 p q r)


lemma L5 (h: (p ∨ q) ∨ r) : p ∨ (q ∨ r) := or.elim h
(assume hpq : (p ∨ q), or.elim hpq
    (assume hp : p, or.intro_left (q ∨ r) hp)
    (assume hq : q, or.intro_right p (or.intro_left r hq))
)
(assume hr : r, or.intro_right p (or.intro_right q hr))

lemma L6 (h: p ∨ (q ∨ r)) :  (p ∨ q) ∨ r := or.elim h
(assume hp : p, or.intro_left r (or.intro_left q hp))
(assume hqr : (q ∨ r), or.elim hqr
    (assume hq : q, or.intro_left r (or.intro_right p hq))
    (assume hr : r, or.intro_right (p ∨ q) hr)
)

lemma P4 : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := iff.intro (L5 p q r) (L6 p q r)


-- -- distributivity
-- example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry


-- -- other properties
lemma L11 (h: (p → (q → r))) : (p ∧ q → r) := assume hpq : (p ∧ q), show r, from h hpq.left hpq.right 

lemma L12 (h: (p ∧ q → r)) : (p → (q → r)) := assume hp : p, assume hq : q, show r, from h (and.intro (hp) (hq))

lemma P7 : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro (L11 p q r) (L12 p q r)


lemma L13 (h: ((p ∨ q) → r)) : (p → r) ∧ (q → r) := and.intro
(assume hp : p, h (or.intro_left q hp))
(assume hq : q, h (or.intro_right p hq))

lemma L14 (h: (p → r) ∧ (q → r)) : ((p ∨ q) → r) := sorry

lemma P8 : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := iff.intro (L13 p q r) (L14 p q r)

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