import Mathlib.Tactic
import Mathlib.Data.Real.Basic

open Real Nat

/-
# Overview

Lean is an open-source, general-purpose, extensible, dependently-typed functional programming
language and interactive proof assistant based on a version of dependent type theory
known as the *Calculus of Inductive Constructions*.

Every expression has a *type*, and you can use the `#check` command to
print it. Some expressions have types like `ℕ` or `ℕ → ℕ`.
-/

/- Define some constants. -/

def m : ℕ := 1         -- m is a natural number
def n : ℕ := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Some useful fiagnostic commands:
- `#check` prints the type of an expression;
- `#eval` evaluates an expression;
- `#lint` checks the file satisfies some style guidelines.
-/

/- Check their types. -/

#check 2 + 2        -- ℕ
#check m            -- output: ℕ
#check n
#check n + 0        -- ℕ
#check m * (n + 0)  -- ℕ
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9

#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

/- Given that every expression in Lean has a type, it is natural to ask: what type does `Type`
itself have? -/

#check Type

/- Lean's underlying foundation has an infinite hierarchy of types: -/

#check Type
#check Type 0
#check Type 1
#check Type 2
#check Type 3

/- Define a function. -/
def f (x : ℕ) : ℕ := x + 3
def g : ℕ → ℕ := fun x ↦ x + 3

#check f

/- We can express propositions, which are terms of type `Prop`. -/

#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

def FermatLastTheorem' : Prop := ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n
def FermatLastTheorem'' (x y z n : ℕ) (_ : n > 2 ∧ x * y * z ≠ 0) : Prop := x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem
#print FermatLastTheorem
/-
Some expressions are terms of type `P` where `P` itself is a term of type `Prop`.
Such an expression is a proof of the proposition `P`.
-/

theorem easy : 2 + 2 = 4 := by
  rfl

theorem easy' : 2 + 2 = 4 := rfl

#check easy

theorem hard : FermatLastTheorem := sorry

#check hard

/-
Given that we are trying to build complex expressions, Lean offers two ways of going about it:
- *term mode*: we can write down the expressions themselves;
- *tactic mode*: we can invoke metaprograms called *tactics* which provide instructions to
construct the expressions.

For example, the following expression represents a proof of the fact that
if `n` is even then so is `m * n`:
-/
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

/- The *proof term* can be compressed to a single line: -/
example : ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

/- The following is, instead, a *tactic-style* proof of the same theorem, where lines
starting with `--` are comments, hence ignored by Lean: -/
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Introduce `m` and `n` and decompose the hypothesis `Even n` to a `k` and the assumption that `n = 2 * k`
  rintro m n ⟨k, hk⟩
  -- Declare we are going to show that `m * n` is even by showing `m * n = 2 * (m * k)`.
  use m * k
  -- Replace `n` by `2 * k` in the target.
  rw [hk]
  -- Resolve by using ring properties.
  ring

/- A simple example theorem to showcase implicit arguments, sections, variables, namespaces. -/
theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

section MySection

variable (a b c d : ℝ)
variable (h₁ : a ≤ b) (h₂ : c ≤ d)

#check my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d h₁
#check my_add_le_add _ _ _ _ h₁
#check my_add_le_add _ _ _ _ h₁ h₂

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

#check @my_add_le_add'
#check my_add_le_add' h₁ h₂

end MySection

/- Let's compare `def` vs. `theorem` vs. `example`. -/
def my_add_le_add'' (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

theorem my_add_le_add''' (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

example (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

#check my_add_le_add''

#check my_add_le_add'''


/-
# Calculating

## The ring tactic

One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. Of course we usually don't want to invoke those explicitly
so mathlib has a tactic `ring` taking care of proving equalities that follow by applying
the properties of all commutative rings.
-/

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by ring

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by ring

/- In the first example above, take a closer look at where Lean displays parentheses.
The `ring` tactic certainly knows about associativity of multiplication, but sometimes
it is useful to understand that binary operation really are binary and an expression like
`a*b*c` is read as `(a*b)*c` by Lean and the fact that is equal `a*(b*c)` is a lemma
that is used by the `ring` tactic when needed.
-/


/-
## Rewriting

Let us now see how to compute using assumptions relating the involved numbers.
This uses the fundamental property of equality: if two
mathematical objects A and B are equal then, in any statement involving A, one can replace A
by B. This operation is called rewriting, and the Lean tactic for this is `rw`.
Carefully step through the proof below and try to understand what is happening.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  rw [h']
  ring

/- ## Rewriting with a lemma

In the previous example, we rewrote the goal using a local assumption. But we can
also use lemmas. For instance let us prove a lemma about exponentiation.
Since `ring` only knows how to prove things from the axioms of rings,
it doesn't know how to work with exponentiation.
For the following lemma, we will rewrite with the lemma
`exp_add x y` twice, which is a proof that `exp(x+y) = exp(x) * exp(y)`.
-/

example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add (a + b) c]
  rw [exp_add a b]


/-
Note also that after the second `rw` the goal becomes
`exp a * exp b * exp c = exp a * exp b * exp c` and Lean immediately declares the proof is done.

If we don't provide arguments to the lemmas, Lean will rewrite the first matching
subexpression. In our example this is good enough. Sometimes more control is needed.
-/

example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add, exp_add]


/-
Let's do an exercise, where you also have to use
`exp_sub x y : exp(x-y) = exp(x) / exp(y)` and `exp_zero : exp 0 = 1`.

Recall that `a + b - c` means `(a + b) - c`.

You can either use `ring` or rewrite with `mul_one x : x * 1 = x` to simplify the denominator on the
right-hand side.
-/

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  rw [exp_sub, exp_add, exp_zero, mul_one]

/-
## Rewriting from right to left

Since equality is a symmetric relation, we can also replace the right-hand side of an
equality by the left-hand side using `←` as in the following example.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h, h']


/-
Whenever you see in a Lean file a symbol that you don't see on your keyboard, such as ←,
you can put your mouse cursor above it and learn from a tooltip how to type it.
In the case of ←, you can type it by typing "\l ", so backslash-l-space.

Note this rewriting from right to left story is all about sides in the equality you want to
*use*, not about sides in what you want to *prove*. The `rw [← h]` will replace the right-hand side
by the left-hand side, so it will look for `b + c` in the current goal and replace it with `a`.
-/

example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  rw [← h', ← h, ← h'']


/- ## Rewriting in a local assumption

We can also perform rewriting in an assumption of the local context, using for instance
  `rw [exp_add x y] at h`
in order to replace `exp(x + y)` by `exp(x) * exp(y)` in assumption `h`.

The `exact` tactic allows you to give an explicit proof term to prove the current goal.
-/

example (a b c d : ℝ) (h : c = d*a + b) (h' : b = d) : c = d*a + d := by
  rw [h'] at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

/- ## Calculation layout using calc

What is written in the above example is very far away from what we would write on
paper. Let's now see how to get a more natural layout (and also return to using `ring`
instead of explicit lemma invocations).
After each `:=` below, the goal is to prove equality with the preceding line
(or the left-hand on the first line).
Carefully check you understand this by putting your cursor after each `by` and looking
at the tactic state.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring

/-
Let's do some exercises using `calc`.
-/

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by rw [h]
              _ = exp ((b + b) + (c + c))           := by ring_nf
              _ = exp (b + b) * exp (c + c)         := by rw [exp_add]
              _ = (exp b * exp b) * (exp c * exp c) := by rw [exp_add, exp_add]
              _ = (exp b) ^ 2 * (exp c)^2           := by ring


/-
From a practical point of view, when writing such a proof, it is sometimes convenient to:
* pause the tactic state view update in VScode by clicking the Pause icon button
  in the top right corner of the Lean Infoview panel.
* write the full calculation, ending each line with ":= ?_"
* resume tactic state update by clicking the Play icon button and fill in proofs.

The underscores should be placed below the left-hand-side of the first line below the `calc`.
Aligning the equal signs and `:=` signs is not necessary but looks tidy.
-/

example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by
  calc
    c = d*a + b   := by rw [h]
    _ = d*a + a*d := by rw [h']
    _ = 2*a*d     := by ring
