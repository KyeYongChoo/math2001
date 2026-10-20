import Mathlib.Data.Set.Basic

/-!
# Russell's paradox in Lean

1. The naive Russell set doesn't typecheck.
2. The engine of every version: no proposition is equivalent to its own negation.
3. Russell's argument as a theorem: naive comprehension is inconsistent.
4. What survives in typed Lean: Cantor's theorem for `Set`.
-/

namespace Russell

/-! ## 1. The naive Russell set is a type error

`Set α` is `α → Prop`, and `x ∈ s` needs `x : α` and `s : Set α`.
For `x ∈ x` to make sense, `x` would need type `α` and type `Set α`
at the same time. Uncomment this to see Lean refuse:

    def R : Set (Set ℕ) := {x | x ∉ x}
    -- error (roughly): failed to synthesize Membership (Set ℕ) (Set ℕ)

A set of sets lives one level up (`Set (Set α)`), so you can't even
*ask* whether a set contains itself.
-/

/-! ## 2. The engine of the paradox

Every version of Russell's paradox ends with a statement that is
equivalent to its own negation. That can never happen.
The proof doesn't use excluded middle, so it holds constructively too. -/

theorem liar (p : Prop) : ¬ (p ↔ ¬ p) := by
  intro h
  -- If p held, h would give ¬p, contradicting p. So ¬p.
  have hnp : ¬ p := fun hp => (h.mp hp) hp
  -- But then h turns ¬p back into p.
  exact hnp (h.mpr hnp)

/-! ## 3. Russell's paradox as a theorem

Naive set theory has a universe `U` of sets, a membership relation `mem`,
and *unrestricted comprehension*: for every property `P`, some set
contains exactly the things satisfying `P`.

Adding these as axioms would make Lean inconsistent. Instead we take
them as hypotheses and prove they can't all hold together. -/

theorem naive_comprehension_inconsistent (U : Type) (mem : U → U → Prop) :
    ¬ (∀ P : U → Prop, ∃ s : U, ∀ x, mem x s ↔ P x) := by
  intro comprehension
  -- Build Russell's set R = {x | x ∉ x}.
  obtain ⟨R, hR⟩ := comprehension (fun x => ¬ mem x x)
  -- hR : ∀ x, mem x R ↔ ¬ mem x x
  -- Now ask whether R ∈ R: hR R says R ∈ R ↔ R ∉ R.
  exact liar (mem R R) (hR R)

/-- The barber paradox is the same argument with one fixed relation:
nobody can shave exactly those who don't shave themselves. -/
theorem no_barber (Person : Type) (shaves : Person → Person → Prop) :
    ¬ ∃ b, ∀ x, shaves b x ↔ ¬ shaves x x := by
  rintro ⟨b, hb⟩
  exact liar (shaves b b) (hb b)

/-! ## 4. What survives in Lean: Cantor's theorem

The typed cousin of `{x | x ∉ x}` is legal. Given any `f : α → Set α`,
the diagonal set `D = {x | x ∉ f x}` is a perfectly good `Set α`.
Russell's argument now shows that `D` is never equal to any `f a`.

So the paradox turns into a theorem: no function from `α` hits every
set of elements of `α`, i.e. `Set α` is strictly bigger than `α`.
A "type of all sets" would have to contain its own power set,
so there isn't one. -/

theorem cantor {α : Type} (f : α → Set α) : ¬ Function.Surjective f := by
  intro hf
  let D : Set α := {x | x ∉ f x}
  -- Surjectivity says D is f a for some a.
  obtain ⟨a, ha⟩ := hf D
  -- By definition of D, a ∈ D exactly when a ∉ f a.
  have h : a ∈ D ↔ a ∉ f a := Iff.rfl
  -- But f a is D, so a ∈ D ↔ a ∉ D.
  rw [ha] at h
  exact liar (a ∈ D) h

-- Mathlib already has this as `Function.cantor_surjective`.

end Russell
