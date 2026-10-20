/-!
# Cardinality vs ordinality, in Lean

Cardinality asks: are two collections the same SIZE?
  "Same" means there is a bijection, any bijection at all.

Ordinality asks: are two well-ordered lines the same SHAPE?
  "Same" means there is a bijection that also respects the order.

In Lean the difference is exactly one extra field (see `SameShape` below).
For finite collections that field costs nothing, since any two orderings of n
things have the same shape. That's why everyday counting blurs "3 apples" with
"the 3rd apple". Infinite collections have room to shuffle (Hilbert's hotel),
and that is where the two notions come apart.

No imports needed; this is plain Lean 4.
-/

namespace CardOrd

/-- Same cardinality: a bijection, with no conditions on it.
(Mathlib calls this `α ≃ β`.) -/
structure SameSize (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- Same order type: a bijection that ALSO respects `<`.
(Mathlib calls this `α ≃o β`.) The only difference is `map_lt`. -/
structure SameShape (α β : Type) [LT α] [LT β] extends SameSize α β where
  map_lt : ∀ a a' : α, a < a' ↔ toFun a < toFun a'

/-! Throughout, `Nat` with its usual `<` is the ordinal ω: 0 < 1 < 2 < …,
going on forever with no last element. -/


/-! ## 1. ω + 1: add a new point at the END

Take 0, 1, 2, … and put one more point after all of them. -/

inductive OmegaPlusOne where
  | nat  : Nat → OmegaPlusOne   -- 0, 1, 2, …
  | back : OmegaPlusOne         -- then one point after all of them (call it ω)

def OmegaPlusOne.lt : OmegaPlusOne → OmegaPlusOne → Prop
  | .nat a, .nat b => a < b
  | .nat _, .back  => True
  | .back,  _      => False

instance : LT OmegaPlusOne := ⟨OmegaPlusOne.lt⟩

/-- Nothing is above the back point. -/
theorem OmegaPlusOne.not_back_lt (x : OmegaPlusOne) : ¬ (OmegaPlusOne.back < x) := by
  intro h
  cases x <;> exact h

/-- Same SIZE as Nat: send 0 to the back point and shift everyone else down.
This is Hilbert's hotel: making room costs nothing. -/
def OmegaPlusOne.fromNat : Nat → OmegaPlusOne
  | 0     => .back
  | n + 1 => .nat n

def OmegaPlusOne.toNat : OmegaPlusOne → Nat
  | .back  => 0
  | .nat n => n + 1

def omegaPlusOne_sameSize : SameSize Nat OmegaPlusOne where
  toFun := OmegaPlusOne.fromNat
  invFun := OmegaPlusOne.toNat
  left_inv := by intro n; cases n <;> rfl
  right_inv := by intro x; cases x <;> rfl

/-- NOT the same SHAPE as Nat. The bijection above scrambles the order
(it puts the biggest point at position 0), and every bijection has to:
ω + 1 has a largest element and Nat doesn't, and an order isomorphism
must preserve "is largest". -/
theorem omegaPlusOne_not_sameShape (e : SameShape Nat OmegaPlusOne) : False := by
  -- Some natural number n gets sent to the back point.
  obtain ⟨n, hn⟩ : ∃ n, e.toFun n = OmegaPlusOne.back :=
    ⟨_, e.right_inv OmegaPlusOne.back⟩
  -- n < n + 1, so e must send n + 1 somewhere above the back point.
  have h : e.toFun n < e.toFun (n + 1) := (e.map_lt n (n + 1)).mp (Nat.lt_succ_self n)
  rw [hn] at h
  -- But there's nothing above it.
  exact OmegaPlusOne.not_back_lt _ h


/-! ## 2. 1 + ω: add a new point at the FRONT

Now put the new point before everything else. This time the shape doesn't
change: shift every point up by one and the order is untouched.

So 1 + ω = ω, but ω + 1 ≠ ω. Ordinal addition is not commutative.
Cardinal addition is: 1 + ℵ₀ = ℵ₀ + 1 = ℵ₀, because size doesn't care
where you put the new point. Order does. -/

inductive OnePlusOmega where
  | front : OnePlusOmega          -- a new first point
  | nat   : Nat → OnePlusOmega    -- followed by 0, 1, 2, …

def OnePlusOmega.lt : OnePlusOmega → OnePlusOmega → Prop
  | .front, .front => False
  | .front, .nat _ => True
  | .nat _, .front => False
  | .nat a, .nat b => a < b

instance : LT OnePlusOmega := ⟨OnePlusOmega.lt⟩

def OnePlusOmega.shift : Nat → OnePlusOmega
  | 0     => .front
  | n + 1 => .nat n

def OnePlusOmega.unshift : OnePlusOmega → Nat
  | .front => 0
  | .nat n => n + 1

def onePlusOmega_sameShape : SameShape Nat OnePlusOmega where
  toFun := OnePlusOmega.shift
  invFun := OnePlusOmega.unshift
  left_inv := by intro n; cases n <;> rfl
  right_inv := by intro x; cases x <;> rfl
  map_lt := by
    intro a b
    cases a with
    | zero =>
      cases b with
      | zero =>
        show 0 < 0 ↔ False
        exact ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => h.elim⟩
      | succ m =>
        show 0 < m + 1 ↔ True
        exact ⟨fun _ => trivial, fun _ => Nat.succ_pos m⟩
    | succ n =>
      cases b with
      | zero =>
        show n + 1 < 0 ↔ False
        exact ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => h.elim⟩
      | succ m =>
        show n + 1 < m + 1 ↔ n < m
        exact ⟨Nat.lt_of_succ_lt_succ, Nat.succ_lt_succ⟩


/-! ## 3. ω + ω: two copies of Nat, one after the other

First 0, 1, 2, …, and then, after ALL of those, a second copy
ω, ω+1, ω+2, … . This is the ordinal ω·2. -/

inductive OmegaTwo where
  | first  : Nat → OmegaTwo   -- 0, 1, 2, …
  | second : Nat → OmegaTwo   -- ω, ω+1, ω+2, …

def OmegaTwo.lt : OmegaTwo → OmegaTwo → Prop
  | .first a,  .first b  => a < b
  | .first _,  .second _ => True
  | .second _, .first _  => False
  | .second a, .second b => a < b

instance : LT OmegaTwo := ⟨OmegaTwo.lt⟩

/-- Same SIZE as Nat: evens go to the first copy, odds to the second. -/
def OmegaTwo.interleave (n : Nat) : OmegaTwo :=
  if n % 2 = 0 then .first (n / 2) else .second (n / 2)

def OmegaTwo.deinterleave : OmegaTwo → Nat
  | .first n  => 2 * n
  | .second n => 2 * n + 1

def omegaTwo_sameSize : SameSize Nat OmegaTwo where
  toFun := OmegaTwo.interleave
  invFun := OmegaTwo.deinterleave
  left_inv := by
    intro n
    show OmegaTwo.deinterleave (OmegaTwo.interleave n) = n
    by_cases h : n % 2 = 0
    · have e : OmegaTwo.interleave n = .first (n / 2) := if_pos h
      rw [e]
      show 2 * (n / 2) = n
      omega
    · have e : OmegaTwo.interleave n = .second (n / 2) := if_neg h
      rw [e]
      show 2 * (n / 2) + 1 = n
      omega
  right_inv := by
    intro x
    cases x with
    | first n =>
      show OmegaTwo.interleave (2 * n) = .first n
      have h : 2 * n % 2 = 0 := by omega
      have e : OmegaTwo.interleave (2 * n) = .first (2 * n / 2) := if_pos h
      rw [e, show 2 * n / 2 = n by omega]
    | second n =>
      show OmegaTwo.interleave (2 * n + 1) = .second n
      have h : ¬ ((2 * n + 1) % 2 = 0) := by omega
      have e : OmegaTwo.interleave (2 * n + 1) = .second ((2 * n + 1) / 2) := if_neg h
      rw [e, show (2 * n + 1) / 2 = n by omega]

/-- Something stronger than "not the same shape": ω·2 can't even be
squeezed INTO Nat while keeping its order. There is no strictly increasing
map at all, even if it misses some numbers.

Why: the point ω (`second 0`) sits above infinitely many points, and in
Nat every number has only finitely many numbers below it.

So ω·2 isn't a bigger set than ω. It's a LONGER line. -/
theorem omegaTwo_no_embedding (f : OmegaTwo → Nat)
    (hf : ∀ x y, x < y → f x < f y) : False := by
  -- Along the first copy, f climbs at least one step at a time,
  -- so f (first n) ≥ n.
  have climb : ∀ n, n ≤ f (.first n) := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have step : f (.first k) < f (.first (k + 1)) :=
        hf (.first k) (.first (k + 1)) (Nat.lt_succ_self k)
      omega
  -- But the point ω = second 0 is above EVERY first n,
  -- including n = f (second 0) itself.
  have above : f (.first (f (.second 0))) < f (.second 0) :=
    hf (.first (f (.second 0))) (.second 0) trivial
  have := climb (f (.second 0))
  omega


/-! ## 4. Why anyone cares: ordinals measure processes, not sizes

Lean has to check that every recursive function terminates. In Ackermann's
function the second argument can jump up enormously while the first goes
down, so no simple Nat counter visibly decreases. Lean instead orders the
argument pairs (m, n) lexicographically: compare m first, then n.

That order has type ω² (ω copies of ω, one after another), which is far
longer than ω·2 from §3. As a SET, Nat × Nat is the same size as Nat
(Mathlib: `Nat.pairEquiv : ℕ × ℕ ≃ ℕ`). As an ORDER, the argument in §3
shows it can't be squeezed into Nat.

So termination is an ordinal question: it's about how long a descending
process can run, not how many states there are. Lean finds this
lexicographic order on its own: -/

def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

#eval ack 2 3   -- 9


/-! ## The picture

Every type in this file has the same SIZE, ℵ₀ (the size of Nat).
As ORDERS they're all different, and they sit on a ladder:

  ω = 1 + ω  <  ω + 1  <  ω + 2  < … <  ω·2  < … <  ω²  < …

Cardinality can't tell these rungs apart, while ordinality can.

The ladder goes on far beyond ω², and every rung is still countable for a
very long time. The first rung that can NOT be put in bijection with Nat is
called ω₁, and its size is the next cardinal, ℵ₁. That's one way to think of
cardinals: they mark the rungs on the ordinal ladder where the size finally
changes.
-/

end CardOrd
