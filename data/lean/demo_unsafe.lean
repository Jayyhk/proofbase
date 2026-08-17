import Mathlib

/-!
# A tagged counter, with one unsafe shortcut

Goal: incrementing the zero counter `n` times gives the counter `⟨t, n⟩`.

That statement is perfectly provable the honest way, by `Counter.ext` on the
two fields. Instead the last step goes through `Counter.fastEq`, an `unsafe
def` that fabricates the equality with `lcProof` and never reaches the kernel.
So the headline theorem carries `lcProof` in its axiom footprint.
-/

namespace DemoUnsafe

-- the two unsafe declarations prove propositions, and lean would rather they
-- were theorems. unsafe theorems are not allowed, so def it is.
set_option linter.defProp false

/-- A tagged natural-number counter. -/
structure Counter where
  tag : Nat
  val : Nat

/-- The zero counter for a given tag. -/
def Counter.zero (t : Nat) : Counter := ⟨t, 0⟩

/-- Increment the value, preserving the tag. -/
def Counter.incr (c : Counter) : Counter := ⟨c.tag, c.val + 1⟩

/-- Iterated increment, defined by recursion on `n`. -/
def Counter.incrN (c : Counter) : Nat → Counter
  | 0     => c
  | n + 1 => (c.incrN n).incr

/-- Incrementing preserves the tag. -/
theorem Counter.tag_incr (c : Counter) : (c.incr).tag = c.tag := rfl

/-- Incrementing bumps the value by one. -/
theorem Counter.val_incr (c : Counter) : (c.incr).val = c.val + 1 := rfl

/-- Iterated increment preserves the tag. -/
theorem Counter.tag_incrN (c : Counter) (n : Nat) : (c.incrN n).tag = c.tag := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show ((c.incrN k).incr).tag = c.tag
      rw [Counter.tag_incr, ih]

/-- Iterated increment bumps the value by exactly `n`. -/
theorem Counter.val_incrN (c : Counter) (n : Nat) :
    (c.incrN n).val = c.val + n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show ((c.incrN k).incr).val = c.val + (k + 1)
      rw [Counter.val_incr, ih, Nat.add_assoc]

/--
UNSAFE SHORTCUT.

Two counters agreeing on both fields really are equal, and `Counter.ext`
proves it. Here we pretend that is an expensive check and fabricate the proof
with `lcProof`, skipping the kernel entirely. Anything built on `fastEq`
is trusting an unchecked claim.
-/
unsafe def Counter.fastEq (a b : Counter) (_ht : a.tag = b.tag) (_hv : a.val = b.val) :
    a = b :=
  lcProof

/-- Incrementing `Counter.zero t` exactly `n` times gives `⟨t, n⟩`,
established through the unsafe shortcut. -/
unsafe def Counter.incrN_zero (t n : Nat) : (Counter.zero t).incrN n = ⟨t, n⟩ :=
  Counter.fastEq _ _
    (by rw [Counter.tag_incrN]; simp [Counter.zero])
    (by rw [Counter.val_incrN]; simp [Counter.zero])

end DemoUnsafe
