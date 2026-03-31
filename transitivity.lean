import Lean

open Lean Meta Elab Tactic

universe u



def Set (α : Type u) : Type u := α → Prop

namespace Set

protected def Subset {α : Type u} (s t : Set α) : Prop :=
  ∀ x : α, s x → t x

instance {α : Type u} : HasSubset (Set α) := ⟨Set.Subset⟩

protected theorem Subset.trans {α : Type u} {s t u : Set α}
    (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u :=
  fun _x hx => h₂ _x (h₁ _x hx)

-- reg Trans using the standard notation so typeclasses resolve
instance {α : Type u} : Trans (α := Set α) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) :=
  ⟨Set.Subset.trans⟩

end Set

instance : Trans (α := Nat) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Nat.le_trans⟩
instance : Trans (α := Nat) (· < ·) (· < ·) (· < ·) := ⟨Nat.lt_trans⟩

variable {α : Type u}


-- handling generic tactics

-- a wrapper for Trans.trans.
-- by enforcing that the relation R is the exact same for all three steps
theorem step_trans {β : Sort _} {R : β → β → Prop} [Trans R R R]
    {a b c : β} (h₁ : R a b) (h₂ : R b c) : R a c :=
  Trans.trans h₁ h₂


-- extracts the LHS and RHS from any applied relation.
-- gets the last two arguments bypassing hidden implicit type arguments
private def getLhsRhs (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size ≥ 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

elab "step" : tactic => do
  withMainContext do
    let target ← getMainTarget

    let some (goalLhs, goalRhs) := getLhsRhs target
      | throwError "step: Goal is not a recognized binary relation"

    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue

      if let some (hypLhs, hypRhs) := getLhsRhs decl.type then

        -- Guard against infinite loops from reflexive hypotheses (e.g., B ⊆ B)
        if hypLhs == hypRhs then continue

        -- Graph Check: Does this hypothesis start at our current goals LHS?
        if hypLhs == goalLhs then

          -- Case A: Exact Match (Destination Reached)
          if hypRhs == goalRhs then
            try
              evalTactic (← `(tactic| exact $(mkIdent decl.userName)))
              logInfo s!"step ✓ closed by {decl.userName}"
              return
            catch _ => pure ()

          -- Case B: Forward Step using our specialized `step_trans`
          try
            evalTactic (← `(tactic| refine step_trans $(mkIdent decl.userName) ?_))
            logInfo s!"step → advanced using {decl.userName}"
            return
          catch _ =>
            continue

    throwError "step: dead end — no forward hypothesis found from {goalLhs}"

macro "follow_chain" : tactic => `(tactic| repeat step)







-- Examples ---

-- Example 1 — basic subset chain
example (A B C : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  follow_chain


-- Example 2 — Nat inequality chain
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  follow_chain


-- Example 3 —  dummy hypotheses in context
example (A B C D E : Set α)
    (irrelevant      : D ⊆ E)
    (h1              : A ⊆ B)
    (also_irrelevant : B ⊆ B)   -- reflexive — must NOT cause a loop
    (h2              : B ⊆ C) : A ⊆ C := by
  follow_chain


-- Example 4 — three-step subset chain
example (A B C D : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : C ⊆ D) : A ⊆ D := by
  follow_chain


-- Example 5 — manual step calls
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  step   -- goal becomes b ≤ c
  step   -- closes goal

-- Example 6 — 2 conjuncts solved in parallel subgoals
example (a b c d e f : Nat)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hde : d ≤ e) (hef : e ≤ f) :
    a ≤ c ∧ d ≤ f := by
  constructor
  · follow_chain
  · follow_chain


-- Example 7 — using step with other tactics
example (A B C D : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : C ⊆ D) : A ⊆ D := by
  step        -- A ⊆ B via h1  →  goal: B ⊆ D
  step        -- B ⊆ C via h2  →  goal: C ⊆ D
  assumption  -- h3


-- Example 8 — Longer chain (5 sets)
example (A B C D E : Set α)
    (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : C ⊆ D) (h4 : D ⊆ E) : A ⊆ E := by
  follow_chain

-- Example 9 — calc for the same proof
example (A B C D : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) (hCD : C ⊆ D) : A ⊆ D := by
  calc A ⊆ B := h1
       _ ⊆ C := h2
       _ ⊆ D := hCD

-- Example 10 — follow_chain and calc are equivalent
example (A B C D : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) (hCD : C ⊆ D) : A ⊆ D := by
  follow_chain


-- Example 11 — theorem
theorem chain_example (X Y Z W : Set α)
    (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) (hZW : Z ⊆ W) : X ⊆ W := by
  follow_chain
