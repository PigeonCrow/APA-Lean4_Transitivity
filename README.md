# APA-Lean4_Transitivity

Automated forward transitivity chaining in Lean 4, implemented as a custom tactic. No Mathlib dependency — only `import Lean`.

## What it does

Proofs involving subset hierarchies or inequality chains typically require chaining several transitive steps before reaching a conclusion. In Lean 4 this is usually done with `calc` (verbose) or delegated to `omega`/`aesop` (opaque). This project provides two tactics that automate the process while remaining transparent and composable:

- **`step`** — scans the local hypothesis context, finds the unique hypothesis that advances the current goal by one relational hop, and either closes the goal or produces a strictly simpler residual goal.
- **`follow_chain`** — repeats `step` until the goal is closed.
```lean
example (A B C D : Set α) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : C ⊆ D) : A ⊆ D := by
  follow_chain   -- done in 3 steps, no manual wiring
```

## Supported relations

| Relation | Type |
|----------|------|
| `Set.Subset` (`⊆`) | User-defined sets |
| `Nat.le` (`≤`) | Natural numbers |
| `Nat.lt` (`<`) | Natural numbers |


Reflexive hypotheses (e.g. `h : B ⊆ B`) are skipped automatically — no loop, no crash.


## Requirements

- Lean 4 (core only)
- No Mathlib
