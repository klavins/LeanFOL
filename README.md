A Formalization of First Order Logic
===

In this project we embed First Order Logic into Lean by defining:

- An **abstract syntax** tree (AST) for first order logic expressions built from variables, predicates, `⊥`, `→`, and `∀`, from which one defines `∧`, `∨`, `¬`, and `∃`.

- An inductive definition of **provability**, denoted `Γ ⊢ φ`, that encodes the proof rules `ax`, `⊥-elim`, `→-intro`, `→-elim`, `∀-intro`, `∀-elim`, and `em`.

- A definition of **entailment**, denoted `Γ ⊨ φ`

- Examples from graph theory and the natural numbers.

- A proof of **soundness**: `Γ ⊢ φ → Γ ⊨ φ`

- A *partial* proof of **completness**: `Γ ⊨ φ → Γ ⊢ φ`

Functions are not defined directly, but are simulated using predicates. See the examples.

Details of the Embedding
===

**Variables** are represented using **Debruijn indices**. For example:

&nbsp;&nbsp;&nbsp; `all (ex (rel P ![1,0]))`   &nbsp;&nbsp;&nbsp;
represents                  &nbsp;&nbsp;&nbsp;
`∀ x . ∃ y . P(x,y)`

A comprehesive library of dozens of `@[simps]` supports substitution, lifting,
and renaming of variable indices crucial for the proof of soundness.

**Signatures** contain predicate declarations with specific arities.
For example, a Graph theory signature with equality is denoted:
```lean
inductive Graph : Signature 
  | E : Graph 2 
  | eq: Graph 2
```

**Models** are represented as structures with interpretations as in:
```lean
def Cycle (n : ℕ): Model Graph (Fin n) := ⟨
  fun sym f => match sym with
    | E => f 0 = ((f 1) + 1) % n
    | eq => f 0 = f 1
⟩
```

Related Work
===

▸ A great book for First Order Logic is by Ederton: *A Mathematical
Introduction to Logic*.

▸ [Debruijn](https://en.wikipedia.org/wiki/De_Bruijn_index) was developed
in terms of the lambda calculus. It is explained in Arthur Charguéraud's *The Locally Nameless Representation*, JAR 2012 [Link](https://www.chargueraud.org/research/2009/ln/main.pdf) among other places.

▸ First order logic is already defined in Mathlib based on the
[Flypitch project](https://flypitch.github.io/), which is a formalization
of the proof of the independence of the continuum hypothesis. This project was
developed separately, for purposes of self-edification.

▸ For connections to category theory: *First Order Categorical Logic
Model-Theoretical Methods in the Theory of Topoi and Related Categories*, by
Michael Makkai and Gonzalo E. Reyes.

