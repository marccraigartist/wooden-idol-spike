# THE WOODEN IDOL

A Lean 4 formalisation of twelve constraints written from Leake Street.

**Marc Craig** · 2025–2026

---

## The question

Leake Street is London's sanctioned graffiti tunnel, beneath Waterloo Station —
a legal, continually repainted graffiti site since 2008. Nothing on its walls is
permanent; the practice is.

After a year of watching it, I wrote down twelve constraints describing what
seemed to be happening there — not what the wall looks like, but what kind of
thing it is. They were first shown as a poster asking the viewer to find a
system **S** satisfying all twelve at once, or to prove that no such system
exists.

The title carries two references: Bacon's idols of the mind, and the German
*hölzernes Eisen* — "wooden iron", a contradiction in terms. The accusation
built into the question was that the twelve might not be jointly satisfiable.

This repository answers that accusation. It contains a machine-checked proof
that a system satisfying all twelve exists, and a separate machine-checked
proof that no finite system can.

---

## Scope of this release

This release is a Lean 4 formalisation of the twelve constraints as stated in
the 18 July 2026 Rev B poster. Rev A, dated 9 April 2026, remains a distinct
earlier formulation in the project's history. The certificate establishes its
results for Rev B; it does not declare Rev B to be the sole or final canonical
artistic formulation.

The two revisions diverge at B6–B9.

---

## The twelve

| | Constraint | Content | Chart |
|---|---|---|---|
| **B1** | Non-solvability | No algorithm decides the system's global state | TRUTH |
| **B2** | Non-convergence | Some orbit recurs forever without converging | DISCOVERY |
| **B3** | Stabilising interval without specification | A stable region whose stabilising mechanism cannot be named in the system's own language | TRUTH |
| **B4** | Observational structure only | All relations derive from observed co-recurrence | TRUTH |
| **B5** | Proof-free consistency | The system is consistent, and no proof object inside it certifies that consistency | TRUTH |
| **B6** | Transformation without displacement | The global state changes while no element moves | DISCOVERY |
| **B7** | Self-reference without fixed point | A map referring to its own output everywhere, with no fixed point | DISCOVERY |
| **B8** | Non-generative coherence | Coherence is transported but never created | DISCOVERY |
| **B9** | Relation-only stability | No element is invariant under time | TRUTH |
| **B10** | Time as revealer, not solver | Time exposes structure but never collapses complexity | DISCOVERY |
| **B11** | Invariant without symbol | A nontrivial invariant that no sentence of the internal language defines | TRUTH |
| **B12** | Essential non-termination | Every state has a productive successor | DISCOVERY |

### Two partitions

The TRUTH / DISCOVERY charts are **interleaved**: what the wall *is* versus what
the wall *does*.

A second, different partition runs **contiguously**: B1–B6 as *doing*, B7–B12 as
*done*. B6 and B12 are its one-way hinges — doing becomes done at B6; what was
left behind re-enters as doing at B12.

The recorded mirror pairing is B1↔B10, B2↔B9, B3↔B8, B4↔B7, B5↔B6, B11↔B12.
The mirror exchanges TRUTH and DISCOVERY throughout, while interacting
non-uniformly with the doing/done split: four pairs cross that split, and two
sit beside its hinges.

Both partitions and the mirror are artistic and structural readings. Neither is
a Lean theorem.

### The B3–B9 chord

Lean certifies that the truth-set `Tr` is invariant under the dynamics while the
same dynamics fixes no individual state. I interpret this coexistence — a stable
set whose every point continues to move — as the B3–B9 chord joining doing and
done. The mathematical coexistence is certified; its artistic meaning is my
reading.

The invariance itself is inexpensive on this witness: the dynamics moves only
the Boolean coordinate, while `Tr` depends only on the first. B3's content comes
from Tarski's theorem, not from the dynamics.

---

## What is certified

The development establishes two separate results:

1. **There exists a system satisfying all twelve** — `Stage2.wooden_idol_stage2`
2. **No finite system satisfies all twelve** — `no_finite_idol`

Existence and finite impossibility are separate theorems and are stated
separately throughout.

Beyond those:

- **Gödel's second incompleteness theorem is load-bearing in B5**, through
  Foundation's `consistent_unprovable 𝗜𝚺₁`.
- **Tarski's undefinability theorem is load-bearing in Stage 2's B3 and B11**,
  through `undefinability_of_truth`.
- There is no `sorryAx` anywhere in the printed results.

The classical ingredients are classical. Nothing here is a new theorem of Gödel,
Tarski or Turing. The word for what has happened is **tested**.

---

## Architecture

| File | Status |
|---|---|
| `Idol.lean` | Stage 1. **Frozen** at v4.3. |
| `Idol2.lean` | Stage 2 sidecar, `namespace Stage2`. Certified. |
| `Spike.lean` | Disposable probe file. |
| `lakefile.toml` | Declares `Spike`, `Idol`, `Idol2`. |

`Idol2.lean` imports `Idol` and `Foundation.FirstOrder.Incompleteness.Tarski`.
The second import is required: Tarski is not visible through `import Idol` alone
under Lean 4.33 module visibility.

A theorem in a module importing a frozen certified module is a valid Lean
certificate. No monolithic merge is required or planned. The modular design is
easier to audit and keeps Stage 1 untouched.

### Naming warning

`Idol.lean` contains unqualified `wall3` and `wall11`. **These are the Stage 1
weld witnesses** — the old even-fibre construction, in which arithmetic
sentences denoted point-independently and could not name any subset of the wall.
Tarski is **not** load-bearing in them.

The Tarski-backed results are `Stage2.wall3` and `Stage2.wall11`.

Two independent auditors previously read the unqualified names and assumed
Tarski was already in place. The `Stage2.` names are the ones to cite.

---

## Stage 2: the integrated language

Stage 1 attached arithmetic to the wall but did not integrate it. Stage 1's
arithmetic branch was spatially mute. Its infinite even-fibre witness escaped
both the finite-support tables and the point-independent sentence denotations.

Stage 2 replaces that arrangement. The language has three constructors:

```lean
inductive WallL : Type
  | tbl : ℕ → WallL
  | snt : ArithmeticSentence → WallL
  | frm : ArithmeticSemisentence 1 → WallL
```

One-variable formulas denote at the fibre index, by decoding it:

```lean
| .frm θ, p => ∃ σ : ArithmeticSentence,
    Encodable.decode p.1 = some σ ∧
    ℕ↓[ℒₒᵣ] ⊧ θ/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]
```

Decoding is **partial**. Of the first 200 fibre addresses, 39 decode to a
sentence and 161 are silent. Silent addresses are the majority of the wall, and
this is why the decoding-performed definition is the honest one.

The accurate claim, and no stronger: *one-variable arithmetic formulas denote
genuine subsets of the readable fibres through their decoded sentence codes.*
They do not name every arithmetically definable pattern of every fibre — they
ignore the Boolean coordinate and are false at silent addresses.

### The invariant and the three-way obstruction

```lean
def Tr (p : ℕ × Bool) : Prop :=
  ∃ σ : ArithmeticSentence,
    Encodable.decode p.1 = some σ ∧ ℕ↓[ℒₒᵣ] ⊧ σ
```

A fibre belongs to `Tr` when its address decodes to a closed arithmetic sentence
that is true in the standard model. `wallNameless` closes all three naming
routes separately:

- **`Tr_no_tbl`** — bit tables coded by naturals have finite support; `Tr` is
  infinite.
- **`Tr_no_snt`** — a closed sentence denotes everywhere or nowhere; `Tr` is
  nonempty and not universal.
- **`Tr_no_frm`** — a formula naming `Tr` would define arithmetic truth,
  contradicting Tarski.

The arithmetic-formula branch is no longer spatially mute: it names genuine
subsets of readable fibres, yet still cannot name `Tr`. What blocks it is a
theorem, not a poverty of the language.

**B10 keeps its finite-table witness** by explicit decision — minimal
intervention, not necessity.

---

## Axiom report

Verbatim from `CERTIFICATE-2026-09-07.TXT`.

Stage 2, from `Idol2.lean`:

```
Stage2.topPow_true            [propext, Classical.choice, Quot.sound]
Stage2.topPow_inj             [propext]
Stage2.Tr_no_tbl              [propext, Classical.choice, Quot.sound]
Stage2.Tr_no_snt              [propext, Classical.choice, Quot.sound]
Stage2.Tr_no_frm              [propext, Classical.choice, Quot.sound]
Stage2.wallNameless           [propext, Classical.choice, Quot.sound]
Stage2.wall3                  [propext, Classical.choice, Quot.sound]
Stage2.wall11                 [propext, Classical.choice, Quot.sound]
Stage2.wooden_idol_stage2     [propext, Classical.choice, Quot.sound]
```

Stage 1, from the frozen `Idol.lean`, all on
`[propext, Classical.choice, Quot.sound]`:

```
no_finite_idol
idol11
departure_requires_infinity
artist_departure_requires_infinite_kappa
wall3
wall5
wall11
arrival_requires_infinity
artist_arrival_requires_infinite_kappa
wooden_idol
```

`[propext, Classical.choice, Quot.sound]` is the normal classical foundation
inherited from Lean and Mathlib. It contains no project-specific assumption and
no proof hole. `Stage2.topPow_inj` needs only `propext`.

These are the nineteen names the certificate prints. Other declarations exist in
the source and are built when the modules build; they are not individually
reported here.

---

## κ

κ is my name for the artists: what arrives from outside, changes the wall,
leaves, and whose residue becomes the next arrival's material.

**κ is not yet inside the twelve.** The `System` signature has no input type.
The κ results sit beside the main certificate. Under the formal predicates used,
the certificate prints four:

- `departure_requires_infinity`
- `artist_departure_requires_infinite_kappa`
- `arrival_requires_infinity`
- `artist_arrival_requires_infinite_kappa`

Informally: nothing finite can keep arriving, nothing finite can keep leaving,
and the two are asymmetric — an arrival is recognisable from a finite past,
while a departure quantifies over the unresolved future. The wall can keep a
register of who arrived; it can never finally close the register of who has
gone.

That is a statement about the chosen predicates, not a sociological law. No
priority search has established the asymmetry as new to the literature.

---

## The declared debt

**B1 is certified only in a no-finite-table form.** The prose says *no
algorithm*; the Lean says *no finite table*. Church–Turing strength requires a
new witness — the current one has trivially decidable reachability — and every
other constraint would need re-proving on that replacement.

This is the sole declared formalisation debt.

---

## What the kernel cannot check

Lean verifies that a proof follows from its definitions. It does not verify that
the definitions mean what the artwork meant.

B5 could have been closed with `Prf := fun _ => False`. The axiom report would
have been byte-identical: clean, hole-free, hollow. This is definition
laundering, and it is the one failure the kernel is structurally blind to.

The defences used here are prose-to-definition comparison, adversarial
read-back, anti-vacuity requirements, multiple independent auditors, visible
error ledgers, and refusing to treat *compiles* as *means what we meant*.

### Witness economy

Not all twelve are equally hard on this witness, and it would be dishonest to
present them as twelve breakthroughs:

- **B4** is true by definition (`Iff.rfl`).
- **B6** and **B8** are inexpensive on the two-phase construction.
- **B7** and **B12** follow from B9 on this witness.
- **B9** is the central contentful dynamical fact.
- **B3** and **B11** were cheap in Stage 1 and are not cheap in Stage 2 — they
  now require three independent closures.
- **B1** and **B10** rest on finite-support arguments.

---

## Error ledger

The failures are part of the work, and some of them are in the file as certified
theorems about their own inadequacy.

- **`naive_B1_always_false`** — the project's first B1 formalisation was
  vacuous. The proof of its inadequacy is preserved rather than deleted.
- **`extensional_selfref_fixed`, `B7_extensional_impossible`** — a purely
  extensional reading of self-reference forces exactly the fixed point B7
  forbids. B7 therefore requires an intensional reading.
- **`B3naive_B9_inconsistent`** — an early naïve B3 clashed with B9.
- **The abandoned `GodelTheory` abstraction** — four faults found in the
  project's own design: insufficient propositional logic, a D2 that was D1 in
  disguise, a D3 in the wrong form, and a diagonal condition satisfiable by no
  consistent theory. Abandoned rather than patched, in favour of Foundation's
  certified theorem.
- **The quotation misdiagnosis** — a large elaboration cascade was read as a
  mismatch between quoting a sentence and quoting its Gödel code. The two are
  definitionally equal by `rfl`. A local type-inference failure had generated a
  false mathematical story, and a day's work was estimated against it.
- **den1 vs den2** — an attempted equivalence proof became a genuine
  non-equivalence, because decoding is partial.
- **The missing import** — one unresolved identifier propagated `sorryAx`
  through five downstream theorems including the headline certificate.
- **`99import Idol`** — a two-character paste artefact on line 1 that stopped a
  build before any mathematics was parsed.

---

## Reproducibility

```
Lean       leanprover/lean4:v4.33.0
Mathlib    v4.33.0
Foundation FormalizedFormalLogic/Foundation @ f212e81 (Apache-2.0, ~56k lines)
```

Build command, as run:

```
lake build 2>&1 | tee build.log
```

Foundation brings Mathlib transitively. The toolchain must match exactly.

From the certificate:

```
Build completed successfully (8841 jobs).
[8840/8841] Built Idol2
```

`Foundation.FirstOrder.Incompleteness.Tarski` built as job 8824/8841. The Lean
build step took 14m 24s from a clean machine.

---

## Provenance

Two commits, answering two different questions.

**Certified Stage 2 source** — the code the kernel checked:

```
04d7f7d714bf2789af3b4e561a7fc92333b1c567
```

Workflow #32 · "Update Idol2.lean" · Success · 17m 40s

**Certificate snapshot** — the above plus the committed build log:

```
1e76d94ccd30c9f65fccc2f301395c6e7007c83c
```

Workflow #33 · "Create CERTIFICATE-2026-09-07.TXT" · Success · 17m 47s

Both snapshots received green builds. `CERTIFICATE-2026-09-07.TXT` is raw
evidence and is preserved verbatim; provenance and interpretation live here, not
in it. `CERTIFICATE-2026-09-06.TXT` records the Stage 1 state.

---

## Roadmap

- **Now** — publication: this README, a release, a DOI, external scrutiny.
- **Next** — a second constraint set written blind for another body of work,
  before any general machinery, so that a fit cannot be manufactured by
  construction.
- **Then** — Camp 7, standalone: what it can mean for the wall not to generate
  κ. Five candidate definitions, compared, with at least one closed infinite
  negative control so that infinity alone cannot masquerade as κ.
- **Not started** — Stage 3 adds inputs to the signature and changes the object.
  Stage 4 asks whether B3 forces the driver outside the language, and may be
  false. Stage 5 is B1 at Church–Turing strength plus the independence matrix.

The twelve have not been shown independent. The independence matrix has been
designed and never run.

---

## Claims not established by this release

- That any new theorem of Gödel, Tarski or Turing appears here.
- That B1 is a completed Church–Turing result.
- That all four language constraints "turned out to be" their classical
  theorems — B5 and Stage 2's B3/B11 do; B1 does not yet.
- That the Leake Street tunnel has been proved to instantiate S. That is a
  gallery interpretation.
- That an existential result about one object is a universal law about
  creativity, living systems, AI, physics or consciousness. It is not.
- That the twelve are independent.
- That the B3–B9 chord reading is kernel-certified.
- That the language names every arithmetically definable pattern of every fibre.
- That "wooden iron" was a paradox. It was a joint-satisfiability question, now
  answered with a witness.

---

## Credits

Twelve constraints, artistic direction and final semantic authority: **Marc
Craig**.

Candidate definitions and Lean proof drafts were produced in collaboration with
several AI systems, working against each other and against the kernel. Their
output was treated as testimony until the kernel accepted it; several of the
errors above were theirs, and several were caught by other AI collaborators
reading the same artefacts. The kernel is the only referee for proof validity.
No AI is the referee for meaning.

Gödel II, Tarski's undefinability theorem and the supporting first-order
machinery come from **FormalizedFormalLogic/Foundation**, Apache-2.0, whose
authors are gratefully acknowledged. Mathlib and the Lean 4 community underpin
all of it.

---

## Licence

The Lean source code and build configuration in this repository are licensed
under the **Apache License 2.0**. See [`LICENSE`](LICENSE).

The twelve constraints as worded, the prose of this README, and the associated
artwork and exhibition material are **© Marc Craig 2025–2026, all rights
reserved**. They are not covered by the Apache licence. See
[`COPYRIGHT.md`](COPYRIGHT.md) for the exact split.

Third-party dependencies retain their own licences. FormalizedFormalLogic/
Foundation is Apache-2.0 and is used as a dependency, not vendored.
