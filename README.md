# erdos-1089-lean

A Lean 4 proof of **Erdős problem [#1089](https://www.erdosproblems.com/1089)**, and of
**[#502](https://www.erdosproblems.com/502)** as a free corollary.

> **This is not the first formalisation of #1089, and does not claim to be.**
> [`plby/lean-proofs`](https://github.com/plby/lean-proofs) has had one since **2026-08-17**, eleven
> days before this one was completed, arrived at independently. Both now prove the same bounds and limit. See
> [Prior and independent work](#prior-and-independent-work) — and the machine-checked comparison in
> [`cross-check/`](cross-check/), which is the part of this repository most likely to be useful to
> anyone else.

```
#print axioms ErdosProofs.P1089.gDSpec_limit
  -- [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. No `sorry` anywhere in the source.

## What is proved

Let `g_d(n)` be the least `N` such that **every** collection of `N` points in ℝ^d determines at
least `n` distinct distances.

```lean
theorem gDSpec_limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun d : ℕ => (gDSpec d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (𝓝 (1 / ((n - 1).factorial : ℝ)))
```

That is `g_d(n) / d^(n-1) → 1/(n-1)!`, which answers #1089's *"does the limit exist?"* and gives its
value. It follows by squeezing the known sandwich

```
C(d+1, n-1) + 1  ≤  g_d(n)  ≤  C(d+n-1, n-1) + 1
```

whose lower bound is the Aletheia construction and whose upper bound is Bannai–Bannai–Stanton 1983.
BBS83 is not in mathlib, so it is proved here too, via a formalisation of **Petrov–Pohoata 2021**
([arXiv:1912.08181](https://arxiv.org/abs/1912.08181)) — `ErdosProofs/PetrovPohoata.lean`. That file
also yields #502 directly:

```lean
theorem P502.cardTwoDistanceSet_le : P.card ≤ Nat.choose (n + 2) 2   -- two-distance sets
```

### Fidelity

`gDSpec` is the problem's own wording, transcribed literally. The file also carries `gD`, defined as
`MD d (n-1) + 1` (the same quantity read from the maximising end), which is what the proof machinery
actually uses. **The two are proved equal** rather than assumed:

```lean
theorem gDSpec_eq_gD (d n : ℕ) (hn : 1 ≤ n) : gDSpec d n = gD d n
```

Cite `gDSpec_limit`. It is the one stated over the literal reading.

Two conventions, documented rather than hidden:

- **`n ≥ 1` is load-bearing.** At `n = 0` every `N` vacuously forces zero distances, so
  `gDSpec d 0 = 0` while `gD d 0 = 2`.
- **`d = 0` is degenerate.** ℝ⁰ is a single point, so no set of size `≥ 2` exists and the forcing
  condition is vacuous; both sides collapse to `2`. The theorem is true there but verifies nothing.

## Prior and independent work

[`plby/lean-proofs`](https://github.com/plby/lean-proofs) contains
`src/latest/ErdosProblems/Erdos1089.lean`, added **2026-08-17**. It is sorry-free, uses no
`native_decide` and adds no axioms, and its `erdos_1089` proves the full literature sandwich

```
C(d+1, n-1) + 1  ≤  g_d(n)  ≤  C(d+n-1, n-1) + 1
```

alongside the limit. Until 2026-10-27 this repository proved only the weaker lower bound
`C(d, n-1) + 1`; it now proves the same sandwich (`gDSpec_sandwich`), by mapping the sum-`s`
hyperplane of `ℝ^(d+1)` isometrically onto `ℝ^d` (`hyperplaneToEucl`). By the authoring agent's
account, only their headline statement was read, to state the cross-check, and not their
`hyperplaneIsometry`; nothing in the repository can verify that.

Erdős #502 is likewise already registered upstream: `FormalConjectures/ErdosProblems/502.lean` is
`@[category research solved]` with a `formal_proof` link to the same author's `Erdos502.lean`, by the
same Petrov–Pohoata route this repository takes.

### So what is this repository for

An **independent second formalisation**, and a machine-checked comparison of the two.
[`cross-check/run.sh`](cross-check/run.sh) fetches their file at runtime, at a pinned commit, type-checks it alongside
this one, and proves:

```lean
theorem g_eq_gDSpec (d n : ℕ) : Erdos1089.g d n = ErdosProofs.P1089.gDSpec d n
```

The two definitions were written independently and look nothing alike — theirs over `Finset` with
`dist` and `Finset.card`, this one over `Set` with `‖x - y‖` and `Set.ncard`. They are the same
function. Each side's limit theorem is then derived from the other's proof, in both directions, and
their whole `erdos_1089`, sandwich included, is derived from this one (`their_headline_from_ours`).

That is worth something a single formalisation cannot provide: for a statement nobody has yet
registered upstream, two independent transcriptions of the same informal source, by different model
lineages, provably agreeing on what the statement *means*. Misformalisation is the failure mode
formal statements are most exposed to, and agreement between independent renderings is evidence
against it.

Their repository carries **no LICENSE file**, so its content is all-rights-reserved. Nothing of
theirs is vendored here; the cross-check fetches it at run time.

## Verifying it yourself

```sh
lake exe cache get
lake build                       # expect zero `declaration uses sorry` warnings
printf 'import ErdosProofs\n#print axioms ErdosProofs.P1089.gDSpec_limit\n' > /tmp/ax.lean
lake env lean /tmp/ax.lean       # expect [propext, Classical.choice, Quot.sound]
```

CI runs the same checks on every push and weekly: `lake build`, then
[`cross-check/Axioms.lean`](cross-check/Axioms.lean) (fails if any headline theorem uses an axiom beyond those
three), then the cross-check.

Mathlib is pinned to `85e6e1b4` in `lakefile.lean`, deliberately: a repository that exists to be
cited as a verified proof should not stop verifying the day mathlib moves.

**Read the axiom check, not the build output.** A green `lake build` was not sufficient here — at one
point during development `P1089.lean` had no sorry warnings while `gD_limit` still depended on
`sorryAx` through the Petrov–Pohoata file. Only `#print axioms` catches that.

## Provenance — please read before citing

This is a **transcription**, not original mathematics, and it was produced with heavy AI assistance.
Specifically:

- The mathematical content comes from published, citable sources. The upper bound is
  Bannai–Bannai–Stanton 1983 (Combinatorica, 147–152). The lower bound is credited on
  erdosproblems.com to *Aletheia*, from **T. Feng et al., "Semi-Autonomous Mathematics Discovery
  with Gemini: A Case Study on the Erdős Problems", [arXiv:2601.22401](https://arxiv.org/abs/2601.22401)
  (2026)** — so the informal proof being transcribed here is itself an AI-discovered result, from a
  preprint, not an unattributed model output.
- The Lean formalisation was written by Claude (Anthropic) acting as a coding agent, across several
  sessions, under human direction. Individual proof steps were reviewed and iterated against the Lean
  kernel, which is the only oracle that matters for the sorry-freeness claim.
- Adversarial review of the substantive commits was performed by a different model lineage (OpenAI
  Codex) framed as a skeptic. It found no blocking defect in the proofs; the fixes it did prompt are
  recorded in the git history.

**What this repository does not claim.** That the informal source artifact is itself correct — the
Lean proof establishes the theorems *as stated here*, from mathlib, and nothing more. If you find a
misformalisation, that is a real bug and an issue is welcome.

## Licence

MIT — see [`LICENSE`](LICENSE).
