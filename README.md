# erdos-1089-lean

A Lean 4 proof of **Erdős problem [#1089](https://www.erdosproblems.com/1089)**, and of
**[#502](https://www.erdosproblems.com/502)** as a free corollary.

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

## Verifying it yourself

```sh
lake exe cache get
lake build                       # expect zero `declaration uses sorry` warnings
printf 'import ErdosProofs\n#print axioms ErdosProofs.P1089.gDSpec_limit\n' > /tmp/ax.lean
lake env lean /tmp/ax.lean       # expect [propext, Classical.choice, Quot.sound]
```

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
