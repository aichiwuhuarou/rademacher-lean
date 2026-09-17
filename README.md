# Rademacher's Theorem in Lean 4

A complete, machine-checked proof of **Rademacher's theorem** (1962):

> Every graph on `n ≥ 3` vertices with at least `⌊n²/4⌋ + 1` edges
> contains at least `⌊n/2⌋` triangles.

**Scope note.** This repository formalizes the case `l = 1` (Rademacher's
original theorem). The generalization of Khadzhiivanov–Nikiforov (1981) —
at least `⌊n/2⌋ · l` triangles for `⌊n²/4⌋ + l` edges with `2l < n` — is
not (yet) included; its known proofs require the long structural argument of
Lovász–Simonovits.

## Main result

```lean
theorem Rad.rademacher [DecidableRel G.Adj] (h3 : 3 ≤ Fintype.card V)
    (he : Fintype.card V ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    Fintype.card V / 2 ≤ (G.cliqueFinset 3).card
```

See [`Prizeformalize/Basic.lean`](Prizeformalize/Basic.lean). The proof is a
strong induction on the number of vertices, following the classical elementary
argument (documented in [`PROOF.md`](PROOF.md)):

* **Base cases** `n = 3, 4` (via Mantel's theorem from mathlib's Turán machinery).
* **Odd `n = 2m+1`**: a handshake-lemma argument produces a vertex of degree
  `≤ m`; peeling it leaves a graph satisfying the induction hypothesis.
* **Even `n = 2m`**:
  * if some vertex has degree `≤ m − 1`, peel it (deleting one edge of a
    Mantel-guaranteed triangle when the vertex lies in no triangle);
  * otherwise all degrees are `≥ m`; the identity `Σ(d(v) − m) = 2` (handshake)
    shows at most two vertices have degree `≥ m+1`, so some vertex lying in a
    triangle still has degree `≤ m`, and peeling it costs at most one triangle.

Trust boundary: `#print axioms` reports only `[propext, Classical.choice,
Quot.sound]` — the three standard axioms of Lean 4 + mathlib; there is no
`sorry`, `native_decide`, or custom axiom.

## Building

Requires [elan](https://elan.lean-lang.org). The toolchain and mathlib
revision are pinned (`lean-toolchain`, `lake-manifest.json`).

```sh
lake exe cache get   # download prebuilt mathlib (≈ 6 GB)
lake build
```

Verified with Lean `v4.33.0` and mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

## Attribution

* **Theorem**: E. Rademacher, 1962 (unpublished; see the references in
  PROOF.md for the history). The informal proof formalized here is the
  standard elementary induction; the write-up in PROOF.md was assembled and
  gap-checked from public lecture materials.
* **Formalization**: AI-assisted (GLM, via the ZCode agent, directed by
  @aichiwuhuarou), September 2026. All proof scripts are original to this
  repository; no third-party Lean code was copied.

## License

Apache License 2.0 (see [LICENSE](LICENSE)).
