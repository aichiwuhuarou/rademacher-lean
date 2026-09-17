# The informal proof

This is the informal write-up that the Lean formalization in
`Prizeformalize/Basic.lean` follows. It was assembled from public lecture
materials and independently re-verified (each numerical identity re-derived);
three gaps found in a widely-circulated transcription were repaired here.

## 2. PROOF A — Complete elementary proof of Theorem R (l = 1), verified step by step

*(Method tags: [monotonicity], [counting/handshake], [induction], [Mantel].)*

**A.0 External input.** Mantel's theorem: a triangle-free graph on N vertices has at most
⌊N²/4⌋ edges. (Standard; already available in Lean libraries via Turán.)

**A.1 Monotone reduction. [monotonicity]**
Deleting an edge cannot increase T. Hence it suffices to prove the "at least" form, and
inside the induction we may always pass to a spanning subgraph with exactly
⌊N²/4⌋ + 1 edges whenever an N-vertex graph has more (T only decreases). We prove:

> **P(n):** every graph on n ≥ 3 vertices with **at least** ⌊n²/4⌋ + 1 edges has
> ≥ ⌊n/2⌋ triangles.

by strong induction on n. (In the steps below, G − v, G − v − e* etc. may have more than
⌊·⌋+1 edges; P is stated with "at least" precisely so that the induction hypothesis
applies to them directly.)

**A.2 Base cases. [counting]**
- n = 3: ⌊9/4⌋ + 1 = 3, so G = K₃, T = 1 = ⌊3/2⌋. ✔
- n = 4: ⌊16/4⌋ + 1 = 5 = C(4,2) − 1, so G is K₄ minus one edge, which has exactly
  2 = ⌊4/2⌋ triangles. ✔

**A.3 Inductive step, odd n = 2m + 1 (m ≥ 2, i.e. n ≥ 5). [handshake + induction]**
Here ⌊n²/4⌋ + 1 = m² + m + 1. Suppose, for contradiction, δ(G) ≥ m + 1. Then by the
handshake lemma
  2(m² + m + 1) = 2e(G) = Σ_v d(v) ≥ (2m + 1)(m + 1) = 2m² + 3m + 1,
which gives 2m² + 2m + 2 ≥ 2m² + 3m + 1, i.e. m ≤ 1 — contradicting m ≥ 2.
Hence δ(G) ≤ m; pick v with d(v) ≤ m. Then
  e(G − v) ≥ (m² + m + 1) − m = m² + 1 = ⌊(2m)²/4⌋ + 1,
i.e. G − v (on n − 1 = 2m ≥ 4 vertices) satisfies the hypothesis of P(2m). By strong
induction, T(G − v) ≥ ⌊2m/2⌋ = m. Finally T(G) ≥ T(G − v) ≥ m = ⌊n/2⌋. ✔
(No triangle through v is needed in the odd case.)

**A.4 Inductive step, even n = 2m (m ≥ 3, i.e. n ≥ 6). [Mantel + counting + induction]**
Here e(G) ≥ m² + 1 and ⌊n/2⌋ = m. Since m² + 1 > m² = ⌊n²/4⌋, Mantel's theorem gives
that G contains **at least one triangle**; let S = set of vertices lying in ≥ 1 triangle,
so |S| ≥ 3. (If e(G) > m² + 1, first pass to a spanning subgraph with exactly m² + 1
edges, per A.1 — so we may read e(G) = m² + 1 in what follows.)

*Case A.4.1: δ(G) ≤ m − 1.* Pick v of minimum degree. Then
  e(G − v) ≥ m² + 1 − (m − 1) = m² − m + 2 = ⌊(2m−1)²/4⌋ + 2.
  - **A.4.1a: v lies in a triangle of G.** Then
    e(G − v) ≥ ⌊(n−1)²/4⌋ + 1, so by P(2m − 1), T(G − v) ≥ ⌊(2m−1)/2⌋ = m − 1; and the
    triangles of G consisting of v plus two neighbors of v are absent from G − v, so
    T(G) ≥ T(G − v) + 1 ≥ m. ✔
  - **A.4.1b: v lies in no triangle.** Then T(G) = T(G − v). Moreover
    e(G − v) ≥ m² − m + 2 > m² − m = ⌊(2m−1)²/4⌋, so by Mantel's theorem G − v contains
    a triangle; choose an edge e* of G − v that lies in ≥ 1 triangle of G − v. Then
    T(G − v) ≥ T(G − v − e*) + 1, and e(G − v − e*) ≥ m² − m + 1 = ⌊(2m−1)²/4⌋ + 1, so
    P(2m − 1) gives T(G − v − e*) ≥ m − 1. Hence T(G) = T(G − v) ≥ m. ✔

*Case A.4.2: δ(G) ≥ m.* By the handshake lemma,
  Σ_v (d(v) − m) = 2e(G) − mn = (2m² + 2) − 2m² = 2.
Every summand is ≥ 0 (δ ≥ m), hence **at most 2 vertices have d(v) ≥ m + 1**.
Since |S| ≥ 3, some w ∈ S has d(w) ≤ m. Then
  e(G − w) ≥ m² + 1 − m = m² − m + 1 = ⌊(2m−1)²/4⌋ + 1,
so P(2m − 1) gives T(G − w) ≥ m − 1, and w lies in a triangle of G not present in
G − w, so T(G) ≥ (m − 1) + 1 = m. ✔

This completes the induction; P(n) holds for all n ≥ 3, and Theorem R follows. ∎

**Verification status of Proof A: every numerical identity above was independently
re-derived and checked (including Σ(d−m) = 2 in A.4.2 — note this argument is only
valid because δ ≥ m makes all summands nonnegative). The proof uses only: edge/vertex
monotonicity of T, the handshake lemma, Mantel's theorem, and strong induction on n.**

**Why the natural extension to general l fails (important for planning).** Running the
same argument with e = ⌊n²/4⌋ + l gives Σ(d − n/2) = 2l, so one can still find a
triangle-vertex w of degree ≤ ⌊n/2⌋ *provided* |S| > 2l — unproven in general — and even
then deleting w costs l·1 triangles from the budget (IH gives l(m−1), one needs lm),
i.e. one would need a vertex lying in ≥ ⌊n/2⌋ triangles ("large book"). For l = 1 the
book needed is just of size 1, which is free; for general l the required statement is
essentially the (hard, partially open) Erdős book problem territory. This is exactly the
obstruction that makes Theorem KN hard and its known proofs long. See §6.

---



## 7. Source links (all accessed 2026-09-17)

- Math.SE question with Duke pset proof transcription:
  https://math.stackexchange.com/questions/4929024/minimum-number-of-triangles-in-a-graph-with-at-least-lfloor-fracn24-rfloo
- Duke Math 290-60 Problem Set 1 (origin of Proof B; now 404):
  services.math.duke.edu/~hlijiang/pset1.pdf
- Erdős 1962, Illinois J. Math. 6, 122–127:
  https://combinatorica.hu/~p_erdos/1962-09.pdf
- Lovász–Simonovits Part II (1983), Studies in Pure Mathematics:
  https://renyi.hu/~miki/LovSimBirk.pdf
- Lovász–Simonovits Part I (1976), Proc. 5th British Comb. Conf. (Aberdeen),
  Congressus Numerantium XV, 431–442 (not open access).
- Khadzhiivanov–Nikiforov (1981), C. R. Acad. Bulgare Sci. 34 (not digitized).
- Yufei Zhao, Graph Theory and Additive Combinatorics (book/OCW notes) — Exercises
  1.1.4–1.1.10, in particular Exercise 1.1.8 = Rademacher (statement only, no proof):
  https://yufeizhao.com/gtacbook/ ; MIT OCW 18.225 lecture notes:
  https://ocw.mit.edu/courses/18-225-graph-theory-and-additive-combinatorics-fall-2023/lists/lecture-notes/
- Balogh–Clemen, On stability of the Erdős–Rademacher problem (arXiv:2003.12917) —
  historical confirmation that the general-l theorem is due to Lovász–Simonovits [10]
  (= Part I) and Khadzhiivanov–Nikiforov: https://arxiv.org/abs/2003.12917
- Liu–Pikhurko, A note on extremal constructions for the Erdős–Rademacher problem
  (arXiv:2311.18753) — exact minimum clique counts above Turán:
  https://arxiv.org/abs/2311.18753

Local artifacts:
- `papers/lovsim_clean.txt` — full text of L–S Part II (for detailed step-by-step
  extraction during formalization).
- `papers/erdos_clean.txt` — full text of Erdős 1962.
- `papers/zhao_ch1_clean.txt` — Zhao book chapter 1 (Exercises 1.1.4–1.1.10 text).
