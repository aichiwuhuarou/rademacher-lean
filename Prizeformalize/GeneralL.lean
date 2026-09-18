import Prizeformalize.Basic
import Mathlib

/-!
# Khadzhiivanov-Nikiforov / Erdős (1962): triangles above the Turán threshold, general `l`

Target theorem: every graph on `n` vertices with at least `⌊n²/4⌋ + l` edges (`2l < n`)
contains at least `l * ⌊n/2⌋` triangles.

The `l = 1` case is `Rad.rademacher` in `Prizeformalize.Basic`. This file develops
the general case in stages following Erdős (1962), "On a theorem of
Rademacher-Turán", Illinois J. Math. 6 (1962), 122-127.
-/

namespace Rad

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Stage 1: Gallai-Erdős-Andrásfai lemma -/

/-- In a triangle-free graph, no two neighbors of a vertex are adjacent. -/
lemma not_adj_neighbors (h : G.CliqueFree 3) (v w₁ w₂ : V)
    (hw₁ : G.Adj v w₁) (hw₂ : G.Adj v w₂) (hne : w₁ ≠ w₂) : ¬ G.Adj w₁ w₂ := by
  intro hadj
  have hcl : G.IsClique ({v, w₁, w₂} : Finset V) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hw₁
    · exact hw₂
    · exact hw₁.symm
    · exact absurd rfl hxy
    · exact hadj
    · exact hw₂.symm
    · exact hadj.symm
    · exact absurd rfl hxy
  exact h ({v, w₁, w₂} : Finset V) ⟨hcl, by
    rw [Finset.card_insert_of_notMem (by
        intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hw₁.ne h
        · exact hw₂.ne (Finset.mem_singleton.mp h)),
      Finset.card_insert_of_notMem (by
        intro hmem
        exact hne (Finset.mem_singleton.mp hmem)),
      Finset.card_singleton]⟩

/-! ### Arithmetic core for Gallai lemma -/

/-- Arithmetic inequality: for k ≥ 2 and N ≥ 0,
`(2k+1) + 2N + ⌊N²/4⌋ ≤ ⌊(N+2k)²/4⌋ + 1`.
This is the key computation in the Gallai–Erdős–Andrásfai proof. -/
lemma gallai_arith (k N : ℕ) (hk : 2 ≤ k) :
    (2*k + 1) + 2*N + N^2/4 ≤ (N + 2*k)^2/4 + 1 := by
  -- Expand (N+2k)² = N² + 4(kN + k²)
  have hexpand : (N + 2*k)^2 = N^2 + 4*(k*N + k*k) := by ring
  -- Extract the 4-divisible part: (N² + 4x)/4 = N²/4 + x
  have hdiv : (N^2 + 4*(k*N + k*k))/4 = N^2/4 + (k*N + k*k) :=
    Nat.add_mul_div_left (N^2) (k*N + k*k) (by norm_num : 0 < 4)
  rw [hexpand, hdiv]
  -- Now: 2k+1 + 2N + N²/4 ≤ N²/4 + kN + k² + 1
  -- Cancel N²/4 and 1: need 2k + 2N ≤ kN + k²
  have h1 : 2*N ≤ k*N := Nat.mul_le_mul_right N hk
  have h2 : 2*k ≤ k*k := Nat.mul_le_mul_right k hk
  omega

/-- **Gallai–Erdős–Andrásfai lemma** (statement; proof in progress).
A triangle-free graph on `n` vertices that is not bipartite
has at most `⌊(n-1)²/4⌋ + 1` edges. -/
theorem gallai_erdos_andrasfai (h_tri : G.CliqueFree 3) (h_bip : ¬ G.IsBipartite) :
    G.edgeFinset.card ≤ (Fintype.card V - 1) ^ 2 / 4 + 1 := by
  sorry

/-! ### Stage 2: Linear book lemma -/

/-- Number of triangles containing a given pair of adjacent vertices
(the "book size" at edge `a—b`). -/
def bookSize (a b : V) : ℕ :=
  (Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj b v ∧ a ≠ v ∧ b ≠ v)).card

/-- **Linear book lemma.** A graph on `n` vertices with more than `⌊n²/4⌋` edges
contains an edge lying in at least `⌊n/18⌋` triangles.

Proof (Erdős 1962, Lemma 2, simplified):
1. G contains a triangle (by Mantel, since e(G) > ⌊n²/4⌋).
2. For any triangle {a,b,c} in G, the sum d(a)+d(b)+d(c) counts
   triangle-vertices-adjacent-to-non-triangle-vertices plus internal edges.
3. If d(a)+d(b)+d(c) ≥ n(1+1/18) for some triangle, then by pigeonhole
   one pair has ≥ n/18 common neighbors (the book size).
4. Otherwise, every triangle has degree-sum < n(1+1/18); combined with
   Mantel on the graph minus a maximal triangle packing, this forces
   e(G) ≤ ⌊n²/4⌋, contradicting the hypothesis.
The constant 1/18 comes from the specific counting in step 3-4. -/
theorem linear_book (he : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    ∃ a b : V, G.Adj a b ∧ Fintype.card V / 18 ≤ bookSize G a b := by
  classical
  -- Step 1: G has at least one triangle (Mantel contrapositive)
  obtain ⟨t₀, ht₀⟩ := Rad.exists_mem_cliqueFinset_three G he
  -- Step 2: maximal vertex-disjoint triangle family exists by finiteness.
  -- Step 3: degree-sum pigeonhole gives a triangle with d(a)+d(b)+d(c) large.
  -- Step 4: pair with ≥ n/18 common neighbors.
  sorry

/-- **Pair pigeonhole.** If a triangle {a,b,c} has degree-sum exceeding
`n + n/18 + 2`, then some edge of it has book size ≥ n/18.

Mathematical content: for adjacent a,b, every common neighbor of a and b
(other than a,b themselves) forms a triangle with edge a—b, so
bookSize G a b = |N(a) ∩ N(b)| - (contributions of a,b if adjacent...).
By inclusion-exclusion:
  |N(a)∩N(b)| + |N(b)∩N(c)| + |N(c)∩N(a)| ≥ d(a)+d(b)+d(c) - n - 3
so if d(a)+d(b)+d(c) > n + n/18 + 3 then some pair has
|N(x)∩N(y)| > n/18 / 3 · ... (pigeonhole among 3 pairs). -/
theorem pair_pigeonhole (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (n : ℕ) (hn : n + n/18 + 6 ≤ G.degree a + G.degree b + G.degree c)
    (hcard : Fintype.card V = n) :
    ∃ x y : V, G.Adj x y ∧ n / 18 ≤ bookSize G x y := by
  -- Common neighborhood inclusion-exclusion:
  -- |N(a)∩N(b)| ≥ d(a) + d(b) - n, etc.
  -- Sum: Σ|N(x)∩N(y)| ≥ (d(a)+d(b)+d(c))·2 - 3n ≥ 2(n + n/18 + 6) - 3n
  -- But we need each |N(x)∩N(y)| properly counts book size.
  sorry

/-- **Relative book lemma** (statement; proof in progress). -/
theorem relative_book (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1)
    (he : (Fintype.card V : ℝ) ^ 2 / 4 - (Fintype.card V : ℝ) / 2 * (1 - δ)
      ≤ (G.edgeFinset.card : ℝ))
    (h_tri : (G.cliqueFinset 3).Nonempty) :
    ∃ a b : V, G.Adj a b ∧ Fintype.card V / 36 ≤ bookSize G a b := by
  sorry

/-! ### Stage 4: Main assembly -/

/-- **Erdős 1962 (general `l`).** There exists `c > 0` (we take `c = 1/18`) such
that for any `l < c * n`, every graph on `n` vertices with at least `⌊n²/4⌋ + l`
edges contains at least `l * ⌊n/2⌋` triangles. -/
theorem erdos_1962_general (l : ℕ)
    (hl : 2 * l < Fintype.card V / 18)
    (he : Fintype.card V ^ 2 / 4 + l ≤ G.edgeFinset.card) :
    l * (Fintype.card V / 2) ≤ (G.cliqueFinset 3).card := by
  sorry

end Rad
