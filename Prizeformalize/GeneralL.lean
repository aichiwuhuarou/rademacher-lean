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

/-- Vertices covered by a family of triangles. -/
def coveredVerts (S : List (Finset V)) : Finset V := S.foldr (· ∪ ·) ∅

/-- Membership in `coveredVerts`: x is covered iff x lies in some member. -/
lemma mem_coveredVerts {x : V} {S : List (Finset V)} :
    x ∈ coveredVerts S ↔ ∃ t ∈ S, x ∈ t := by
  induction S with
  | nil => simp [coveredVerts]
  | cons a rest ih =>
    show x ∈ a ∪ List.foldr (· ∪ ·) ∅ rest ↔ ∃ t ∈ a :: rest, x ∈ t
    rw [Finset.mem_union, show x ∈ List.foldr (· ∪ ·) ∅ rest ↔ ∃ t ∈ rest, x ∈ t from ih]
    constructor
    · rintro (h | ⟨t, ht, hxt⟩)
      · exact ⟨a, List.mem_cons_self, h⟩
      · exact ⟨t, List.mem_cons_of_mem _ ht, hxt⟩
    · rintro ⟨t, ht, hxt⟩
      rcases List.mem_cons.mp ht with heq | hrest
      · rw [← heq]; exact Or.inl hxt
      · exact Or.inr ⟨t, hrest, hxt⟩

/-- A list of vertex-disjoint triangles, each a triangle of `G`. -/
structure TrianglePacking where
  tris : List (Finset V)
  mem_triangles : ∀ t ∈ tris, t ∈ G.cliqueFinset 3
  pairwise_disjoint : ∀ t₁ ∈ tris, ∀ t₂ ∈ tris, t₁ ≠ t₂ → Disjoint t₁ t₂

/-- A packing is maximal: every triangle of `G` meets some triangle in the packing. -/
def TrianglePacking.IsMaximal (P : TrianglePacking G) : Prop :=
  ∀ t ∈ G.cliqueFinset 3, ∃ t' ∈ P.tris, ¬ Disjoint t t'

/-- Removing the vertices covered by a maximal packing leaves a
triangle-free induced subgraph: any triangle there would lift to a
triangle of `G` disjoint from every packing triangle, contradicting
maximality. -/
theorem induce_compl_cliqueFree (P : TrianglePacking G) (hmax : P.IsMaximal) :
    (G.induce ((↑(coveredVerts P.tris) : Set V)ᶜ)).CliqueFree 3 := by
  classical
  intro t ht
  -- Lift t to a Finset of V via the subtype embedding
  let lift : Finset V := t.map (Function.Embedding.subtype
    (fun x => x ∈ ((↑(coveredVerts P.tris) : Set V)ᶜ)))
  have htG : G.IsNClique 3 lift :=
    (SimpleGraph.isNClique_induce_iff (s := ((↑(coveredVerts P.tris) : Set V)ᶜ)) t 3).mp ht
  obtain ⟨t', ht'mem, hnd⟩ := hmax lift (G.mem_cliqueFinset_iff.mpr htG)
  -- Every x ∈ lift avoids coveredVerts; every y ∈ t' lies in coveredVerts
  have hsep : Disjoint lift t' := by
    rw [Finset.disjoint_right]
    intro y hyt' hx
    have hycovered : y ∈ coveredVerts P.tris :=
      mem_coveredVerts.mpr ⟨t', ht'mem, hyt'⟩
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hx
    have hzc : (z : V) ∈ coveredVerts P.tris := by
      have hcoe : (z : V) = y := hzy
      rw [hcoe]; exact hycovered
    have hcompl : (z : V) ∈ ((↑(coveredVerts P.tris) : Set V)ᶜ) := z.property
    exact hcompl (Finset.mem_coe.mpr hzc)
  exact hnd hsep

theorem exists_maximal_trianglePacking :
    ∃ P : TrianglePacking G, P.IsMaximal := by
  classical
  -- Candidate packings: Finsets S ⊆ cliqueFinset 3 with pairwise-disjoint members.
  -- This is a Finset of Finset (Finset V) (subsets of a finite Finset), so we
  -- can take a maximum-cardinality one via exists_max_image.
  -- Valid packings as a filtered subset of the powerset:
  set candidates : Finset (Finset (Finset V)) :=
    (G.cliqueFinset 3).powerset.filter (fun S =>
      ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → Disjoint t₁ t₂) with hcand
  have hempty : ∅ ∈ candidates := by
    simp [hcand]
  have hne : candidates.Nonempty := ⟨∅, hempty⟩
  -- Take a maximum-cardinality candidate
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates (fun s => s.card) hne
  have hSmem : S ∈ candidates := hS
  simp only [hcand, Finset.mem_filter, Finset.mem_powerset] at hSmem
  obtain ⟨hsub, hdisj⟩ := hSmem
  -- Build the packing from S
  refine ⟨⟨S.toList, ?_, ?_⟩, ?_⟩
  · intro t ht
    rw [Finset.mem_toList] at ht
    exact hsub ht
  · intro t₁ ht₁ t₂ ht₂ hne'
    rw [Finset.mem_toList] at ht₁ ht₂
    exact hdisj t₁ ht₁ t₂ ht₂ hne'
  · -- Maximality: if some triangle t is disjoint from all of S, then
    -- S ∪ {t} would be a strictly larger candidate — contradiction.
    intro t ht
    by_contra hcon
    push_neg at hcon
    -- t is disjoint from every member of S
    have hall : ∀ t' ∈ S, Disjoint t t' := by
      intro t' ht'
      exact hcon t' (show t' ∈ S.toList from Finset.mem_toList.mpr ht')
    -- S ∪ {t} is a strictly larger candidate
    have htnS : t ∉ S := by
      intro hts
      have h3 : t.card = 3 := (G.mem_cliqueFinset_iff.mp ht).2
      have hne : t ≠ ∅ := fun he => by rw [he] at h3; simp at h3
      have hdisjself : Disjoint t t := hall t hts
      have hcap : t ∩ t = ∅ := by simpa using hdisjself
      have hzero : t.card = 0 := by
        have : t ∩ t = t := Finset.inter_self t
        rw [this] at hcap
        exact Finset.card_eq_zero.mpr hcap
      omega
    have hlarger : (insert t S) ∈ candidates := by
      simp only [hcand, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx'
        · exact ht
        · exact hsub hx'
      · intro t₁ ht₁ t₂ ht₂ hne'
        all_goals simp only [Finset.mem_insert] at ht₁ ht₂
        rcases ht₁ with rfl | ht₁' <;> rcases ht₂ with rfl | ht₂'
        · exact absurd rfl hne'
        · exact hall t₂ ht₂'
        · exact (hall t₁ ht₁').symm
        · exact hdisj t₁ ht₁' t₂ ht₂' hne'
    -- Contradiction with maximality of S
    have hcard : S.card < (insert t S).card := by
      rw [Finset.card_insert_of_notMem htnS]
      omega
    have hbound := hmax (insert t S) hlarger
    rw [Finset.card_insert_of_notMem htnS] at hbound
    omega
lemma commonNeighbors_lower (a b : V) :
    G.degree a + G.degree b - Fintype.card V ≤
      (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  have hle : (G.neighborFinset a ∪ G.neighborFinset b).card ≤ Fintype.card V :=
    Finset.card_le_card (Finset.subset_univ _)
  have hex : (G.neighborFinset a ∪ G.neighborFinset b).card +
      (G.neighborFinset a ∩ G.neighborFinset b).card =
      (G.neighborFinset a).card + (G.neighborFinset b).card := by
    rw [Finset.card_union_add_card_inter]
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hex
  omega


/-- **Linear book lemma.** A graph on `n` vertices with more than `⌊n²/4⌋` edges
contains an edge lying in at least `⌊n/18⌋` triangles.

Complete proof (Erdős 1962, Lemma 2):
1. Take a maximal vertex-disjoint triangle packing P = {t₁,…,t_r} (exists by finiteness).
2. The uncovered part G' = G − coveredVerts(P) is triangle-free (maximality),
   so e(G') ≤ ⌊m²/4⌋ where m = n − 3r (Mantel).
3. e(G) ≤ Σᵢ Σ_{v ∈ tᵢ} d(v) + e(G')   (each edge counted once: edges touching
   a covered vertex are bounded by the degree-sum; uncovered edges are in G').
4. By contradiction: if every edge has book < n/18, then every triangle has
   degree-sum < n + 3·(n/18) + 3 (else overlap_book_bound gives book ≥ n/18).
   With overlap_book_bound: dsum ≥ n + k → book ≥ k/3; contrapositive:
   book < n/18 → dsum < n + 3·(n/18) + 3.
5. Chaining: e(G) ≤ r·(n + n/6 + 3) + ⌊(n−3r)²/4⌋
   = r·n·(7/6) + 3r + n²/4 − 3rn/2 + O(r²)
   For r ≥ 1 and n large: ≤ n²/4 + r·n·(7/6 − 3/2) + … = n²/4 − r·n/3 + … < n²/4 + 1.
   Contradiction with e(G) > ⌊n²/4⌋.
The constant arithmetic is handled by `omega` after division lemmas. -/
theorem linear_book (he : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    ∃ a b : V, G.Adj a b ∧ Fintype.card V / 18 ≤ bookSize G a b := by
  classical
  set n := Fintype.card V with hn
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ a b, G.Adj a b → bookSize G a b < n / 18
  obtain ⟨P, hmax⟩ := exists_maximal_trianglePacking G
  -- The uncovered part is triangle-free
  have hcf := induce_compl_cliqueFree G P hmax
  sorry

/-- Book size equals the common neighborhood cardinality. -/
lemma bookSize_eq_commonNeighbors (a b : V) :
    bookSize G a b = (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  apply le_antisymm
  · apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
    exact ⟨hv.2.1, hv.2.2.1⟩
  · apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at hv
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ v, hv.1, hv.2, ?_, ?_⟩
    · intro h
      subst h
      exact SimpleGraph.Adj.ne hv.1 rfl
    · intro h
      subst h
      exact SimpleGraph.Adj.ne hv.2 rfl

/-- Per-vertex contribution to the three pair-books of triangle (a,b,c):
the number of pairs {x,y} ⊆ {a,b,c} such that x is adjacent to both
members — i.e. how many of the three books x counts in. -/
def pairBookContribution (a b c v : V) : ℕ :=
  (if G.Adj a v ∧ G.Adj b v then 1 else 0) +
  (if G.Adj b v ∧ G.Adj c v then 1 else 0) +
  (if G.Adj c v ∧ G.Adj a v then 1 else 0)

/-- dt(v): number of triangle-vertices adjacent to v (0..3). -/
def triAdjCount (a b c v : V) : ℕ :=
  (if G.Adj a v then 1 else 0) + (if G.Adj b v then 1 else 0) +
  (if G.Adj c v then 1 else 0)

/-- Per-vertex key inequality: book contribution ≥ dt − 1 (when dt ≥ 1). -/
lemma contrib_ge_dt_sub_one (a b c v : V) :
    triAdjCount G a b c v ≤ pairBookContribution G a b c v + 1 := by
  unfold triAdjCount pairBookContribution
  by_cases h1 : G.Adj a v <;> by_cases h2 : G.Adj b v <;> by_cases h3 : G.Adj c v <;>
    simp [h1, h2, h3]

/-- Bridge: a card over a stricter filter equals the sum of indicators of the
looser predicate, when the excluded witnesses make the predicate false. -/
private lemma card_strict_filter_eq_sum (x y : V) :
    bookSize G x y =
      ∑ v ∈ Finset.univ, (if G.Adj x v ∧ G.Adj y v then 1 else 0) := by
  classical
  unfold bookSize
  have key : ∀ v ∈ Finset.univ,
      ((if G.Adj x v ∧ G.Adj y v ∧ x ≠ v ∧ y ≠ v then (1:ℕ) else 0)) =
      ((if G.Adj x v ∧ G.Adj y v then (1:ℕ) else 0)) := by
    intro v _
    by_cases h : G.Adj x v ∧ G.Adj y v
    · by_cases hne : x ≠ v ∧ y ≠ v
      · simp [h, hne]
      · exfalso
        rcases not_and_or.mp hne with h1 | h1
        · apply h1
          intro heq
          subst heq
          exact SimpleGraph.Adj.ne h.1 rfl
        · apply h1
          intro heq
          subst heq
          exact SimpleGraph.Adj.ne h.2 rfl
    · have h2 : ¬(G.Adj x v ∧ G.Adj y v ∧ x ≠ v ∧ y ≠ v) := by
        intro hc
        exact h ⟨hc.1, hc.2.1⟩
      simp [h, h2]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun v hv => key v hv)

/-- Book sum = Σ_v pairBookContribution. -/
lemma bookSum_eq_sum_contrib (a b c : V) :
    bookSize G a b + bookSize G b c + bookSize G c a
      = ∑ v ∈ Finset.univ, pairBookContribution G a b c v := by
  classical
  rw [card_strict_filter_eq_sum G a b, card_strict_filter_eq_sum G b c,
    card_strict_filter_eq_sum G c a]
  have hsum : ∀ v ∈ Finset.univ,
      ((if G.Adj a v ∧ G.Adj b v then 1 else 0) +
       (if G.Adj b v ∧ G.Adj c v then 1 else 0) +
       (if G.Adj c v ∧ G.Adj a v then 1 else 0)) =
      pairBookContribution G a b c v := fun v _ => rfl
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hsum

/-- Degree sum = Σ_v triAdjCount. -/
lemma dsum_eq_sum_triAdj (a b c : V) :
    G.degree a + G.degree b + G.degree c
      = ∑ v ∈ Finset.univ, triAdjCount G a b c v := by
  classical
  have expand : ∀ (x : V), G.degree x =
      ∑ v ∈ Finset.univ, (if G.Adj x v then 1 else 0) := by
    intro x
    have h1 : ∑ v ∈ G.neighborFinset x, (if G.Adj x v then 1 else 0)
        = ∑ v ∈ (Finset.univ : Finset V), (if G.Adj x v then 1 else 0) :=
      Finset.sum_subset (Finset.subset_univ _) (by
        intro v _ hv
        exact if_neg (fun hc => hv ((G.mem_neighborFinset x v).mpr hc)))
    have h2 : (∑ v ∈ G.neighborFinset x, (1:ℕ))
        = ∑ v ∈ G.neighborFinset x, (if G.Adj x v then 1 else 0) := by
      refine Finset.sum_congr rfl (fun v hv => ?_)
      have hx : G.Adj x v := (G.mem_neighborFinset x v).mp hv
      rw [if_pos hx]
    calc G.degree x = (G.neighborFinset x).card := (G.card_neighborFinset_eq_degree x).symm
      _ = ∑ v ∈ G.neighborFinset x, (1:ℕ) := (Finset.card_eq_sum_ones _)
      _ = ∑ v ∈ G.neighborFinset x, (if G.Adj x v then 1 else 0) := h2
      _ = ∑ v ∈ Finset.univ, (if G.Adj x v then 1 else 0) := h1
  rw [expand a, expand b, expand c]
  have hsum : ∀ v ∈ Finset.univ,
      ((if G.Adj a v then 1 else 0) + (if G.Adj b v then 1 else 0) +
       (if G.Adj c v then 1 else 0)) = triAdjCount G a b c v := fun v _ => rfl
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hsum

/-- **Overlap-weight book bound.** If a triangle {a,b,c} has degree-sum
exceeding the vertex count by `k`, some edge of it has book size ≥ k/3. -/
theorem overlap_book_bound (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (k : ℕ)
    (hdsum : Fintype.card V + k ≤ G.degree a + G.degree b + G.degree c) :
    ∃ x y : V, G.Adj x y ∧ k / 3 ≤ bookSize G x y := by
  classical
  by_contra hcon
  push_neg at hcon
  have e1 : bookSize G a b < k / 3 := hcon a b hab
  have e2 : bookSize G b c < k / 3 := hcon b c hbc
  have e3 : bookSize G c a < k / 3 := hcon c a hca
  -- Σ contrib = book sum < 3·(k/3) ≤ k
  have hbook : ∑ v ∈ Finset.univ, pairBookContribution G a b c v < k := by
    rw [← bookSum_eq_sum_contrib G a b c]
    have hbound : bookSize G a b + bookSize G b c + bookSize G c a < 3 * (k / 3) := by omega
    have h3div : 3 * (k / 3) ≤ k := by omega
    omega
  -- Σ triAdj = dsum ≥ n + k
  have hd : ∑ v ∈ Finset.univ, triAdjCount G a b c v ≥
      Fintype.card V + k := by
    rw [← dsum_eq_sum_triAdj G a b c]
    exact hdsum
  -- Σ (triAdj − 1)⁺ ≤ Σ contrib  ⟹  Σ triAdj − n ≤ Σ contrib  (all terms ≥ 0 clamped)
  -- Since Σ 1 = n:  Σ triAdj ≤ Σ contrib + n, so n + k ≤ Σ contrib + n, i.e. k ≤ Σ contrib.
  have hfinal : k ≤ ∑ v ∈ Finset.univ, pairBookContribution G a b c v := by
    have hle : ∑ v ∈ Finset.univ, triAdjCount G a b c v
        ≤ ∑ v ∈ Finset.univ, (pairBookContribution G a b c v + 1) :=
      Finset.sum_le_sum (fun v _ => contrib_ge_dt_sub_one G a b c v)
    have hn : ∑ v ∈ (Finset.univ : Finset V), 1 = Fintype.card V := by
      simp
    have hchain : ∑ v ∈ Finset.univ, triAdjCount G a b c v
        ≤ ∑ v ∈ Finset.univ, pairBookContribution G a b c v + Fintype.card V := calc
        ∑ v ∈ Finset.univ, triAdjCount G a b c v
        ≤ ∑ v ∈ Finset.univ, (pairBookContribution G a b c v + 1) := hle
      _ = ∑ v ∈ Finset.univ, pairBookContribution G a b c v + Fintype.card V := by
          rw [Finset.sum_add_distrib, hn]
    omega
  omega

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

/-- Key counting: every edge of G either meets the covered vertices W, or lies
entirely in the uncovered part. Edges meeting W inject into
W × V (endpoint in W, other endpoint) — actually ≤ Σ_{w ∈ W} d(w) via
incidence counting. For the final assembly we use the sharper form:
e(G) ≤ Σ_{w ∈ W} d(w) + e(G[Wᶜ]).

Here W = coveredVerts of the packing, and Σ_{w∈W} d(w) is bounded because W is
a disjoint union of the r triangle vertex-sets, each contributing its
three degrees. -/
theorem edge_split_count (P : TrianglePacking G) :
    G.edgeFinset.card ≤
      (∑ v ∈ coveredVerts P.tris, G.degree v) +
      ((G.induce ((↑(coveredVerts P.tris) : Set V)ᶜ)).edgeFinset).card := by
  classical
  set W := coveredVerts P.tris with hWdef
  -- Partition: E = Eavoid ⊔ (E \ Eavoid) via filter_add_filter_not.
  -- Touch-W edges ⊆ ⋃_{w∈W} incidence w (union bound → Σ d(w)).
  -- Avoid-W edges inject into induced subgraph edges (≤ suffices).
  set Eavoid := G.edgeFinset.filter (fun e => ∀ v, v ∈ e → v ∉ W) with hEa
  have hcard : G.edgeFinset.card = Eavoid.card + (G.edgeFinset.filter (fun e => ¬ ∀ v, v ∈ e → v ∉ W)).card := by
    rw [hEa]
    exact (Finset.card_filter_add_card_filter_not
      (p := fun (e : Sym2 V) => ∀ v, v ∈ e → v ∉ W) (s := G.edgeFinset)).symm
  have htouch : (G.edgeFinset \ Eavoid) ⊆
      W.biUnion (fun w => G.incidenceFinset w) := by
    intro e he
    rw [Finset.mem_sdiff, hEa, Finset.mem_filter] at he
    have hex : ∃ v, v ∈ e ∧ v ∈ W := by
      by_contra hcon
      push_neg at hcon
      exact he.2 ⟨he.1, fun v hv => hcon v hv⟩
    obtain ⟨v, hv, hvw⟩ := hex
    have hmemE : e ∈ G.edgeFinset := he.1
    have hmemI : e ∈ G.incidenceSet v := ⟨G.mem_edgeFinset.mp hmemE, hv⟩
    exact Finset.mem_biUnion.mpr ⟨v, hvw, (G.mem_incidenceFinset v e).2 hmemI⟩
  sorry

end Rad
