import Mathlib

/-!
# Rademacher's theorem and the Nikiforov–Khadzhiivanov generalization

Every graph on `n` vertices with at least `n ^ 2 / 4 + l` edges
(`1 ≤ l`, `2 * l < n`) contains at least `l * (n / 2)` triangles.
The case `l = 1` is Rademacher's theorem (1962); the general case is due to
Khadzhiivanov and Nikiforov (1981).
-/

open SimpleGraph Finset

namespace Rad

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-! ### A 2-clique is exactly an edge -/

theorem exists_pair_of_mem_cliqueFinset_two [DecidableRel G.Adj]
    {s : Finset V} (hs : s ∈ G.cliqueFinset 2) :
    ∃ x y : V, x ≠ y ∧ s = {x, y} ∧ G.Adj x y := by
  classical
  obtain ⟨hclique, hcard⟩ := G.mem_cliqueFinset_iff.mp hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp at hcard
  · have h1 : (s.erase x).card = 1 := by
      rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨y, hy⟩ := Finset.card_eq_one.1 h1
    have hxyn : x ≠ y := by
      have hy' : y ∈ s.erase x := by rw [hy]; simp
      exact Ne.symm (Finset.mem_erase.1 hy').1
    have hins : s = insert x {y} := by
      rw [(Finset.insert_erase hx).symm, hy]
    have hyms : y ∈ s := Finset.mem_of_mem_erase (by rw [hy]; simp)
    exact ⟨x, y, hxyn, hins, hclique (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hyms) hxyn⟩

/-! ### Mantel's theorem (contrapositive form) -/

/-- The Turán bound for `r = 2` is exactly `⌊n²/4⌋`. -/
theorem turan_two_bound (n : ℕ) :
    (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + ((n % 2).choose 2) = n ^ 2 / 4 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hm : (2 * k) % 2 = 0 := by omega
    have hc0 : Nat.choose 0 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hm, hc0]
    norm_num
  · have h1 : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    have hdiv : ∀ X : ℕ, (4 * X + 1) / 4 = X := fun X => by omega
    have hch : Nat.choose 1 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hm : (2 * k + 1) % 2 = 1 := by omega
    rw [h1, hm, hch, one_pow]
    have hs : 4 * (k * k + k) + 1 - 1 = 4 * (k * k + k) := by omega
    rw [hs]
    have hd2 : ∀ Y : ℕ, 4 * Y / 4 = Y := fun Y => by omega
    rw [hdiv, Nat.mul_one, Nat.add_zero, hd2]

/-- Mantel: more than `⌊n²/4⌋` edges force a triangle. -/
theorem exists_mem_cliqueFinset_three [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    ∃ t, t ∈ G.cliqueFinset 3 := by
  by_contra hcl
  rcases (G.cliqueFinset 3).eq_empty_or_nonempty with hempty | hne
  · have hcf : G.CliqueFree 3 := by
      intro t ht
      have hmem : t ∈ G.cliqueFinset 3 := G.mem_cliqueFinset_iff.2 ht
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty t)
    have h2 := SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) hcf
    have h2' : G.edgeFinset.card ≤ (Fintype.card V ^ 2 - (Fintype.card V % 2) ^ 2)
        * (2 - 1) / (2 * 2) + (Fintype.card V % 2).choose 2 := h2
    rw [turan_two_bound] at h2'
    exact absurd h2' (Nat.not_le.2 h)
  · exact hcl hne

/-! ### Monotonicity -/

theorem cliqueFinset_subset_of_le {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : H ≤ G) :
    H.cliqueFinset 3 ⊆ G.cliqueFinset 3 := by
  intro s hs
  simp only [SimpleGraph.mem_cliqueFinset_iff] at hs ⊢
  obtain ⟨hc, hcard⟩ := hs
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  exact h (hc hx hy hxy)

theorem card_cliqueFinset_mono {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : H ≤ G) :
    (H.cliqueFinset 3).card ≤ (G.cliqueFinset 3).card :=
  Finset.card_le_card (cliqueFinset_subset_of_le h)

/-! ### Peeling a vertex -/

open Classical in
/-- Triangles of the vertex-deleted graph inject into triangles avoiding `v`. -/
theorem card_cliqueFinset_three_induce_compl_le [DecidableRel G.Adj] (v : V) :
    ((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).card ≤
      ((G.cliqueFinset 3).filter (fun s => v ∉ s)).card := by
  classical
  have hsub : ((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).map ((Finset.mapEmbedding (Function.Embedding.subtype (· ∈ ({v}ᶜ : Set V)))).toEmbedding) ⊆
      (G.cliqueFinset 3).filter (fun s => v ∉ s) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 ht
    have hcl : G.IsNClique 3 (u.map (Function.Embedding.subtype (· ∈ ({v}ᶜ : Set V)))) :=
      (SimpleGraph.isNClique_induce_iff {v}ᶜ u 3).1 ((G.induce ({v}ᶜ : Set V)).mem_cliqueFinset_iff.1 hu)
    refine Finset.mem_filter.2 ⟨G.mem_cliqueFinset_iff.2 hcl, ?_⟩
    intro hmem
    obtain ⟨x, hx, hxv⟩ := Finset.mem_map.1 hmem
    exact (Set.mem_compl_singleton_iff.1 x.2) (by simpa using hxv)
  calc ((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).card =
      (((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).map ((Finset.mapEmbedding (Function.Embedding.subtype (· ∈ ({v}ᶜ : Set V)))).toEmbedding)).card :=
        (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- If `v` lies in some triangle, deleting `v` loses at least one triangle. -/
theorem card_cliqueFinset_three_induce_compl_add_one_le [DecidableRel G.Adj]
    {v : V} {t : Finset V} (ht : t ∈ G.cliqueFinset 3) (hvt : v ∈ t) :
    ((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).card + 1 ≤ (G.cliqueFinset 3).card := by
  classical
  have hsplit : ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card +
      ((G.cliqueFinset 3).filter (fun s => v ∉ s)).card = (G.cliqueFinset 3).card := by
    simpa using Finset.card_filter_add_card_filter_not (p := fun s => v ∈ s)
  have hpos : 1 ≤ ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card :=
    Finset.card_pos.2 ⟨t, Finset.mem_filter.2 ⟨ht, hvt⟩⟩
  have hle := card_cliqueFinset_three_induce_compl_le G v
  omega

open Classical in
/-- Edge bookkeeping: deleting `v` removes at most `d(v)` edges. -/
theorem card_edgeFinset_le_induce_compl_add_degree [DecidableRel G.Adj] (v : V) :
    G.edgeFinset.card ≤
      ((G.induce ({v}ᶜ : Set V)).edgeFinset).card + G.degree v := by
  classical
  have hsplit : G.edgeFinset.card =
      (G.edgeFinset \ G.incidenceFinset v).card + G.degree v := by
    rw [Finset.card_sdiff_of_subset (G.incidenceFinset_subset v),
      G.card_incidenceFinset_eq_degree]
    have hdle : G.degree v ≤ G.edgeFinset.card := by
      rw [← G.card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (G.incidenceFinset_subset v)
    omega
  have himg : G.edgeFinset \ G.incidenceFinset v ⊆
      ((G.induce ({v}ᶜ : Set V)).edgeFinset).image (Sym2.map (Subtype.val)) := by
    intro e he
    obtain ⟨hee, hne⟩ := Finset.mem_sdiff.1 he
    obtain ⟨a, b, rfl⟩ := (Sym2.exists (f := fun z => z = e)).mp ⟨e, rfl⟩
    have hb : G.Adj a b := G.mem_edgeSet.1 (G.mem_edgeFinset.1 hee)
    have hva : v ≠ a := by
      intro h
      apply hne
      have hmem : s(a, b) ∈ G.incidenceSet v := by rw [h]; exact (G.mem_incidenceSet a b).2 hb
      exact ((G.mem_incidenceFinset v) _).2 hmem
    have hvb : v ≠ b := by
      intro h
      apply hne
      have hswap : s(b, a) = s(a, b) := by simp
      have hmem0 : s(b, a) ∈ G.incidenceSet b := (G.mem_incidenceSet b a).2 ((G.adj_comm a b).1 hb)
      rw [hswap] at hmem0
      have hmem : s(a, b) ∈ G.incidenceSet v := by rw [h]; exact hmem0
      exact ((G.mem_incidenceFinset v) _).2 hmem
    have ha' : (a : V) ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.2 hva.symm
    have hb' : (b : V) ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.2 hvb.symm
    have hadj : (G.induce ({v}ᶜ : Set V)).Adj ⟨a, ha'⟩ ⟨b, hb'⟩ := hb
    refine Finset.mem_image.2 ⟨s(⟨a, ha'⟩, ⟨b, hb'⟩),
      ((G.induce ({v}ᶜ : Set V)).mem_edgeFinset).2
        ((SimpleGraph.mem_edgeSet (G.induce ({v}ᶜ : Set V))).2 hadj), ?_⟩
    rfl
  have hsd : (G.edgeFinset \ G.incidenceFinset v).card ≤
      ((G.induce ({v}ᶜ : Set V)).edgeFinset).card := by
    calc (G.edgeFinset \ G.incidenceFinset v).card ≤
        (((G.induce ({v}ᶜ : Set V)).edgeFinset).image (Sym2.map (Subtype.val))).card :=
          Finset.card_le_card himg
      _ = ((G.induce ({v}ᶜ : Set V)).edgeFinset).card :=
          Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
  calc G.edgeFinset.card = (G.edgeFinset \ G.incidenceFinset v).card + G.degree v := hsplit
    _ ≤ ((G.induce ({v}ᶜ : Set V)).edgeFinset).card + G.degree v :=
        Nat.add_le_add_right hsd _

/-! ### Deleting an edge -/

open Classical in
/-- Deleting an edge that lies in a triangle `t` loses at least one triangle. -/
theorem card_cliqueFinset_three_deleteEdges_add_one_le [DecidableRel G.Adj] (e : Sym2 V)
    (he : e ∈ G.edgeFinset) {t : Finset V} (ht : t ∈ G.cliqueFinset 3)
    (hsub : ∀ x ∈ e, x ∈ t) :
    ((G.deleteEdges ({e} : Finset (Sym2 V))).cliqueFinset 3).card + 1 ≤
      (G.cliqueFinset 3).card := by
  classical
  have hnot : t ∉ (G.deleteEdges ({e} : Finset (Sym2 V))).cliqueFinset 3 := by
    intro hmem
    obtain ⟨hcl, _⟩ := (G.deleteEdges ({e} : Finset (Sym2 V))).mem_cliqueFinset_iff.1 hmem
    obtain ⟨a, b, rfl⟩ := (Sym2.exists (f := fun z => z = e)).mp ⟨e, rfl⟩
    have ha : a ∈ t := hsub a (by simp)
    have hb : b ∈ t := hsub b (by simp)
    have hGadj : G.Adj a b := G.mem_edgeSet.1 (G.mem_edgeFinset.1 he)
    have hab : a ≠ b := by
      intro h; subst h
      exact hGadj.ne rfl
    have hDeadj := hcl (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab
    simp only [SimpleGraph.deleteEdges_adj] at hDeadj
    exact hDeadj.2 (by simp)
  have hsub2 : (insert t ((G.deleteEdges ({e} : Finset (Sym2 V))).cliqueFinset 3)) ⊆
      G.cliqueFinset 3 := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs'
    · exact ht
    · exact cliqueFinset_subset_of_le (G.deleteEdges_le _) hs'
  have h2 := Finset.card_le_card hsub2
  rwa [Finset.card_insert_of_notMem hnot] at h2

open Classical in
/-- Deleting one edge decreases the edge count by exactly one. -/
theorem card_edgeFinset_deleteEdges_singleton [DecidableRel G.Adj] (e : Sym2 V)
    (he : e ∈ G.edgeFinset) :
    ((G.deleteEdges ({e} : Finset (Sym2 V))).edgeFinset).card + 1 = G.edgeFinset.card := by
  classical
  rw [G.edgeFinset_deleteEdges,
    Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 he),
    Finset.card_singleton]
  have hpos : 1 ≤ G.edgeFinset.card := Finset.card_pos.2 ⟨e, he⟩
  omega

/-! ### Rademacher's theorem (l = 1) -/

open Classical in
/-- For any `k ≤ #edges` there is a spanning subgraph with exactly `k` edges. -/
theorem exists_le_card_edgeFinset_eq [DecidableRel G.Adj] {k : ℕ}
    (hk : k ≤ G.edgeFinset.card) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card = k := by
  classical
  obtain ⟨t, htsub, htcard⟩ := Finset.le_card_iff_exists_subset_card.mp hk
  refine ⟨G.deleteEdges ↑(G.edgeFinset \ t), G.deleteEdges_le _, ?_⟩
  rw [G.edgeFinset_deleteEdges,
    Finset.card_sdiff_of_subset (Finset.sdiff_subset),
    Finset.card_sdiff_of_subset htsub]
  have hle := Finset.card_le_card htsub
  omega

/-- `⌊(2m+1)²/4⌋ = m² + m`. -/
theorem sq_odd_div_four (m : ℕ) : (2 * m + 1) ^ 2 / 4 = m * m + m := by
  have h1 : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
  have hdiv : ∀ X : ℕ, (4 * X + 1) / 4 = X := fun X => by omega
  rw [h1, hdiv]

/-- `⌊(2m)²/4⌋ = m²`. -/
theorem sq_even_div_four (m : ℕ) : (2 * m) ^ 2 / 4 = m * m := by
  have h1 : (2 * m) ^ 2 = 4 * (m * m) := by ring
  have hdiv : ∀ X : ℕ, 4 * X / 4 = X := fun X => by omega
  rw [h1, hdiv]

/-- `⌊(2m−1)²/4⌋ = m² − m`. -/
theorem sq_pred_div_four (m : ℕ) : (2 * m - 1) ^ 2 / 4 = m * m - m := by
  rcases m with _ | m
  · norm_num
  · have h1 : (2 * (m + 1) - 1) ^ 2 = 4 * ((m + 1) * m) + 1 := by
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega]; ring
    have hdiv : ∀ X : ℕ, (4 * X + 1) / 4 = X := fun X => by omega
    have h2 : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
      have hring : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      have hring2 : (m + 1) * m = m * m + m := by ring
      omega
    rw [h1, hdiv, h2]

/-- The set of vertices lying in at least one triangle has size at least 3
when a triangle exists. -/
theorem three_le_card_triangleVerts [DecidableRel G.Adj]
    {t : Finset V} (ht : t ∈ G.cliqueFinset 3) :
    3 ≤ ((G.cliqueFinset 3).biUnion id).card := by
  classical
  have hc : t.card = 3 := (G.mem_cliqueFinset_iff.1 ht).2
  have hsub : t ⊆ (G.cliqueFinset 3).biUnion id :=
    fun x hx => Finset.mem_biUnion.2 ⟨t, ht, hx⟩
  have hle := Finset.card_le_card hsub
  omega

open Classical in
set_option maxHeartbeats 2000000 in
theorem rademacher_core : ∀ (n : ℕ) (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], 3 ≤ n → Fintype.card V = n →
    n ^ 2 / 4 + 1 ≤ G.edgeFinset.card → n / 2 ≤ (G.cliqueFinset 3).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V instFV instDEV G instDAG h3 hcard he
    classical
    -- Base case n = 3: Mantel directly gives a triangle.
    rcases Nat.lt_or_ge n 4 with hn3 | hn4ge
    · -- n = 3
      have hlt : Fintype.card V ^ 2 / 4 < G.edgeFinset.card := by
        rw [hcard]; omega
      obtain ⟨t, ht⟩ := Rad.exists_mem_cliqueFinset_three G hlt
      have : 1 ≤ (G.cliqueFinset 3).card := Finset.card_pos.2 ⟨t, ht⟩
      omega
    · rcases Nat.lt_or_ge n 5 with hn4b | hn5
      · -- n = 4: Mantel gives a triangle `t`. The outside vertex `w` either
        -- completes a second triangle with two vertices of `t`, or has degree ≤ 1,
        -- which forces `e ≤ 3 + 1 < 5`, a contradiction.
        have hltn : n ^ 2 / 4 < G.edgeFinset.card := by omega
        have hlt : Fintype.card V ^ 2 / 4 < G.edgeFinset.card := by
          rw [hcard]; exact hltn
        obtain ⟨t, ht⟩ := Rad.exists_mem_cliqueFinset_three G hlt
        obtain ⟨hcl, hcardt⟩ := G.mem_cliqueFinset_iff.1 ht
        have hu : (Finset.univ : Finset V).card = 4 := by
          rw [Finset.card_univ (α := V), hcard]; omega
        have hcardw : (Finset.univ \ t).card = 1 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ t)]; omega
        have hne : (Finset.univ \ t).Nonempty :=
          Finset.card_pos.1 (show 0 < (Finset.univ \ t).card by omega)
        obtain ⟨w, hw⟩ := hne
        have hwt : w ∉ t := (Finset.mem_sdiff.1 hw).2
        have honly : ∀ u : V, u ∈ Finset.univ \ t → u = w := by
          intro u hu'
          by_contra huu
          have hsub1 : ({u, w} : Finset V) ⊆ Finset.univ \ t := by
            intro z hz
            rcases Finset.mem_insert.1 hz with rfl | hm
            · exact hu'
            · rw [Finset.mem_singleton] at hm; subst hm; exact hw
          have h2 : 2 ≤ (Finset.univ \ t).card := by
            have hcarduw : ({u, w} : Finset V).card = 2 := by
              rw [Finset.card_insert_of_notMem (by
                intro (hm : u ∈ ({w} : Finset V)); rw [Finset.mem_singleton] at hm; exact huu hm),
                Finset.card_singleton]
            have h3card := Finset.card_le_card hsub1
            omega
          omega
        have hmem : ∀ u : V, u ≠ w → u ∈ t := by
          intro u huw
          by_contra hut
          exact huw (honly u (Finset.mem_sdiff.2 ⟨Finset.mem_univ u, hut⟩))
        by_cases hpair : ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ G.Adj w x ∧ G.Adj w y
        · obtain ⟨x, hx, y, hy, hxy, hwx, hwy⟩ := hpair
          have hxyAdj : G.Adj x y := hcl (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hxy
          have hclwxy : G.IsClique ({w, x, y} : Set V) := by
            intro pa hpa pb hpb hpab
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpa hpb
            rcases hpa with rfl | rfl | rfl <;> rcases hpb with rfl | rfl | rfl
            all_goals first
              | exact absurd rfl hpab
              | assumption
              | rw [G.adj_comm] <;> assumption
          have hwxn : w ∉ ({x, y} : Finset V) := by
            intro hm
            rcases Finset.mem_insert.1 hm with rfl | hm'
            · exact hwt hx
            · rw [Finset.mem_singleton] at hm'; subst hm'; exact hwt hy
          have hcardwxy : (insert w {x, y} : Finset V).card = 3 := by
            rw [Finset.card_insert_of_notMem hwxn,
              Finset.card_insert_of_notMem (fun hm => hxy (Finset.mem_singleton.1 hm)),
              Finset.card_singleton]
          have hmemwxy : insert w {x, y} ∈ G.cliqueFinset 3 := by
            refine G.mem_cliqueFinset_iff.2 ⟨?_, hcardwxy⟩
            have hcoe : (↑(insert w ({x, y} : Finset V)) : Set V) = {w, x, y} := by
              simp [Finset.coe_insert, Finset.coe_singleton]
            rw [hcoe]
            exact hclwxy
          have hwmem : w ∈ insert w {x, y} := Finset.mem_insert.2 (Or.inl rfl)
          have hnew : insert w {x, y} ≠ t := by
            intro h; exact hwt (h ▸ hwmem)
          have hsub2 : (insert t {insert w {x, y}}) ⊆ G.cliqueFinset 3 := by
            intro s hs
            rcases Finset.mem_insert.1 hs with rfl | hs'
            · exact ht
            · rw [Finset.mem_singleton] at hs'; subst hs'; exact hmemwxy
          have hcard2 := Finset.card_le_card hsub2
          rw [Finset.card_insert_of_notMem (by
            intro hm; rw [Finset.mem_singleton] at hm; exact hnew hm.symm),
            Finset.card_singleton] at hcard2
          omega
        · exfalso
          have hdw : G.degree w ≤ 1 := by
            by_contra h1
            have h2 : 2 ≤ (G.neighborFinset w).card := by
              rw [G.card_neighborFinset_eq_degree]; omega
            obtain ⟨x, hx⟩ := Finset.card_pos.1 (show 0 < (G.neighborFinset w).card by omega)
            have hcard1 : ((G.neighborFinset w).erase x).card = (G.neighborFinset w).card - 1 :=
              Finset.card_erase_of_mem hx
            obtain ⟨y, hy⟩ := Finset.card_pos.1
              (show 0 < ((G.neighborFinset w).erase x).card by omega)
            have hy0 : y ∈ G.neighborFinset w := Finset.mem_of_mem_erase hy
            have hxy0 : y ≠ x := (Finset.mem_erase.1 hy).1
            have hxw : x ≠ w := ((G.mem_neighborFinset w x).1 hx).ne.symm
            have hyw : y ≠ w := ((G.mem_neighborFinset w y).1 hy0).ne.symm
            exact hpair ⟨x, hmem x hxw, y, hmem y hyw, hxy0.symm,
              (G.mem_neighborFinset w x).1 hx, (G.mem_neighborFinset w y).1 hy0⟩
          have hcover : G.edgeFinset ⊆
              (((G.induce (↑t : Set V)).edgeFinset).image (Sym2.map Subtype.val)) ∪
                G.incidenceFinset w := by
            intro e heedge
            obtain ⟨p, q, rfl⟩ := (Sym2.exists (f := fun z => z = e)).mp ⟨e, rfl⟩
            rcases eq_or_ne p w with hpw | hpw
            · refine Finset.mem_union.2 (Or.inr ?_)
              have hpq : G.Adj p q := G.mem_edgeSet.1 (G.mem_edgeFinset.1 heedge)
              have hmem : s(p, q) ∈ G.incidenceSet w := by
                rw [hpw]
                rw [hpw] at hpq
                exact (G.mem_incidenceSet w q).2 hpq
              exact ((G.mem_incidenceFinset w) _).2 hmem
            · rcases eq_or_ne q w with hqw | hqw
              · refine Finset.mem_union.2 (Or.inr ?_)
                have hpq : G.Adj p q := G.mem_edgeSet.1 (G.mem_edgeFinset.1 heedge)
                have hmem : s(p, q) ∈ G.incidenceSet w := by
                  rw [hqw, show s(p, w) = s(w, p) from by simp]
                  rw [hqw] at hpq
                  exact (G.mem_incidenceSet w p).2 ((G.adj_comm p w).1 hpq)
                exact ((G.mem_incidenceFinset w) _).2 hmem
              · refine Finset.mem_union.2 (Or.inl ?_)
                have hpq : G.Adj p q := G.mem_edgeSet.1 (G.mem_edgeFinset.1 heedge)
                have hpt : p ∈ t := hmem p hpw
                have hqt : q ∈ t := hmem q hqw
                exact Finset.mem_image.2 ⟨s(⟨p, hpt⟩, ⟨q, hqt⟩),
                  (G.induce (↑t : Set V)).mem_edgeFinset.2
                    ((G.induce (↑t : Set V)).mem_edgeSet.2 hpq), rfl⟩
          have hcardt3 : Fintype.card (↥(↑t : Set V)) = 3 := by
            simp [hcardt]
          have hind3 : ((G.induce (↑t : Set V)).edgeFinset).card ≤ 3 := by
            have hle := SimpleGraph.card_edgeFinset_le_card_choose_two
              (G := G.induce (↑t : Set V))
            rw [hcardt3] at hle
            simpa using hle
          have hsplit : G.edgeFinset.card ≤
              (((G.induce (↑t : Set V)).edgeFinset).image (Sym2.map Subtype.val)).card +
                (G.incidenceFinset w).card := by
            have h1 := Finset.card_union_le (s := ((G.induce (↑t : Set V)).edgeFinset).image (Sym2.map Subtype.val)) (t := G.incidenceFinset w)
            have h2 := Finset.card_le_card hcover
            omega
          have hsplit2 : G.edgeFinset.card ≤
              ((G.induce (↑t : Set V)).edgeFinset).card + G.degree w := by
            have himg : (((G.induce (↑t : Set V)).edgeFinset).image
                (Sym2.map (Subtype.val : ↥(↑t : Set V) → V))).card =
                ((G.induce (↑t : Set V)).edgeFinset).card :=
              Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
            rw [G.card_incidenceFinset_eq_degree] at hsplit
            omega
          have hn4e : n = 4 := by omega
          subst hn4e
          omega
      · -- n ≥ 5: strong induction step (odd / even)
        rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
        · -- even n = 2m, m ≥ 3
          have hm3 : 3 ≤ m := by omega
          obtain ⟨H, hHG, hHe⟩ := exists_le_card_edgeFinset_eq (G := G)
            (k := m * m + 1) (by rw [← sq_even_div_four m]; exact he)
          have hshake := H.sum_degrees_eq_twice_card_edges
          rw [hHe] at hshake
          by_cases hex : ∃ v : V, H.degree v ≤ m - 1
          · -- Case A.4.1: some vertex has degree ≤ m − 1
            obtain ⟨v, hv⟩ := hex
            have hpeel := card_edgeFinset_le_induce_compl_add_degree H v
            have hIH := ih (2 * m - 1) (by omega) ↥({v}ᶜ : Set V)
              (H.induce ({v}ᶜ : Set V)) (by omega)
              (by
                have h1 : Fintype.card {x // x = v} = 1 := Fintype.card_unique
                have h2 := Fintype.card_subtype_compl (p := fun x : V => x = v)
                simp only [h1] at h2
                have h3 : Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - 1 := h2
                omega)
              (by
                have h1 : m * m + 1 ≤
                    ((H.induce ({v}ᶜ : Set V)).edgeFinset).card + H.degree v := by
                  rw [← hHe]; exact hpeel
                have h2 : m * m - m + 1 ≤
                    ((H.induce ({v}ᶜ : Set V)).edgeFinset).card := by
                  have hA : m * m + 1 ≤
                      ((H.induce ({v}ᶜ : Set V)).edgeFinset).card + (m - 1) := by
                    calc m * m + 1 ≤
                          ((H.induce ({v}ᶜ : Set V)).edgeFinset).card + H.degree v := h1
                      _ ≤ ((H.induce ({v}ᶜ : Set V)).edgeFinset).card + (m - 1) :=
                          Nat.add_le_add_left hv _
                  have hring : ∀ k : ℕ, (k + 1) * (k + 1) = k * k + 2 * k + 1 := fun k => by ring
                  rcases m with _ | k
                  · omega
                  · have hringk : (k + 1) * (k + 1) = k * k + 2 * k + 1 := hring k
                    omega
                have hed : (2 * m - 1) ^ 2 / 4 + 1 ≤
                    ((H.induce ({v}ᶜ : Set V)).edgeFinset).card := by
                  rw [sq_pred_div_four]; exact h2
                exact hed)
            by_cases hvtri : ∃ t ∈ H.cliqueFinset 3, v ∈ t
            · obtain ⟨t, ht, hvt⟩ := hvtri
              have h2 := card_cliqueFinset_three_induce_compl_add_one_le H ht hvt
              have hTG := card_cliqueFinset_mono hHG
              omega
            · -- A.4.1b: `v` lies in no triangle; Mantel on the peel, delete one edge
              have hW1 : m * m + 1 ≤
                  ((H.induce ({v}ᶜ : Set V)).edgeFinset).card + H.degree v := by
                rw [← hHe]; exact hpeel
              obtain ⟨u, hu⟩ := exists_mem_cliqueFinset_three
                (G := H.induce ({v}ᶜ : Set V))
                (by
                  have h1c : Fintype.card {x // x = v} = 1 := Fintype.card_unique
                  have h2c := Fintype.card_subtype_compl (p := fun x : V => x = v)
                  simp only [h1c] at h2c
                  have h3c : Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - 1 := h2c
                  have hc2 : (Fintype.card ↥({v}ᶜ : Set V)) = 2 * m - 1 := by
                    have h3c' : (Fintype.card ↥({v}ᶜ : Set V)) = Fintype.card V - 1 := h2c
                    omega
                  rw [hc2, sq_pred_div_four]
                  have hring : ∀ k : ℕ, (k + 1) * (k + 1) = k * k + 2 * k + 1 := fun k => by ring
                  rcases m with _ | k
                  · omega
                  · have hringk : (k + 1) * (k + 1) = k * k + 2 * k + 1 := hring k
                    omega)
              obtain ⟨hcl3, hcard3⟩ :=
                (H.induce ({v}ᶜ : Set V)).mem_cliqueFinset_iff.1 hu
              obtain ⟨a, hamem⟩ := Finset.card_pos.1 (show 0 < u.card by omega)
              have h1b : (u.erase a).card = 2 := by
                rw [Finset.card_erase_of_mem hamem]; omega
              obtain ⟨b, hbmem'⟩ := Finset.card_pos.1
                (show 0 < (u.erase a).card by omega)
              have hba : b ≠ a := (Finset.mem_erase.1 hbmem').1
              have hbU : b ∈ u := Finset.mem_of_mem_erase hbmem'
              have huAdj : (H.induce ({v}ᶜ : Set V)).Adj a b :=
                hcl3 (Finset.mem_coe.2 hamem) (Finset.mem_coe.2 hbU) hba.symm
              have he1 : s(a, b) ∈ (H.induce ({v}ᶜ : Set V)).edgeFinset :=
                (H.induce ({v}ᶜ : Set V)).mem_edgeFinset.2
                  ((H.induce ({v}ᶜ : Set V)).mem_edgeSet.2 huAdj)
              have hsub : ∀ x ∈ (s(a, b) : Sym2 ↥({v}ᶜ : Set V)), x ∈ u := by
                intro x hx
                have hxb : x = a ∨ x = b := by simpa using hx
                rcases hxb with rfl | rfl
                · exact hamem
                · exact hbU
              have hdelt := card_cliqueFinset_three_deleteEdges_add_one_le
                (G := H.induce ({v}ᶜ : Set V)) (e := s(a, b)) he1 hu hsub
              have hcardE : (((H.induce ({v}ᶜ : Set V)).deleteEdges
                  ({s(a, b)} : Finset (Sym2 ↥({v}ᶜ : Set V)))).edgeFinset).card + 1
                  = ((H.induce ({v}ᶜ : Set V)).edgeFinset).card :=
                card_edgeFinset_deleteEdges_singleton (G := H.induce ({v}ᶜ : Set V)) (e := s(a, b)) he1
              have hIH2 := ih (2 * m - 1) (by omega) ↥({v}ᶜ : Set V)
                ((H.induce ({v}ᶜ : Set V)).deleteEdges
                  ({s(a, b)} : Finset (Sym2 ↥({v}ᶜ : Set V))))
                (by omega)
                (by
                  have h1c : Fintype.card {x // x = v} = 1 := Fintype.card_unique
                  have h2c := Fintype.card_subtype_compl (p := fun x : V => x = v)
                  simp only [h1c] at h2c
                  have h3c : Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - 1 := h2c
                  omega)
                (by
                  rw [sq_pred_div_four]
                  have hring : ∀ k : ℕ, (k + 1) * (k + 1) = k * k + 2 * k + 1 := fun k => by ring
                  rcases m with _ | k
                  · omega
                  · have hringk : (k + 1) * (k + 1) = k * k + 2 * k + 1 := hring k
                    omega)
              have hfil0 : ((H.cliqueFinset 3).filter (fun s => v ∈ s)) = ∅ :=
                Finset.filter_eq_empty_iff.2 (fun s hs hvs => hvtri ⟨s, hs, hvs⟩)
              have hfil : ((H.cliqueFinset 3).filter (fun s => v ∈ s)).card +
                  ((H.cliqueFinset 3).filter (fun s => v ∉ s)).card =
                  (H.cliqueFinset 3).card := by
                simpa using Finset.card_filter_add_card_filter_not
                  (p := fun s => v ∈ s) (s := H.cliqueFinset 3)
              have hTH' := card_cliqueFinset_three_induce_compl_le H v
              have hTG := card_cliqueFinset_mono hHG
              omega
          · -- A.4.2: every degree ≥ m; pigeonhole a low-degree triangle-vertex
            obtain ⟨t, ht⟩ := exists_mem_cliqueFinset_three (G := H)
              (by rw [hcard, sq_even_div_four m]; omega)
            have hS3 : 3 ≤ ((H.cliqueFinset 3).biUnion id).card :=
              three_le_card_triangleVerts H ht
            have hhigh : ((Finset.univ.filter (fun w => m + 1 ≤ H.degree w)).card ≤ 2) := by
              by_contra hcon
              push_neg at hcon
              set hi : Finset V := Finset.univ.filter (fun w => m + 1 ≤ H.degree w) with hidef
              have hhi3 : 3 ≤ hi.card := by omega
              obtain ⟨x, hx⟩ := Finset.card_pos.1 (show 0 < hi.card by omega)
              have e1 : (hi.erase x).card = hi.card - 1 := Finset.card_erase_of_mem hx
              obtain ⟨y, hy⟩ := Finset.card_pos.1 (show 0 < (hi.erase x).card by omega)
              have e2 : ((hi.erase x).erase y).card = (hi.erase x).card - 1 :=
                Finset.card_erase_of_mem hy
              obtain ⟨z, hz⟩ := Finset.card_pos.1 (show 0 < ((hi.erase x).erase y).card by omega)
              have hyx : y ≠ x := (Finset.mem_erase.1 hy).1
              have hzy : z ≠ y := (Finset.mem_erase.1 hz).1
              have hzx : z ≠ x := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hz)).1
              have hy' : y ∈ hi := Finset.mem_of_mem_erase hy
              have hz' : z ∈ hi := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
              have hdx : (m + 1) ≤ H.degree x :=
                (Finset.mem_filter.1 (show x ∈ Finset.univ.filter
                  (fun w => m + 1 ≤ H.degree w) from hx)).2
              have hdy : (m + 1) ≤ H.degree y :=
                (Finset.mem_filter.1 (show y ∈ Finset.univ.filter
                  (fun w => m + 1 ≤ H.degree w) from hy')).2
              have hdz : (m + 1) ≤ H.degree z :=
                (Finset.mem_filter.1 (show z ∈ Finset.univ.filter
                  (fun w => m + 1 ≤ H.degree w) from hz')).2
              have hcard3z : ({x, y, z} : Finset V).card = 3 := by
                rw [Finset.card_insert_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.1 hm with rfl | hm'
                    · exact hyx rfl
                    · exact hzx (Finset.mem_singleton.1 hm').symm),
                  Finset.card_insert_of_notMem (by
                    intro hm
                    exact hzy (Finset.mem_singleton.1 hm).symm),
                  Finset.card_singleton]
              -- every vertex has degree ≥ m in this branch
              have hallm : ∀ w : V, m ≤ H.degree w := by
                intro w
                by_contra hc
                push_neg at hc
                exact hex ⟨w, by omega⟩
              -- split the total degree sum into {x,y,z} and the rest
              have hpart : ∑ w ∈ ({x, y, z} : Finset V), H.degree w +
                  ∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), H.degree w =
                  ∑ w ∈ (Finset.univ : Finset V), H.degree w := by
                have hdisj : Disjoint ({x, y, z} : Finset V)
                    ((Finset.univ : Finset V) \ {x, y, z}) :=
                  by
                    rw [disjoint_iff_inf_le]
                    simp [Finset.inf_eq_inter]
                have hun : ({x, y, z} : Finset V) ∪
                    ((Finset.univ : Finset V) \ {x, y, z}) = Finset.univ := by
                  ext w
                  by_cases hw : w ∈ ({x, y, z} : Finset V) <;> simp [hw]
                calc ∑ w ∈ ({x, y, z} : Finset V), H.degree w +
                    ∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), H.degree w
                    = ∑ w ∈ (({x, y, z} : Finset V) ∪ ((Finset.univ : Finset V) \ {x, y, z})), H.degree w :=
                      (Finset.sum_union hdisj).symm
                  _ = ∑ w ∈ (Finset.univ : Finset V), H.degree w := by rw [hun]
              have hremsum : 2 * (m * m) ≤
                  (∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), H.degree w) + 3 * m := by
                have h1 : ((Finset.univ : Finset V) \ {x, y, z}).card + 3 = 2 * m := by
                  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
                    Finset.card_univ (α := V), hcard, hcard3z]
                  omega
                have hsc : ∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), m
                    = ((Finset.univ : Finset V) \ {x, y, z}).card * m := by
                  rw [Finset.sum_const, Nat.nsmul_eq_mul]
                have h2 : ((Finset.univ : Finset V) \ {x, y, z}).card * m ≤
                    ∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), H.degree w := by
                  have hs : ∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), m ≤
                      ∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), H.degree w :=
                    Finset.sum_le_sum (fun w hw => hallm w)
                  rw [← hsc]; exact hs
                have h3 : (((Finset.univ : Finset V) \ {x, y, z}).card + 3) * m
                    = 2 * (m * m) := by
                  rw [h1]; ring
                calc 2 * (m * m)
                    = (((Finset.univ : Finset V) \ {x, y, z}).card + 3) * m := h3.symm
                  _ = ((Finset.univ : Finset V) \ {x, y, z}).card * m + 3 * m := by ring
                  _ ≤ (∑ w ∈ ((Finset.univ : Finset V) \ {x, y, z}), H.degree w) + 3 * m :=
                      by omega
              have hsumeq : ∑ w ∈ ({x, y, z} : Finset V), H.degree w =
                  H.degree x + (H.degree y + H.degree z) := by
                rw [Finset.sum_insert (by
                    intro hm
                    rcases Finset.mem_insert.1 hm with rfl | hm'
                    · exact hyx rfl
                    · exact hzx (Finset.mem_singleton.1 hm').symm),
                  Finset.sum_insert (by
                    intro hm
                    exact hzy (Finset.mem_singleton.1 hm).symm),
                  Finset.sum_singleton]
              have hc1 : 2 * (m * m + 1) = 2 * (m * m) + 2 := by ring
              have hring : ∀ k : ℕ, (k + 1) * (k + 1) = k * k + 2 * k + 1 := fun k => by ring
              rcases m with _ | k
              · omega
              · have hringk : (k + 1) * (k + 1) = k * k + 2 * k + 1 := hring k
                omega
            have hnotsub : ¬ ((H.cliqueFinset 3).biUnion id ⊆
                Finset.univ.filter (fun w => m + 1 ≤ H.degree w)) := by
              intro hsub2
              have hcardeq := Finset.card_le_card hsub2
              omega
            obtain ⟨w, hwS, hwnh⟩ := Finset.not_subset.mp hnotsub
            obtain ⟨t', ht'mem, hwt'⟩ := Finset.mem_biUnion.1 hwS
            have hdw : H.degree w ≤ m := by
              by_contra hcon2
              push_neg at hcon2
              exact hwnh (Finset.mem_filter.2 ⟨Finset.mem_univ w, hcon2⟩)
            have hpeel2 := card_edgeFinset_le_induce_compl_add_degree H w
            have hIH3 := ih (2 * m - 1) (by omega) ↥({w}ᶜ : Set V)
              (H.induce ({w}ᶜ : Set V)) (by omega)
              (by
                have h1w : Fintype.card {x // x = w} = 1 := Fintype.card_unique
                have h2w := Fintype.card_subtype_compl (p := fun x : V => x = w)
                simp only [h1w] at h2w
                have h3w : Fintype.card ↥({w}ᶜ : Set V) = Fintype.card V - 1 := h2w
                omega)
              (by
                rw [sq_pred_div_four]
                have hring : ∀ k : ℕ, (k + 1) * (k + 1) = k * k + 2 * k + 1 := fun k => by ring
                rcases m with _ | k
                · omega
                · have hringk : (k + 1) * (k + 1) = k * k + 2 * k + 1 := hring k
                  omega)
            have hplus := card_cliqueFinset_three_induce_compl_add_one_le H ht'mem hwt'
            have hTG := card_cliqueFinset_mono hHG
            omega
        · -- odd n = 2m+1, m ≥ 2
          have hm2 : 2 ≤ m := by omega
          obtain ⟨H, hHG, hHe⟩ := exists_le_card_edgeFinset_eq (G := G)
            (k := m * m + m + 1) (by rw [← sq_odd_div_four m]; exact he)
          have hshake := H.sum_degrees_eq_twice_card_edges
          rw [hHe] at hshake
          have hmin : ∃ v : V, H.degree v ≤ m := by
            by_contra hcon
            push_neg at hcon
            have hlow : (2 * m + 1) * (m + 1) ≤ ∑ v ∈ Finset.univ, H.degree v := by
              calc (2 * m + 1) * (m + 1)
                  = ∑ _ ∈ (Finset.univ : Finset V), (m + 1) := by
                    rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ (α := V), hcard]
                _ ≤ ∑ v ∈ Finset.univ, H.degree v :=
                  Finset.sum_le_sum (fun v _ => hcon v)
            have hc1 : (2 * m + 1) * (m + 1) = 2 * (m * m) + 3 * m + 1 := by ring
            have hc2 : 2 * (m * m + m + 1) = 2 * (m * m) + 2 * m + 2 := by ring
            omega
          obtain ⟨v, hv⟩ := hmin
          have hpeel := card_edgeFinset_le_induce_compl_add_degree H v
          have hcardsub : Fintype.card ↥({v}ᶜ : Set V) = 2 * m := by
            have h1 : Fintype.card {x // x = v} = 1 := Fintype.card_unique
            have h2 := Fintype.card_subtype_compl (p := fun x : V => x = v)
            simp only [h1] at h2
            have h3 : Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - 1 := h2
            omega
          have hIH := ih (2 * m) (by omega) ↥({v}ᶜ : Set V)
            (H.induce ({v}ᶜ : Set V)) (by omega) hcardsub
            (by rw [sq_even_div_four]; omega)
          have hTH := card_cliqueFinset_three_induce_compl_le H v
          have hfil : ((H.cliqueFinset 3).filter (fun s => v ∈ s)).card +
              ((H.cliqueFinset 3).filter (fun s => v ∉ s)).card =
              (H.cliqueFinset 3).card := by
            simpa using Finset.card_filter_add_card_filter_not
              (p := fun s => v ∈ s) (s := H.cliqueFinset 3)
          have hTG := card_cliqueFinset_mono hHG
          omega

/-- **Rademacher's theorem**: a graph on `n ≥ 3` vertices with at least
`⌊n²/4⌋ + 1` edges contains at least `⌊n/2⌋` triangles. -/
theorem rademacher [DecidableRel G.Adj] (h3 : 3 ≤ Fintype.card V)
    (he : Fintype.card V ^ 2 / 4 + 1 ≤ G.edgeFinset.card) :
    Fintype.card V / 2 ≤ (G.cliqueFinset 3).card :=
  rademacher_core (Fintype.card V) V G h3 rfl he

end Rad
