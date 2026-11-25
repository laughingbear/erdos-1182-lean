/-
Copyright 2026 laughingbear. Released under the Apache License, Version 2.0.
-/
import Mathlib

/-!
# Erdős Problem 1182: Chvátal's theorem for triangles

Standalone proofs of `erdos_1182.variants.chvatal` and `erdos_1182.variants.F_ge_pred` from
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1182.lean`).

The definitions `SimpleGraph.graphRamsey` (from
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`), `IsTriangleGood`, `F` and
`le_F` are copied verbatim; the two theorem statements are byte-identical to the originals.

Proof outline:
* `tree_isContained_of_le_degree`: a tree on `k` vertices embeds into any graph with at least `k`
  vertices and minimum degree `≥ k - 1` (remove a leaf, embed the rest, put the leaf at a free
  neighbour of its parent's image).
* `triangle_or_tree`: a triangle-free graph on `2n - 1` vertices either has a vertex of degree
  `≥ n` (its neighbourhood is a clique of the complement) or its complement has minimum degree
  `≥ n - 1`.
* `exists_good_colouring`: for `N ≤ 2n - 2` the complete bipartite graph with parts of size
  `≤ n - 1` is triangle-free and its complement (two cliques) contains no connected graph on `n`
  vertices.
-/

namespace SimpleGraph

/--
The two-color Ramsey number `graphRamsey G H` is the minimum number of vertices `n`
such that every 2-coloring of the edges of the complete graph on `n` vertices contains
a copy of `G` in the first color or a copy of `H` in the second color.

A 2-coloring of the complete graph on `Fin n` is represented by a graph `C` (the edges of the
first color) and its complement `Cᶜ` (the edges of the second color).
-/
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

end SimpleGraph

open SimpleGraph Finset

namespace Erdos1182

/-- A graph `G` on `n` vertices is *$3$-good* (in the sense of [BEFRS80], where a connected graph
is called $m$-good if $R(K_m,G)=(m-1)(n-1)+1$, here with $m=3$) if $R(K_3,G)=2n-1$, where $K_3$ is
`(⊤ : SimpleGraph (Fin 3))`. For connected `G` one always has $R(K_3,G)\ge 2n-1$ (see
`erdos_1182.variants.ramsey_ge`), so this says that the Ramsey number attains its lower bound.

[Er78, p. 33] states the problem for arbitrary graphs $G(n;\ell)$ with $R(K_3,G)\le 2n-1$; for
connected graphs this is the same as `IsTriangleGood`, and we follow [BEFRS80] and the problem
page in restricting to connected graphs. We only apply `IsTriangleGood` to connected graphs, which
have a vertex, so the natural-number subtraction is harmless. -/
def IsTriangleGood {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) G = 2 * n - 1

/-- $F(n)$: the largest $q\le\binom n2$ such that every connected graph on $n$ vertices with at
most $q$ edges is $3$-good (this is $f(n)$ in [BEFRS80]). The set below is downward closed, so
`sSup` is its maximum; for $n\ge3$ it equals one less than the least number of edges of a
connected graph on $n$ vertices that is not $3$-good.

The condition $q\le\binom n2$ is only needed for $n\le2$, where every connected graph is
$3$-good: it gives `F 2 = 1`, as in the table of [BEFRS80], and `F 0 = F 1 = 0`. For $n\ge3$ it is
automatic, because the connected graph $K_n$ is not $3$-good (the complement of the odd cycle
$C_{2n-1}$ shows $R(K_3,K_n)>2n-1$). -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {q : ℕ | q ≤ n.choose 2 ∧
    ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard ≤ q → IsTriangleGood G}

/-- If `q ≤ n.choose 2` and every connected graph on `n` vertices with at most `q` edges is
$3$-good, then `q ≤ F n`. -/
theorem le_F {n q : ℕ} (hq : q ≤ n.choose 2)
    (h : ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard ≤ q → IsTriangleGood G) :
    q ≤ F n := by
  unfold F
  refine le_csSup ⟨n.choose 2, ?_⟩ ⟨hq, h⟩
  rintro p ⟨hp, -⟩
  exact hp

/-- Greedy embedding: a tree on `k` vertices is contained in every graph with at least `k`
vertices and minimum degree at least `k - 1`. -/
theorem tree_isContained_of_le_degree :
    ∀ (k : ℕ) {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V), T.IsTree →
      Fintype.card V = k →
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
        (∀ w, k - 1 ≤ H.degree w) → k ≤ Fintype.card W → T ⊑ H := by
  intro k
  induction k with
  | zero =>
    intro V _ _ T hT hcard
    obtain ⟨v⟩ := hT.connected.nonempty
    have := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  | succ k ih =>
    intro V _ _ T hT hcard W _ _ H _ hdeg hW
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨w⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
      have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      refine ⟨⟨⟨fun _ => w, fun {a b} hab => ?_⟩, fun a b _ => Subsingleton.elim a b⟩⟩
      exact absurd (Subsingleton.elim a b) (T.ne_of_adj hab)
    · have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      classical
      obtain ⟨ℓ, hℓ⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨p, hpℓ, hpuniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hℓ
      have hpne : p ≠ ℓ := (T.ne_of_adj hpℓ).symm
      have hT' : (T.induce ({ℓ}ᶜ : Set V)).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hℓ, hT.isAcyclic.induce _⟩
      have hcard' : Fintype.card ({ℓ}ᶜ : Set V) = k := by
        rw [Fintype.card_compl_set]; simp [hcard]
      obtain ⟨φ⟩ := ih (T.induce ({ℓ}ᶜ : Set V)) hT' hcard' H
        (fun w => by have := hdeg w; omega) (by omega)
      set q : W := φ ⟨p, hpne⟩ with hq
      let img : Finset W := Finset.univ.image fun v => φ v
      have himg : img.card = k := by
        show (Finset.univ.image fun v => φ v).card = k
        rw [Finset.card_image_of_injective (s := Finset.univ) (f := fun v => φ v)
          (fun a b h => φ.injective h), Finset.card_univ, hcard']
      have hfree : ∃ w, H.Adj q w ∧ w ∉ img := by
        by_contra hcon
        push Not at hcon
        have hsub : H.neighborFinset q ⊆ img.erase q := by
          intro w hw
          rw [mem_neighborFinset] at hw
          exact Finset.mem_erase.mpr ⟨(H.ne_of_adj hw).symm, hcon w hw⟩
        have h1 := Finset.card_le_card hsub
        rw [card_neighborFinset_eq_degree,
          Finset.card_erase_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)), himg] at h1
        have := hdeg q
        omega
      obtain ⟨w, hqw, hwimg⟩ := hfree
      let f : V → W := fun v => if h : v = ℓ then w else φ ⟨v, h⟩
      have hf_ne : ∀ v (h : v ≠ ℓ), f v = φ ⟨v, h⟩ := fun v h => by simp [f, h]
      have hf_ℓ : f ℓ = w := by simp [f]
      refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, fun a b hab => ?_⟩⟩
      · by_cases ha : a = ℓ
        · subst ha
          have hb : b = p := hpuniq b hab
          subst hb
          rw [hf_ℓ, hf_ne _ hpne]
          exact hqw.symm
        · by_cases hb : b = ℓ
          · subst hb
            have ha' : a = p := hpuniq a hab.symm
            subst ha'
            rw [hf_ℓ, hf_ne _ hpne]
            exact hqw
          · rw [hf_ne _ ha, hf_ne _ hb]
            exact φ.toHom.map_adj (by simpa [comap_adj] using hab)
      · change f a = f b at hab
        by_cases ha : a = ℓ <;> by_cases hb : b = ℓ
        · rw [ha, hb]
        · subst ha
          rw [hf_ℓ, hf_ne _ hb] at hab
          exact absurd (hab ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)) hwimg
        · subst hb
          rw [hf_ℓ, hf_ne _ ha] at hab
          exact absurd (hab.symm ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)) hwimg
        · rw [hf_ne _ ha, hf_ne _ hb] at hab
          exact congrArg Subtype.val (φ.injective hab)

/-- Upper bound: every graph on `2n - 1` vertices contains a triangle or its complement contains
the tree `T`. -/
theorem triangle_or_tree {n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    (C : SimpleGraph (Fin (2 * n - 1))) : (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ := by
  classical
  obtain ⟨v₀⟩ := hT.connected.nonempty
  have hn : 0 < n := v₀.pos
  by_cases h3 : C.CliqueFree 3
  · right
    by_cases hbig : ∃ v, n ≤ C.degree v
    · obtain ⟨v, hv⟩ := hbig
      obtain ⟨g⟩ : Nonempty (Fin n ↪ C.neighborFinset v) :=
        Function.Embedding.nonempty_of_card_le (by
          rw [Fintype.card_fin, Fintype.card_coe, card_neighborFinset_eq_degree]; exact hv)
      refine ⟨⟨⟨fun i => (g i : Fin (2 * n - 1)), fun {i j} hij => ?_⟩,
        fun i j h => g.injective (Subtype.ext h)⟩⟩
      have hne : i ≠ j := T.ne_of_adj hij
      rw [compl_adj]
      refine ⟨fun h => hne (g.injective (Subtype.ext h)), fun hC => ?_⟩
      apply h3 {v, (g i : Fin (2 * n - 1)), (g j : Fin (2 * n - 1))}
      rw [is3Clique_triple_iff]
      exact ⟨(mem_neighborFinset _ _ _).mp (g i).2, (mem_neighborFinset _ _ _).mp (g j).2, hC⟩
    · push Not at hbig
      refine tree_isContained_of_le_degree n T hT (Fintype.card_fin n) Cᶜ (fun w => ?_) ?_
      · rw [degree_compl, Fintype.card_fin]
        have := hbig w
        omega
      · rw [Fintype.card_fin]; omega
  · left
    exact (not_cliqueFree_iff_top_isContained 3).mp h3

/-- Lower bound: for `N ≤ 2n - 2` the complete bipartite graph with parts of size at most
`n - 1` is triangle-free and its complement contains no connected graph on `n` vertices. -/
theorem exists_good_colouring {n N : ℕ} (T : SimpleGraph (Fin n)) (hT : T.Connected)
    (hN : N ≤ 2 * n - 2) :
    ∃ C : SimpleGraph (Fin N), ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ C ∧ ¬ T ⊑ Cᶜ := by
  classical
  let side : Fin N → Prop := fun i => (i : ℕ) < n - 1
  let C : SimpleGraph (Fin N) :=
    { Adj := fun i j => ¬ (side i ↔ side j)
      symm := ⟨fun i j h h' => h h'.symm⟩
      loopless := ⟨fun i h => h Iff.rfl⟩ }
  have hCadj : ∀ i j, C.Adj i j ↔ ¬ (side i ↔ side j) := fun _ _ => Iff.rfl
  refine ⟨C, ?_, ?_⟩
  · rintro ⟨f⟩
    have h01 := f.toHom.map_adj (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by decide)
    have h12 := f.toHom.map_adj (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by decide)
    have h02 := f.toHom.map_adj (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by decide)
    rw [hCadj] at h01 h12 h02
    tauto
  · rintro ⟨f⟩
    obtain ⟨a⟩ := hT.nonempty
    have hn : 0 < n := a.pos
    have hside : ∀ b, (side (f a) ↔ side (f b)) := by
      intro b
      obtain ⟨w⟩ := hT.preconnected a b
      induction w with
      | nil => exact Iff.rfl
      | cons hadj _ ih =>
        have h := f.toHom.map_adj hadj
        rw [compl_adj, hCadj, not_not] at h
        exact h.2.trans ih
    let S : Finset (Fin N) := Finset.univ.filter fun i => (side i ↔ side (f a))
    have hcardS : n ≤ S.card := by
      have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n))) (t := S)
        (fun b => f b) (fun b _ => by simp [S, (hside b).symm]) (f.injective.injOn)
      simpa using this
    have hS : S.card ≤ n - 1 := by
      by_cases ha : side (f a)
      · have : S.card ≤ (Finset.range (n - 1)).card := by
          apply Finset.card_le_card_of_injOn (fun i : Fin N => (i : ℕ))
          · intro i hi
            simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
            simpa [side] using hi.mpr ha
          · intro i _ j _ h; exact Fin.ext h
        simpa using this
      · have : S.card ≤ (Finset.range (N - (n - 1))).card := by
          apply Finset.card_le_card_of_injOn (fun i : Fin N => (i : ℕ) - (n - 1))
          · intro i hi
            simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
            have h1 : ¬ (i : ℕ) < n - 1 := fun h => ha (hi.mp h)
            have h2 := i.isLt
            simp only [Finset.coe_range, Set.mem_Iio]
            omega
          · intro i hi j hj h
            simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
            have h1 : ¬ (i : ℕ) < n - 1 := fun h => ha (hi.mp h)
            have h2 : ¬ (j : ℕ) < n - 1 := fun h => ha (hj.mp h)
            simp only at h
            exact Fin.ext (by omega)
        simp only [Finset.card_range] at this
        omega
    omega

/-- Chvátal's theorem for triangles: `R(K₃, T) = 2n - 1` for every tree `T` on `n` vertices. -/
theorem graphRamsey_triangle_tree {n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    SimpleGraph.graphRamsey (⊤ : SimpleGraph (Fin 3)) T = 2 * n - 1 := by
  unfold SimpleGraph.graphRamsey
  have hmem : 2 * n - 1 ∈ { N : ℕ | ∀ (C : SimpleGraph (Fin N)),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ T.IsContained Cᶜ } :=
    fun C => triangle_or_tree T hT C
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  intro N hN
  by_contra hlt
  obtain ⟨C, h1, h2⟩ := exists_good_colouring T hT.connected (show N ≤ 2 * n - 2 by omega)
  rcases hN C with h | h
  exacts [h1 h, h2 h]

theorem erdos_1182.variants.chvatal {n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    IsTriangleGood T :=
  graphRamsey_triangle_tree T hT

theorem erdos_1182.variants.F_ge_pred {n : ℕ} (hn : 2 ≤ n) : n - 1 ≤ F n := by
  apply le_F
  · rw [Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]
  · intro G hG hE
    apply erdos_1182.variants.chvatal G
    rw [isTree_iff_connected_and_card]
    refine ⟨hG, ?_⟩
    have h1 := hG.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_coe_set_eq] at h1 ⊢
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1 ⊢
    omega

end Erdos1182
