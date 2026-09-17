/-!
# JSP-000839 (scoped component, k = 2) — two edge-disjoint triangles

Every simple graph on `n ≥ 5` vertices with `⌊n²/4⌋ + 2` edges contains two
edge-disjoint triangles.

This is the `k = 2` case of Erdős problem #1009 (JSP-000839: "just above the
maximum bipartite edge count, how many edge-disjoint triangles are
guaranteed?"). The general result is due to E. Győri (1988); the elementary
bound that `k < n/2` edge-disjoint triangles are guaranteed at
`⌊n²/4⌋ + k + 1`... (scoped: we formalize only `k = 2`).

The proof reuses the graph/counting infrastructure developed for JSP-000840
(Rademacher's theorem, `rademacher_list`): a family of pairwise edge-sharing
triangles either shares one common edge or is contained in a `K₄`; both cases
force `e ≤ ⌊n²/4⌋ + 1`, contradicting the hypothesis.

Self-contained formalization in **Lean 4 core** (no Mathlib, no imports).
-/

namespace Jsp000839

/-! ## Weighted sums over lists -/

/-- Sum of `f` over a list. -/
def ssum (l : List α) (f : α → Nat) : Nat := (l.map f).sum

theorem ssum_nil (f : α → Nat) : ssum [] f = 0 := rfl

theorem ssum_cons (a : α) (l : List α) (f : α → Nat) :
    ssum (a :: l) f = f a + ssum l f := by simp [ssum]

theorem ssum_congr {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x = g x) :
    ssum l f = ssum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, ssum_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem ssum_add (l : List α) (f g : α → Nat) :
    ssum l (fun x => f x + g x) = ssum l f + ssum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [ssum_cons, ssum_cons, ssum_cons, ih]; omega

theorem ssum_const (l : List α) (c : Nat) :
    ssum l (fun _ => c) = c * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, ih, List.length_cons, Nat.mul_succ]; omega

theorem ssum_le {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    ssum l f ≤ ssum l g := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [ssum_cons, ssum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem ssum_ge {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≥ g x) :
    ssum l f ≥ ssum l g := ssum_le h

theorem ssum_swap (A : List α) (B : List β) (f : α → β → Nat) :
    ssum A (fun i => ssum B (f i)) = ssum B (fun j => ssum A (fun i => f i j)) := by
  induction A with
  | nil =>
    have hz : ssum B (fun j => ssum [] (fun i => f i j)) = 0 := by
      calc ssum B (fun j => ssum [] (fun i => f i j))
          = ssum B (fun _ => 0) := ssum_congr (fun j _ => rfl)
        _ = 0 * B.length := ssum_const B 0
        _ = 0 := Nat.zero_mul _
    rw [ssum_nil]; exact hz.symm
  | cons a A ih =>
    rw [ssum_cons]
    have step : ∀ j ∈ B, ssum (a :: A) (fun i => f i j) =
        f a j + ssum A (fun i => f i j) := fun j _ => ssum_cons a A _
    calc ssum B (f a) + ssum A (fun i => ssum B (f i))
        = ssum B (f a) + ssum B (fun j => ssum A (fun i => f i j)) := by rw [ih]
      _ = ssum B (fun j => f a j + ssum A (fun i => f i j)) := (ssum_add B (f a) _).symm
      _ = ssum B (fun j => ssum (a :: A) (fun i => f i j)) := (ssum_congr step).symm

theorem ssum_eq_zero {l : List α} {f : α → Nat} (h : ∀ x ∈ l, f x = 0) :
    ssum l f = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), Nat.add_zero]

/-- If `f ≤ g` pointwise on `l` and the gap at `y ∈ l` is at least 1,
the total gap is at least 1. -/
theorem ssum_add_one_le {l : List α} {f g : α → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) (y : α) (hy : y ∈ l) (hy1 : f y + 1 ≤ g y) :
    ssum l f + 1 ≤ ssum l g := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    rw [List.mem_cons] at hy
    cases hy with
    | inl hya =>
      subst hya
      have h1 : ssum l f ≤ ssum l g :=
        ssum_le (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have h2 := Nat.add_le_add hy1 h1
      rw [ssum_cons, ssum_cons]
      omega
    | inr hyl =>
      have h2 : ssum l f + 1 ≤ ssum l g :=
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hyl
      have h3 : f a ≤ g a := h a (List.mem_cons_self ..)
      rw [ssum_cons, ssum_cons]
      omega

/-- A positive total has a positive term. -/
theorem ssum_pos_of_pos {l : List α} {f : α → Nat} (h : 1 ≤ ssum l f) :
    ∃ x ∈ l, 1 ≤ f x := by
  induction l with
  | nil => rw [ssum_nil] at h; omega
  | cons a l ih =>
    rw [ssum_cons] at h
    by_cases ha : 1 ≤ f a
    · exact ⟨a, List.mem_cons_self .., ha⟩
    · have h0 : f a = 0 := by omega
      have h1 : 1 ≤ ssum l f := by omega
      cases ih h1 with
      | intro x hx => exact ⟨x, List.mem_cons_of_mem _ hx.1, hx.2⟩

/-- If every term vanishes off the `p`-filter, the sum equals the filtered sum. -/
theorem ssum_filter_of_vanish (p : α → Bool) (l : List α) (f : α → Nat)
    (h : ∀ x ∈ l, p x = false → f x = 0) :
    ssum l f = ssum (l.filter p) f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons]
    cases hp : p a with
    | true =>
      have hrw : (a :: l).filter p = a :: l.filter p := by simp [List.filter, hp]
      rw [hrw, ssum_cons, ih (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)]
    | false =>
      have hrw : (a :: l).filter p = l.filter p := by simp [List.filter, hp]
      rw [hrw, h a (List.mem_cons_self ..) hp, Nat.zero_add]
      exact ih (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)

/-- Sums split along a Boolean predicate. -/
theorem ssum_filter_add (p : α → Bool) (l : List α) (f : α → Nat) :
    ssum l f = ssum (l.filter p) f + ssum (l.filter (fun x => !p x)) f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons]
    cases hp : p a with
    | true =>
      have hrw1 : (a :: l).filter p = a :: l.filter p := by simp [List.filter, hp]
      have hrw2 : (a :: l).filter (fun x => !p x) = l.filter (fun x => !p x) := by
        simp [List.filter, hp]
      rw [hrw1, hrw2, ssum_cons, ih]; omega
    | false =>
      have hrw1 : (a :: l).filter p = l.filter p := by simp [List.filter, hp]
      have hrw2 : (a :: l).filter (fun x => !p x) = a :: l.filter (fun x => !p x) := by
        simp [List.filter, hp]
      rw [hrw1, hrw2, ssum_cons, ih]; omega

/-- In a duplicate-free list, "sum of `g` at the position of `y`" is `g y`. -/
theorem ssum_eq_single [DecidableEq α] {l : List α} (nd : l.Nodup) {y : α}
    (hy : y ∈ l) (g : α → Nat) :
    ssum l (fun i => if i = y then g i else 0) = g y := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    rw [List.nodup_cons] at nd
    rw [List.mem_cons] at hy
    rw [ssum_cons]
    cases hy with
    | inl hay =>
      -- hay : y = a
      have h0 : ssum l (fun i => if i = y then g i else 0) = 0 := by
        apply ssum_eq_zero
        intro x hx
        have hne : x ≠ y := by
          intro hxy
          exact nd.1 (hay ▸ hxy ▸ hx)
        simp [hne]
      have h1 : (if a = y then g a else 0) = g y := by rw [hay]; simp
      rw [h1, h0, Nat.add_zero]
    | inr hyl =>
      have hne : ¬ a = y := fun hay => nd.1 (hay ▸ hyl)
      simp [hne]
      exact ih nd.2 hyl

/-- Length of a filter as a weighted sum. -/
theorem filter_length_eq (p : α → Bool) (l : List α) :
    (l.filter p).length = ssum l (fun x => (p x).toNat) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a <;> simp [List.filter, hp, ssum_cons] <;> omega

/-- Filter lengths of a predicate and its negation add up to the list length. -/
theorem filter_length_add (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a <;> simp [List.filter, hp, List.length_cons] <;> omega

/-- In a duplicate-free list containing `y`, exactly one element equals `y`. -/
theorem filter_eq_single_length [DecidableEq α] {l : List α} (nd : l.Nodup)
    {y : α} (hy : y ∈ l) :
    (l.filter (fun x => x == y)).length = 1 := by
  rw [filter_length_eq]
  have hc : (fun i => ((i == y) : Bool).toNat) = (fun i => if i = y then (1 : Nat) else 0) := by
    funext i
    by_cases hiy : i = y <;> simp [hiy]
  rw [hc]
  exact ssum_eq_single nd hy _

/-- Removing one element of a duplicate-free list drops the length by one. -/
theorem length_filter_neq_of_mem [DecidableEq α] {l : List α} (nd : l.Nodup)
    {y : α} (hy : y ∈ l) :
    (l.filter (fun x => !(x == y))).length = l.length - 1 := by
  have h1 := filter_length_add (fun x => x == y) l
  have h2 := filter_eq_single_length nd hy
  have h3 : 1 ≤ l.length := by
    cases l with
    | nil => simp at hy
    | cons a l => simp
  omega

/-! ## More list-sum tools -/

theorem ssum_filter_le (p : α → Bool) (l : List α) (f : α → Nat) :
    ssum (l.filter p) f ≤ ssum l f := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [ssum_cons]
    cases hp : p a with
    | true =>
      have hrw : (a :: l).filter p = a :: l.filter p := by simp [List.filter, hp]
      rw [hrw, ssum_cons]
      exact Nat.add_le_add (Nat.le_refl _) ih
    | false =>
      have hrw : (a :: l).filter p = l.filter p := by simp [List.filter, hp]
      rw [hrw]
      exact Nat.le_add_left_of_le ih

theorem one_le_ssum_of_mem {l : List α} {f : α → Nat} {x : α} (hx : x ∈ l)
    (h : 1 ≤ f x) : 1 ≤ ssum l f := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.mem_cons] at hx
    rw [ssum_cons]
    cases hx with
    | inl hxa => rw [← hxa]; omega
    | inr hxl => have := ih hxl; omega

/-- Sum over the `== y` filter picks out `f y` (duplicate-free list). -/
theorem ssum_filter_eq_single [DecidableEq α] {l : List α} (nd : l.Nodup)
    {y : α} (hy : y ∈ l) (f : α → Nat) :
    ssum (l.filter (fun x => x == y)) f = f y := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    rw [List.nodup_cons] at nd
    rw [List.mem_cons] at hy
    cases hy with
    | inl hay =>
      -- hay : y = a
      have h1 : (a == y) = true := by rw [← hay]; simp
      have h2 : l.filter (fun x => x == y) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have hne : x ≠ y := fun hxy => nd.1 (hay ▸ hxy ▸ hx)
        have h3 : (x == y) = false := by simp [hne]
        simp [h3]
      have hfilter : (a :: l).filter (fun x => x == y) = [a] := by
        simp [List.filter, h1, h2]
      rw [hfilter, ssum_cons, ssum_nil, Nat.add_zero, hay]
    | inr hyl =>
      have hne : (a == y) = false := by
        simp
        intro hay
        exact nd.1 (hay ▸ hyl)
      have hfilter : (a :: l).filter (fun x => x == y) = l.filter (fun x => x == y) := by
        simp [List.filter, hne]
      rw [hfilter]
      exact ih nd.2 hyl

theorem Bool.toNat_le_one : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide

/-! ## Graphs on `Fin n`, counts relative to a vertex list -/

/-- A simple graph on `Fin n` as a Boolean adjacency matrix. -/
structure Gph (n : Nat) where
  adj : Fin n → Fin n → Bool
  sym : ∀ i j, adj i j = adj j i
  irr : ∀ i, adj i i = false

/-- Degree of `v` within the vertex list `l`. -/
def degIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) (v : Fin n) : Nat :=
  ssum l fun j => (A v j).toNat

/-- Number of edges with both endpoints in `l` (each unordered pair counted once). -/
def ecountIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) : Nat :=
  ssum l fun i => ssum l fun j => if (i : Nat) < (j : Nat) then (A i j).toNat else 0

/-- Indicator term for an ordered triple forming a triangle. -/
def triTerm (A : Fin n → Fin n → Bool) (i j k : Fin n) : Nat :=
  if (i : Nat) < (j : Nat) ∧ (j : Nat) < (k : Nat) then (A i j && A j k && A i k).toNat else 0

/-- Number of triangles inside `l` (each unordered triple counted once). -/
def tcountIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) : Nat :=
  ssum l fun i => ssum l fun j => ssum l fun k => triTerm A i j k

/-- Common-neighbor count of `x` and `y` within `l`. -/
def commonIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) (x y : Fin n) : Nat :=
  ssum l fun j => (A x j && A y j).toNat

/-- Handshake lemma: the degrees in `l` sum to twice the edge count. -/
theorem handshake (G : Gph n) (l : List (Fin n)) :
    ssum l (fun v => degIn G.adj l v) = 2 * ecountIn G.adj l := by
  have pw : ∀ v ∈ l, ∀ j ∈ l, (G.adj v j).toNat =
      (if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0) +
      (if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0) := by
    intro v _ j _
    by_cases h1 : (v : Nat) < (j : Nat)
    · have h2 : ¬ (j : Nat) < (v : Nat) := by omega
      simp [h1, h2]
    · by_cases h2 : (j : Nat) < (v : Nat)
      · simp [h1, h2]
      · have h3 : v = j := Fin.ext (by omega)
        rw [h3]
        simp [G.irr]
  calc ssum l (fun v => degIn G.adj l v)
      = ssum l (fun v => ssum l (fun j =>
          (if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0) +
          (if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0))) :=
        ssum_congr fun v hv => ssum_congr fun j hj => pw v hv j hj
    _ = ssum l (fun v => ssum l (fun j => if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0) +
            ssum l (fun j => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) :=
        ssum_congr fun v _ => ssum_add _ _ _
    _ = ssum l (fun v => ssum l (fun j => if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0)) +
        ssum l (fun v => ssum l (fun j => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) :=
        ssum_add _ _ _
    _ = ecountIn G.adj l +
        ssum l (fun j => ssum l (fun v => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) := by
        have hs := ssum_swap l l (fun v j => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)
        show ecountIn G.adj l + ssum l (fun v => ssum l (fun j =>
              if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) = _
        rw [hs]
    _ = 2 * ecountIn G.adj l := by
        have h : ∀ j ∈ l, ∀ v ∈ l,
            (if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0) =
            (if (j : Nat) < (v : Nat) then (G.adj j v).toNat else 0) :=
          fun j _ v _ => by rw [G.sym j v]
        rw [ssum_congr fun j hj => ssum_congr fun v hv => h j hj v hv]
        show ecountIn G.adj l + ecountIn G.adj l = 2 * ecountIn G.adj l
        omega

/-- Pigeonhole: `deg x + deg y ≤ |l| + |common neighbors|`. -/
theorem deg_add_le (G : Gph n) (l : List (Fin n)) (x y : Fin n) :
    degIn G.adj l x + degIn G.adj l y ≤ l.length + commonIn G.adj l x y := by
  have pw : ∀ j ∈ l, (G.adj x j).toNat + (G.adj y j).toNat ≤
      1 + (G.adj x j && G.adj y j).toNat := by
    intro j _
    generalize G.adj x j = b1
    generalize G.adj y j = b2
    cases b1 <;> cases b2 <;> decide
  calc degIn G.adj l x + degIn G.adj l y
      = ssum l (fun j => (G.adj x j).toNat + (G.adj y j).toNat) := (ssum_add _ _ _).symm
    _ ≤ ssum l (fun j => 1 + (G.adj x j && G.adj y j).toNat) := ssum_le pw
    _ = ssum l (fun _ => 1) + commonIn G.adj l x y := ssum_add _ _ _
    _ = l.length + commonIn G.adj l x y := by rw [ssum_const, Nat.one_mul]

/-! ## Boolean helpers -/

theorem bool_true_of_toNat_pos {a : Bool} (h : 1 ≤ a.toNat) : a = true := by
  cases a <;> simp at h ⊢

theorem bool_and_true_of_toNat_pos {a b : Bool} (h : 1 ≤ (a && b).toNat) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp at h ⊢

/-! ## Vertex removal and degree/edge counts -/

/-- Degrees split off a vertex `y`. -/
theorem degIn_filter_add (G : Gph n) {l : List (Fin n)} (nd : l.Nodup) {y : Fin n}
    (hy : y ∈ l) (x : Fin n) :
    degIn G.adj l x = (G.adj x y).toNat + degIn G.adj (l.filter fun v => !(v == y)) x := by
  have h := ssum_filter_add (fun v => v == y) l (fun j => (G.adj x j).toNat)
  rw [ssum_filter_eq_single nd hy] at h
  exact h

/-- The vertex list with `y` removed. -/
def delVertex (l : List (Fin n)) (y : Fin n) : List (Fin n) := l.filter fun v => !(v == y)

/-- Edge count splits off a vertex `y` (nodup list, `y ∈ l`). -/
theorem ecountIn_eq_filter_add_deg (G : Gph n) {l : List (Fin n)} (nd : l.Nodup)
    {y : Fin n} (hy : y ∈ l) :
    ecountIn G.adj l =
      degIn G.adj l y + ecountIn G.adj (delVertex l y) := by
  have memL' : ∀ x ∈ delVertex l y, x ≠ y := by
    intro x hx
    have h := (List.mem_filter.mp hx).2
    intro hxy
    rw [hxy] at h
    simp at h
  -- Per-vertex inner sum splits at `j = y`.
  have hInner : ∀ i ∈ l, ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) =
      (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0) +
      ssum (delVertex l y) (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) := by
    intro i _
    have h := ssum_filter_add (fun v => v == y) l
      (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)
    rw [ssum_filter_eq_single nd hy] at h
    exact h
  -- Sum over `i`: split at `i = y`.
  have hOuter : ecountIn G.adj l =
      ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) +
      ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by
    have h := ssum_filter_add (fun v => !(v == y)) l
      (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0))
    have hs : ssum (l.filter fun v => !(!(v == y)))
        (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
        ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by
      have hsingle := ssum_filter_eq_single nd hy
        (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0))
      have hcongr : ssum (l.filter fun v => !(!(v == y)))
          (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
          ssum (l.filter fun v => v == y)
          (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) := by
        have hfilter : (l.filter fun v => !(!(v == y))) = l.filter fun v => v == y := by
          induction l with
          | nil => rfl
          | cons a l ih =>
            cases hpa : (a == y) <;> simp [List.filter, hpa] <;> exact ih
        rw [hfilter]
      rw [hcongr]
      exact hsingle
    rw [hs] at h
    exact h
  -- Combine: inner sums over `i ∈ delVertex l y`.
  have hMid : ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
      ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0)) +
      ecountIn G.adj (delVertex l y) := by
    have h1 : ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
        ssum (delVertex l y) (fun i => ((if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0) +
          ssum (delVertex l y) (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0))) :=
      ssum_congr fun i hi => hInner i ((List.mem_filter.mp hi).1)
    rw [h1, ssum_add]
    rfl
  have hRow : ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) =
      ssum (delVertex l y) (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by
    have h := ssum_filter_add (fun v => !(v == y)) l
      (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0)
    have hz : ssum (l.filter fun v => !(!(v == y)))
        (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) = 0 := by
      apply ssum_eq_zero
      intro x hx
      have hx2 := (List.mem_filter.mp hx).2
      have hxy : x = y := by
        simp only [Bool.not_not] at hx2
        exact beq_iff_eq.mp hx2
      rw [hxy]
      simp
    rw [hz, Nat.add_zero] at h
    exact h
  have h2 : ∀ j ∈ delVertex l y, (G.adj y j).toNat =
      (if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
      (if (j : Nat) < (y : Nat) then (G.adj y j).toNat else 0) := by
    intro j hj
    have hjy : j ≠ y := memL' j hj
    by_cases h1 : (y : Nat) < (j : Nat)
    · have h2 : ¬ (j : Nat) < (y : Nat) := by omega
      simp [h1, h2]
    · have h2 : (j : Nat) < (y : Nat) := by
        have hne : (j : Nat) ≠ (y : Nat) := fun heq => hjy (Fin.ext heq)
        omega
      simp [h1, h2]
  have hDeg : ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
        ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0)) =
      degIn G.adj l y := by
    calc ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
          ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0))
        = ssum (delVertex l y) (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
          ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0)) := by
          rw [hRow]
      _ = ssum (delVertex l y) (fun j => (if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
            (if (j : Nat) < (y : Nat) then (G.adj y j).toNat else 0)) := (ssum_add _ _ _).symm
      _ = ssum (delVertex l y) (fun j => (G.adj y j).toNat) :=
          ssum_congr fun j hj => (h2 j hj).symm
      _ = degIn G.adj l y := by
          have h4 : degIn G.adj l y = (G.adj y y).toNat + degIn G.adj (delVertex l y) y :=
            degIn_filter_add G nd hy y
          rw [G.irr y] at h4
          simp at h4
          exact h4.symm
  -- Assemble.
  calc ecountIn G.adj l
      = ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) +
        ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := hOuter
    _ = (ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0)) +
          ecountIn G.adj (delVertex l y)) +
        ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by rw [hMid]
    _ = degIn G.adj l y + ecountIn G.adj (delVertex l y) := by
        have h5 : ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0)) =
            ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0)) :=
          ssum_congr fun i _ => by rw [G.sym i y]
        rw [h5]
        omega

/-- The second triangle of infrastructure: edge existence from a positive count. -/
theorem exists_edge_of_pos (G : Gph n) {l : List (Fin n)} (h : 1 ≤ ecountIn G.adj l) :
    ∃ i ∈ l, ∃ j ∈ l, (i : Nat) < (j : Nat) ∧ G.adj i j = true := by
  obtain ⟨i, hi, hpi⟩ := ssum_pos_of_pos h
  obtain ⟨j, hj, hpj⟩ := ssum_pos_of_pos hpi
  have hij : (i : Nat) < (j : Nat) := by
    by_cases hc : (i : Nat) < (j : Nat)
    · exact hc
    · simp [hc] at hpj
  have hA : G.adj i j = true := by
    have h1 : (if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) = (G.adj i j).toNat := by
      simp [hij]
    rw [h1] at hpj
    exact bool_true_of_toNat_pos hpj
  exact ⟨i, hi, j, hj, hij, hA⟩

/-- Edge count is tiny on lists of length at most 2. -/
theorem ecountIn_le_of_length_le_two (A : Fin n → Fin n → Bool) {l : List (Fin n)}
    (h : l.length ≤ 2) : ecountIn A l ≤ l.length - 1 := by
  cases l with
  | nil => simp [ecountIn, ssum]
  | cons a l =>
    cases l with
    | nil =>
      have hz : ecountIn A [a] = 0 := by
        simp [ecountIn, ssum_cons, ssum_nil]
      simp [hz]
    | cons b l =>
      cases l with
      | nil =>
        have hexp : ecountIn A [a, b] =
            (if (a : Nat) < (b : Nat) then (A a b).toNat else 0) +
            (if (b : Nat) < (a : Nat) then (A b a).toNat else 0) := by
          simp [ecountIn, ssum_cons, ssum_nil]
        rw [hexp]
        by_cases h1 : (a : Nat) < (b : Nat)
        · have h2 : ¬ (b : Nat) < (a : Nat) := by omega
          simp [h1, h2]
          exact Bool.toNat_le_one _
        · by_cases h2 : (b : Nat) < (a : Nat)
          · simp [h1, h2]
            exact Bool.toNat_le_one _
          · simp [h1, h2]
      | cons c l => simp at h

/-! ## Mantel's theorem -/

/-- Mantel's theorem (list form): more than `⌊m²/4⌋` edges force a triangle. -/
theorem mantel (G : Gph n) : ∀ m : Nat, ∀ l : List (Fin n), l.Nodup → l.length = m →
    m * m / 4 + 1 ≤ ecountIn G.adj l →
    ∃ x ∈ l, ∃ y ∈ l, ∃ z ∈ l, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      G.adj x y = true ∧ G.adj x z = true ∧ G.adj y z = true := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro l nd hm he
    by_cases hm2 : m ≤ 2
    · have hb : ecountIn G.adj l ≤ l.length - 1 := ecountIn_le_of_length_le_two G.adj (by omega)
      rw [hm] at hb
      have h2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      obtain h0 | h1 | h2 := h2
      · subst h0; omega
      · subst h1; omega
      · subst h2; omega
    · have hm3 : 3 ≤ m := by omega
      have hpos : 1 ≤ ecountIn G.adj l := by omega
      obtain ⟨x, hx, y, hy, hxy, hAxy⟩ := exists_edge_of_pos G hpos
      have hxy' : x ≠ y := by intro h; rw [h] at hxy; omega
      by_cases hdeg : degIn G.adj l x + degIn G.adj l y ≤ m
      · -- Delete both endpoints; the rest still has enough edges.
        have nd₁ : (l.filter fun v => !(v == y)).Nodup := nd.filter _
        have hx₁ : x ∈ l.filter (fun v => !(v == y)) := by
          have h : (!(x == y)) = true := by simp [hxy']
          exact List.mem_filter.mpr ⟨hx, h⟩
        have hE1 := ecountIn_eq_filter_add_deg G nd hy
        have hE2 := ecountIn_eq_filter_add_deg G nd₁ hx₁
        simp only [delVertex] at hE1 hE2
        have hd : degIn G.adj (l.filter fun v => !(v == y)) x + 1 = degIn G.adj l x := by
          have h := degIn_filter_add G nd hy x
          rw [hAxy] at h
          simp at h
          omega
        have nd₂ : ((l.filter fun v => !(v == y)).filter fun v => !(v == x)).Nodup := nd₁.filter _
        have hlen2 : ((l.filter fun v => !(v == y)).filter fun v => !(v == x)).length = m - 2 := by
          have h1 : (l.filter fun v => !(v == y)).length = m - 1 := by
            have h := length_filter_neq_of_mem nd hy
            rwa [hm] at h
          have h2 := length_filter_neq_of_mem nd₁ hx₁
          rw [h1] at h2
          exact h2
        have hE : (m - 2) * (m - 2) / 4 + 1 ≤
            ecountIn G.adj ((l.filter fun v => !(v == y)).filter fun v => !(v == x)) := by
          obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
          have hk2 : m - 2 = k := by omega
          have hexp : (k + 2) * (k + 2) = k * k + 4 * k + 4 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
          rw [hk] at he hdeg
          rw [hexp] at he
          rw [hk2]
          omega
        obtain ⟨x', hx', y', hy', z', hz', h1', h2', h3', h4', h5', h6'⟩ :=
          ih (m - 2) (by omega) _ nd₂ hlen2 hE
        exact ⟨x', (List.mem_filter.mp (List.mem_filter.mp hx').1).1,
               y', (List.mem_filter.mp (List.mem_filter.mp hy').1).1,
               z', (List.mem_filter.mp (List.mem_filter.mp hz').1).1,
               h1', h2', h3', h4', h5', h6'⟩
      · -- High degree sum: a common neighbor exists.
        have hcom := deg_add_le G l x y
        rw [hm] at hcom
        have hcm : 1 ≤ commonIn G.adj l x y := by omega
        obtain ⟨z, hz, hz1⟩ := ssum_pos_of_pos hcm
        obtain ⟨hxz, hyz⟩ := bool_and_true_of_toNat_pos hz1
        have hzx : z ≠ x := by
          intro h; rw [h, G.irr] at hxz; simp at hxz
        have hzy : z ≠ y := by
          intro h; rw [h, G.irr] at hyz; simp at hyz
        exact ⟨x, hx, y, hy, z, hz, hxy', hzx.symm, hzy.symm, hAxy, hxz, hyz⟩

/-! ## Edge deletion -/

/-- The graph with edge `{u,v}` removed. -/
def deleteEdge (G : Gph n) (u v : Fin n) : Gph n where
  adj := fun i j => if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then false else G.adj i j
  sym := by
    intro i j
    have hswap : ∀ a b : Fin n, ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) →
        ((b = u ∧ a = v) ∨ (b = v ∧ a = u)) := by
      intro a b h
      cases h with
      | inl h1 => exact Or.inr ⟨h1.2, h1.1⟩
      | inr h1 => exact Or.inl ⟨h1.2, h1.1⟩
    show (if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then false else G.adj i j) =
         (if (j = u ∧ i = v) ∨ (j = v ∧ i = u) then false else G.adj j i)
    by_cases h : (i = u ∧ j = v) ∨ (i = v ∧ j = u)
    · have h' := hswap i j h
      simp [h, h']
    · by_cases h' : (j = u ∧ i = v) ∨ (j = v ∧ i = u)
      · exact absurd (hswap j i h') h
      · simp [h, h', G.sym i j]
  irr := by
    intro i
    show (if (i = u ∧ i = v) ∨ (i = v ∧ i = u) then false else G.adj i i) = false
    by_cases h : (i = u ∧ i = v) ∨ (i = v ∧ i = u)
    · simp [h]
    · simp [h, G.irr i]

theorem deleteEdge_adj_eq (G : Gph n) (u v i j : Fin n) :
    (deleteEdge G u v).adj i j =
      (if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then false else G.adj i j) := rfl

theorem deleteEdge_adj_true {G : Gph n} {u v a b : Fin n}
    (h : (deleteEdge G u v).adj a b = true) : G.adj a b = true := by
  rw [deleteEdge_adj_eq] at h
  by_cases hc : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
  · simp [hc] at h
  · simp [hc] at h
    exact h

/-- Triangle count is monotone under edge deletion. -/
theorem tcountIn_deleteEdge_le (G : Gph n) (u v : Fin n) (l : List (Fin n)) :
    tcountIn (deleteEdge G u v).adj l ≤ tcountIn G.adj l := by
  apply ssum_le; intro i _
  apply ssum_le; intro j _
  apply ssum_le; intro k _
  simp only [triTerm]
  by_cases hc : (i : Nat) < (j : Nat) ∧ (j : Nat) < (k : Nat)
  · simp [hc]
    by_cases h1 : (deleteEdge G u v).adj i j = true
    · have h1' : G.adj i j = true := deleteEdge_adj_true h1
      by_cases h2 : (deleteEdge G u v).adj j k = true
      · have h2' : G.adj j k = true := deleteEdge_adj_true h2
        by_cases h3 : (deleteEdge G u v).adj i k = true
        · have h3' : G.adj i k = true := deleteEdge_adj_true h3
          simp [h1, h1', h2, h2', h3, h3']
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [hc]

/-- Deleting an existing edge drops the edge count by exactly one. -/
theorem ecountIn_deleteEdge (G : Gph n) {l : List (Fin n)} (nd : l.Nodup)
    {u v : Fin n} (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) (hA : G.adj u v = true) :
    ecountIn (deleteEdge G u v).adj l + 1 = ecountIn G.adj l := by
  have hAvu : G.adj v u = true := by
    rw [G.sym v u]; exact hA
  have pw : ∀ i ∈ l, ∀ j ∈ l,
      (if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) =
      (if (i : Nat) < (j : Nat) then ((deleteEdge G u v).adj i j).toNat else 0) +
      (if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then 1 else 0) := by
    intro i _ j _
    by_cases hp : (i = u ∧ j = v) ∨ (i = v ∧ j = u)
    · have hAij : G.adj i j = true := by
        cases hp with
        | inl h1 => rw [h1.1, h1.2]; exact hA
        | inr h1 => rw [h1.1, h1.2]; exact hAvu
      have hD : (deleteEdge G u v).adj i j = false := by
        rw [deleteEdge_adj_eq]; simp [hp]
      by_cases hij : (i : Nat) < (j : Nat)
      · simp [hij, hAij, hD, hp]
      · simp [hij, hp]
    · have hD : (deleteEdge G u v).adj i j = G.adj i j := by
        rw [deleteEdge_adj_eq]; simp [hp]
      by_cases hij : (i : Nat) < (j : Nat)
      · simp [hij, hD, hp]
      · simp [hij, hp]
  -- The correction term totals exactly 1.
  have hΔ : ssum l (fun i => ssum l (fun j =>
        if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) = 1 := by
    have hsplit : ∀ i ∈ l, ∀ j ∈ l,
        (if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0) =
        (if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then 1 else 0) +
        (if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then 1 else 0) := by
      intro i _ j _
      by_cases h1 : i = u ∧ j = v
      · by_cases h2 : i = v ∧ j = u
        · obtain ⟨hi1, -⟩ := h1
          obtain ⟨hi2, -⟩ := h2
          exact absurd (hi1.symm.trans hi2) huv
        · by_cases h3 : (i : Nat) < (j : Nat)
          · simp [h1, huv]
          · simp [h1, huv]
      · by_cases h2 : i = v ∧ j = u
        · by_cases h3 : (i : Nat) < (j : Nat)
          · simp [h2, huv]
          · simp [h2, huv]
        · by_cases h3 : (i : Nat) < (j : Nat) <;> simp [h1, h2, h3]
    have hΔ1 : ssum l (fun i => ssum l (fun j =>
        if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) =
        (if (u : Nat) < (v : Nat) then 1 else 0) := by
      have hcomp2 : ∀ i ∈ l, ssum l (fun j => if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if i = u then ssum l (fun j => if j = v ∧ (i : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro i _
        by_cases h : i = u
        · simp [h]
        · have hz : ssum l (fun j => if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) = 0 :=
            ssum_eq_zero fun j _ => by simp [h]
          rw [hz]; simp [h]
      rw [ssum_congr fun i hi => hcomp2 i hi, ssum_eq_single nd hu]
      have hcomp3 : ∀ j ∈ l, (if j = v ∧ (u : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if j = v then (if (u : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro j _; by_cases h : j = v <;> simp [h]
      rw [ssum_congr hcomp3, ssum_eq_single nd hv]
    have hΔ2 : ssum l (fun i => ssum l (fun j =>
        if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) =
        (if (v : Nat) < (u : Nat) then 1 else 0) := by
      have hcomp2 : ∀ i ∈ l, ssum l (fun j => if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if i = v then ssum l (fun j => if j = u ∧ (i : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro i _
        by_cases h : i = v
        · simp [h]
        · have hz : ssum l (fun j => if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) = 0 :=
            ssum_eq_zero fun j _ => by simp [h]
          rw [hz]; simp [h]
      rw [ssum_congr fun i hi => hcomp2 i hi, ssum_eq_single nd hv]
      have hcomp3 : ∀ j ∈ l, (if j = u ∧ (v : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if j = u then (if (v : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro j _; by_cases h : j = u <;> simp [h]
      rw [ssum_congr hcomp3, ssum_eq_single nd hu]
    calc ssum l (fun i => ssum l (fun j =>
            if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0))
        = ssum l (fun i => ssum l (fun j =>
            (if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then 1 else 0) +
            (if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then 1 else 0))) :=
          ssum_congr fun i hi => ssum_congr fun j hj => hsplit i hi j hj
      _ = ssum l (fun i => ssum l (fun j => if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) +
          ssum l (fun i => ssum l (fun j => if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) := by
          rw [ssum_congr fun i _ => ssum_add _ _ _, ssum_add]
      _ = (if (u : Nat) < (v : Nat) then 1 else 0) + (if (v : Nat) < (u : Nat) then 1 else 0) := by
          rw [hΔ1, hΔ2]
      _ = 1 := by
          have huv2 : (u : Nat) ≠ (v : Nat) := fun h => huv (Fin.ext h)
          by_cases h1 : (u : Nat) < (v : Nat) <;> by_cases h2 : (v : Nat) < (u : Nat) <;>
            simp [h1, h2] <;> omega
  -- Assemble.
  have hsum : ecountIn G.adj l =
      ecountIn (deleteEdge G u v).adj l +
      ssum l (fun i => ssum l (fun j =>
        if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) := by
    calc ecountIn G.adj l
        = ssum l (fun i => ssum l (fun j =>
            (if (i : Nat) < (j : Nat) then ((deleteEdge G u v).adj i j).toNat else 0) +
            (if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then 1 else 0))) :=
          ssum_congr fun i hi => ssum_congr fun j hj => pw i hi j hj
      _ = ssum l (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then ((deleteEdge G u v).adj i j).toNat else 0)) +
          ssum l (fun i => ssum l (fun j =>
            if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) := by
          rw [ssum_congr fun i _ => ssum_add _ _ _, ssum_add]
      _ = ecountIn (deleteEdge G u v).adj l +
          ssum l (fun i => ssum l (fun j =>
            if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) := by
          rfl
  omega

/-! ## Triangles through a vertex -/

/-- Removing vertex `y` destroys at least one triangle when `y` lies on one. -/
theorem tcountIn_ge_delVertex_add_one (G : Gph n) {l : List (Fin n)} (nd : l.Nodup)
    {y u w : Fin n} (hy : y ∈ l) (hu : u ∈ l) (hw : w ∈ l)
    (hyu : y ≠ u) (hyw : y ≠ w) (huw : u ≠ w)
    (h1 : G.adj y u = true) (h2 : G.adj y w = true) (h3 : G.adj u w = true) :
    tcountIn G.adj (delVertex l y) + 1 ≤ tcountIn G.adj l := by
  -- symmetry variants
  have h1' : G.adj u y = true := by rw [G.sym u y]; exact h1
  have h2' : G.adj w y = true := by rw [G.sym w y]; exact h2
  have h3' : G.adj w u = true := by rw [G.sym w u]; exact h3
  -- value-level distinctness
  have vy'u : (y : Nat) ≠ (u : Nat) := fun h => hyu (Fin.ext h)
  have vy'w : (y : Nat) ≠ (w : Nat) := fun h => hyw (Fin.ext h)
  have vu'w : (u : Nat) ≠ (w : Nat) := fun h => huw (Fin.ext h)
  -- the `== y` filter is the complement of `delVertex`
  have hfeq : (l.filter fun v => !(!(v == y))) = l.filter fun v => v == y := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases hpa : (a == y) <;> simp [List.filter, hpa] <;> exact ih
  -- monotonicity of inner sums under filtering
  have hmono : ∀ i ∈ delVertex l y,
      ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj i j k)) ≤
      ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)) := by
    intro i _
    exact Nat.le_trans (ssum_le fun j _ => ssum_filter_le _ _ _) (ssum_filter_le _ _ _)
  have hle : tcountIn G.adj (delVertex l y) ≤
      ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
    ssum_le hmono
  have hle' : ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) ≤
      tcountIn G.adj l := ssum_filter_le _ _ _
  have hsplit := ssum_filter_add (fun v => !(v == y)) l
    (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)))
  rw [hfeq, ssum_filter_eq_single nd hy] at hsplit
  -- hsplit : tcountIn l = ssum l' F + F y  (up to the delVertex/filter defeq)
  -- case split on the rank of y among {u, w}
  by_cases hA : (y : Nat) < (u : Nat) ∧ (y : Nat) < (w : Nat)
  · -- y is the smallest: the triangle shows up at `i = y`.
    obtain ⟨u', hu'mem, hu'eq, w', hw'mem, hw'eq, hord⟩ :
        ∃ u' ∈ l, (u' = u ∨ u' = w) ∧ ∃ w' ∈ l, (w' = u ∨ w' = w) ∧ (u' : Nat) < (w' : Nat) := by
      by_cases huw2 : (u : Nat) < (w : Nat)
      · exact ⟨u, hu, Or.inl rfl, w, hw, Or.inr rfl, huw2⟩
      · exact ⟨w, hw, Or.inr rfl, u, hu, Or.inl rfl, by omega⟩
    have hyu' : (y : Nat) < (u' : Nat) := by
      cases hu'eq with
      | inl h => rw [h]; omega
      | inr h => rw [h]; omega
    have hterm : triTerm G.adj y u' w' = 1 := by
      have e1 : G.adj y u' = true := by cases hu'eq with | inl h => rw [h]; exact h1 | inr h => rw [h]; exact h2
      have e3 : G.adj u' w' = true := by
        cases hu'eq with
        | inl ha => cases hw'eq with
          | inl hb => rw [ha, hb] at hord; omega
          | inr hb => rw [ha, hb]; exact h3
        | inr ha => cases hw'eq with
          | inl hb => rw [ha, hb]; exact h3'
          | inr hb => rw [ha, hb] at hord; omega
      have e2 : G.adj y w' = true := by cases hw'eq with | inl h => rw [h]; exact h1 | inr h => rw [h]; exact h2
      simp [triTerm, hyu', hord, e1, e3, e2]
    have hFy : 1 ≤ ssum l (fun j => ssum l (fun k => triTerm G.adj y j k)) :=
      one_le_ssum_of_mem hu'mem (one_le_ssum_of_mem hw'mem (by simp [hterm]))
    -- tcountIn l = ssum l' F + F y ≥ tcountIn l' + 1
    have hsplit2 : tcountIn G.adj l =
        ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) +
        ssum l (fun j => ssum l (fun k => triTerm G.adj y j k)) := hsplit
    omega
  · -- y is not smallest
    by_cases hB : (u : Nat) < (y : Nat) ∧ (y : Nat) < (w : Nat)
    · -- middle: u < y < w, strict at `j = y` inside `F u`
      have hGy : 1 ≤ ssum l (fun k => triTerm G.adj u y k) :=
        one_le_ssum_of_mem hw (by
          have ht : triTerm G.adj u y w = 1 := by
            simp [triTerm, hB.1, hB.2, h1', h2, h3]
          simp [ht])
      have huL' : u ∈ delVertex l y := by
        have hb : (!(u == y)) = true := by simp [hyu.symm]
        exact List.mem_filter.mpr ⟨hu, hb⟩
      have hrow : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) + 1 ≤
          ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) := by
        have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) ≤
            ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) :=
          ssum_le fun j _ => ssum_filter_le _ _ _
        have h2 : ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) + 1 ≤
            ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) := by
          have hsp := ssum_filter_add (fun v => v == y) l (fun j => ssum l (fun k => triTerm G.adj u j k))
          rw [ssum_filter_eq_single nd hy] at hsp
          have hsp2 : ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) =
              ssum l (fun k => triTerm G.adj u y k) +
              ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) := hsp
          omega
        omega
      have htot : tcountIn G.adj (delVertex l y) + 1 ≤
          ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) := by
        have hpoint : ∀ i ∈ delVertex l y,
            ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj i j k)) ≤
            ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)) := hmono
        exact ssum_add_one_le hpoint u huL' hrow
      omega
    · -- largest: both u, w < y (or w < y < u handled symmetrically via roles)
      by_cases hC : (w : Nat) < (y : Nat) ∧ (y : Nat) < (u : Nat)
      · -- middle with roles of u, w swapped: w < y < u
        have hGy : 1 ≤ ssum l (fun k => triTerm G.adj w y k) :=
          one_le_ssum_of_mem hu (by
            have ht : triTerm G.adj w y u = 1 := by
              simp [triTerm, hC.1, hC.2, h2', h1, h3']
            simp [ht])
        have hwL' : w ∈ delVertex l y := by
          have hb : (!(w == y)) = true := by simp [hyw.symm]
          exact List.mem_filter.mpr ⟨hw, hb⟩
        have hrow : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) + 1 ≤
            ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) := by
          have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) ≤
              ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) :=
            ssum_le fun j _ => ssum_filter_le _ _ _
          have h2 : ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) + 1 ≤
              ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) := by
            have hsp := ssum_filter_add (fun v => v == y) l (fun j => ssum l (fun k => triTerm G.adj w j k))
            rw [ssum_filter_eq_single nd hy] at hsp
            have hsp2 : ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) =
                ssum l (fun k => triTerm G.adj w y k) +
                ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) := hsp
            omega
          omega
        have htot : tcountIn G.adj (delVertex l y) + 1 ≤
            ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
          ssum_add_one_le hmono w hwL' hrow
        omega
      · -- largest: u < y and w < y. Let a = min u w, b = max u w: strict at k = y inside row b.
        have huy : (u : Nat) < (y : Nat) := by omega
        have hwy : (w : Nat) < (y : Nat) := by omega
        by_cases huw2 : (u : Nat) < (w : Nat)
        · -- a = u, b = w: strict at j = w (row u), k = y
          have hterm : triTerm G.adj u w y = 1 := by
            simp [triTerm, huw2, hwy, h3, h2', h1']
          have hHw : 1 ≤ ssum l (fun k => triTerm G.adj u w k) :=
            one_le_ssum_of_mem hy (by simp [hterm])
          have hroww : ssum (delVertex l y) (fun k => triTerm G.adj u w k) + 1 ≤
              ssum l (fun k => triTerm G.adj u w k) := by
            have hsp := ssum_filter_add (fun v => v == y) l (fun k => triTerm G.adj u w k)
            rw [ssum_filter_eq_single nd hy] at hsp
            have hsp2 : ssum l (fun k => triTerm G.adj u w k) =
                triTerm G.adj u w y + ssum (delVertex l y) (fun k => triTerm G.adj u w k) := hsp
            omega
          have hwL' : w ∈ delVertex l y := by
            have hb : (!(w == y)) = true := by simp [hyw.symm]
            exact List.mem_filter.mpr ⟨hw, hb⟩
          have hrowu : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) + 1 ≤
              ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) := by
            have hpoint : ∀ j ∈ delVertex l y, ssum (delVertex l y) (fun k => triTerm G.adj u j k) ≤
                ssum l (fun k => triTerm G.adj u j k) := fun j _ => ssum_filter_le _ _ _
            have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) + 1 ≤
                ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) :=
              ssum_add_one_le hpoint w hwL' hroww
            exact Nat.le_trans h1 (ssum_filter_le _ _ _)
          have huL' : u ∈ delVertex l y := by
            have hb : (!(u == y)) = true := by simp [hyu.symm]
            exact List.mem_filter.mpr ⟨hu, hb⟩
          have htot : tcountIn G.adj (delVertex l y) + 1 ≤
              ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
            ssum_add_one_le hmono u huL' hrowu
          omega
        · -- a = w, b = u
          have hterm : triTerm G.adj w u y = 1 := by
            have hwu : (w : Nat) < (u : Nat) := by omega
            simp [triTerm, hwu, huy, h3', h1', h2']
          have hHu : 1 ≤ ssum l (fun k => triTerm G.adj w u k) :=
            one_le_ssum_of_mem hy (by simp [hterm])
          have hrowu2 : ssum (delVertex l y) (fun k => triTerm G.adj w u k) + 1 ≤
              ssum l (fun k => triTerm G.adj w u k) := by
            have hsp := ssum_filter_add (fun v => v == y) l (fun k => triTerm G.adj w u k)
            rw [ssum_filter_eq_single nd hy] at hsp
            have hsp2 : ssum l (fun k => triTerm G.adj w u k) =
                triTerm G.adj w u y + ssum (delVertex l y) (fun k => triTerm G.adj w u k) := hsp
            omega
          have huL' : u ∈ delVertex l y := by
            have hb : (!(u == y)) = true := by simp [hyu.symm]
            exact List.mem_filter.mpr ⟨hu, hb⟩
          have hroww2 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) + 1 ≤
              ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) := by
            have hpoint : ∀ j ∈ delVertex l y, ssum (delVertex l y) (fun k => triTerm G.adj w j k) ≤
                ssum l (fun k => triTerm G.adj w j k) := fun j _ => ssum_filter_le _ _ _
            have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) + 1 ≤
                ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) :=
              ssum_add_one_le hpoint u huL' hrowu2
            exact Nat.le_trans h1 (ssum_filter_le _ _ _)
          have hwL' : w ∈ delVertex l y := by
            have hb : (!(w == y)) = true := by simp [hyw.symm]
            exact List.mem_filter.mpr ⟨hw, hb⟩
          have htot : tcountIn G.adj (delVertex l y) + 1 ≤
              ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
            ssum_add_one_le hmono w hwL' hroww2
          omega

/-- Pointwise triangle-term monotonicity under edge deletion. -/
theorem triTerm_deleteEdge_le (G : Gph n) (u v i j k : Fin n) :
    triTerm (deleteEdge G u v).adj i j k ≤ triTerm G.adj i j k := by
  simp only [triTerm]
  by_cases hc : (i : Nat) < (j : Nat) ∧ (j : Nat) < (k : Nat)
  · simp [hc]
    by_cases h1 : (deleteEdge G u v).adj i j = true
    · have h1' : G.adj i j = true := deleteEdge_adj_true h1
      by_cases h2 : (deleteEdge G u v).adj j k = true
      · have h2' : G.adj j k = true := deleteEdge_adj_true h2
        by_cases h3 : (deleteEdge G u v).adj i k = true
        · have h3' : G.adj i k = true := deleteEdge_adj_true h3
          simp [h1, h1', h2, h2', h3, h3']
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [hc]

/-- Deleting an edge that lies on a triangle destroys at least one triangle. -/
theorem tcountIn_deleteEdge_add_one_le (G : Gph n) {l : List (Fin n)}
    {u v w : Fin n} (hu : u ∈ l) (hv : v ∈ l) (hw : w ∈ l)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h1 : G.adj u v = true) (h2 : G.adj u w = true) (h3 : G.adj v w = true) :
    tcountIn (deleteEdge G u v).adj l + 1 ≤ tcountIn G.adj l := by
  have h1' : G.adj v u = true := by rw [G.sym v u]; exact h1
  have h2' : G.adj w u = true := by rw [G.sym w u]; exact h2
  have h3' : G.adj w v = true := by rw [G.sym w v]; exact h3
  have huv2 : (u : Nat) ≠ (v : Nat) := fun h => huv (Fin.ext h)
  have huw2 : (u : Nat) ≠ (w : Nat) := fun h => huw (Fin.ext h)
  have hvw2 : (v : Nat) ≠ (w : Nat) := fun h => hvw (Fin.ext h)
  -- generic finisher: strict gap at the sorted triple (s1, s2, s3)
  have finish : ∀ (s1 s2 s3 : Fin n), s1 ∈ l → s2 ∈ l → s3 ∈ l →
      triTerm (deleteEdge G u v).adj s1 s2 s3 + 1 ≤ triTerm G.adj s1 s2 s3 →
      tcountIn (deleteEdge G u v).adj l + 1 ≤ tcountIn G.adj l := by
    intro s1 s2 s3 h1m h2m h3m hst
    have hstrict2 : ssum l (fun k => triTerm (deleteEdge G u v).adj s1 s2 k) + 1 ≤
        ssum l (fun k => triTerm G.adj s1 s2 k) :=
      ssum_add_one_le (fun k _ => triTerm_deleteEdge_le G u v s1 s2 k) s3 h3m hst
    have hstrict1 : ssum l (fun j => ssum l (fun k => triTerm (deleteEdge G u v).adj s1 j k)) + 1 ≤
        ssum l (fun j => ssum l (fun k => triTerm G.adj s1 j k)) :=
      ssum_add_one_le (fun j _ => ssum_le (fun k _ => triTerm_deleteEdge_le G u v s1 j k)) s2 h2m hstrict2
    have hmono : ∀ i ∈ l, ssum l (fun j => ssum l (fun k => triTerm (deleteEdge G u v).adj i j k)) ≤
        ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)) :=
      fun i _ => ssum_le (fun j _ => ssum_le (fun k _ => triTerm_deleteEdge_le G u v i j k))
    exact ssum_add_one_le hmono s1 h1m hstrict1
  have hduv : (deleteEdge G u v).adj u v = false := by rw [deleteEdge_adj_eq]; simp
  have hdvu : (deleteEdge G u v).adj v u = false := by rw [deleteEdge_adj_eq]; simp
  by_cases c1 : (u : Nat) < (v : Nat)
  · by_cases c2 : (v : Nat) < (w : Nat)
    · -- u < v < w
      refine finish u v w hu hv hw ?_
      have o2 : (v : Nat) < (w : Nat) := c2
      simp only [triTerm]
      simp [c1, o2, hduv, h1, h2, h3]
    · by_cases c3 : (u : Nat) < (w : Nat)
      · -- u < w < v
        refine finish u w v hu hw hv ?_
        have o2 : (w : Nat) < (v : Nat) := by omega
        simp only [triTerm]
        simp [c3, o2, hduv, h2, h3', h1]
      · -- w < u < v
        refine finish w u v hw hu hv ?_
        have o1 : (w : Nat) < (u : Nat) := by omega
        simp only [triTerm]
        simp [o1, c1, hduv, h2', h3', h1]
  · by_cases c2 : (u : Nat) < (w : Nat)
    · -- v < u < w
      refine finish v u w hv hu hw ?_
      have o1 : (v : Nat) < (u : Nat) := by omega
      simp only [triTerm]
      simp [o1, c2, hdvu, h1', h3, h2]
    · by_cases c3 : (w : Nat) < (v : Nat)
      · -- w < v < u
        refine finish w v u hw hv hu ?_
        have o2 : (v : Nat) < (u : Nat) := by omega
        simp only [triTerm]
        simp [c3, o2, hdvu, h3', h2', h1']
      · -- v < w < u
        refine finish v w u hv hw hu ?_
        have o1 : (v : Nat) < (w : Nat) := by omega
        have o2 : (w : Nat) < (u : Nat) := by omega
        simp only [triTerm]
        simp [o1, o2, hdvu, h3, h2', h1']

/-! ## Shrinking to exactly the threshold -/

/-- If `l` has more than `X` edges, delete edges one at a time until exactly `X`;
triangle count only drops. -/
theorem shrink {n : Nat} {l : List (Fin n)} (nd : l.Nodup) :
    ∀ (G : Gph n) (X : Nat), X ≤ ecountIn G.adj l →
      ∃ G' : Gph n, ecountIn G'.adj l = X ∧ tcountIn G'.adj l ≤ tcountIn G.adj l := by
  intro G X hX
  by_cases hEq : ecountIn G.adj l = X
  · exact ⟨G, hEq, Nat.le_refl _⟩
  · have hgt : X + 1 ≤ ecountIn G.adj l := by omega
    have hpos : 1 ≤ ecountIn G.adj l := by omega
    obtain ⟨i, hi, j, hj, hij, hAij⟩ := exists_edge_of_pos G hpos
    have hij' : i ≠ j := by intro h; rw [h] at hij; omega
    have hcount := ecountIn_deleteEdge G nd hi hj hij' hAij
    have hmono := tcountIn_deleteEdge_le G i j l
    obtain ⟨G', h1', h2'⟩ := shrink nd (deleteEdge G i j) X (by omega)
    exact ⟨G', h1', Nat.le_trans h2' hmono⟩
termination_by G X => ecountIn G.adj l - X

/-! ## Arithmetic helpers -/

theorem sq_two_mul (a : Nat) : (2 * a) * (2 * a) = 4 * (a * a) := by
  calc (2 * a) * (2 * a) = 2 * (a * (2 * a)) := Nat.mul_assoc ..
    _ = 2 * ((2 * a) * a) := by rw [Nat.mul_comm a (2 * a)]
    _ = 2 * (2 * (a * a)) := by rw [Nat.mul_assoc]
    _ = 4 * (a * a) := by rw [← Nat.mul_assoc]

theorem sq_add_one (a : Nat) : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega

theorem sq_add_two (a : Nat) : (a + 2) * (a + 2) = a * a + 4 * a + 4 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega

theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- Triangle count is monotone under vertex removal. -/
theorem tcountIn_delVertex_le (G : Gph n) (l : List (Fin n)) (y : Fin n) :
    tcountIn G.adj (delVertex l y) ≤ tcountIn G.adj l :=
  Nat.le_trans
    (Nat.le_trans
      (ssum_le fun _ _ => ssum_le fun _ _ => ssum_filter_le _ _ _)
      (ssum_le fun _ _ => ssum_filter_le _ _ _))
    (ssum_filter_le _ _ _)

/-- Base case: a 3-vertex list whose three pairs are all edges has a triangle. -/
theorem base_three (G : Gph n) {a b c : Fin n}
    (h1 : G.adj a b = true) (h2 : G.adj a c = true) (h3 : G.adj b c = true) :
    1 ≤ tcountIn G.adj [a, b, c] := by
  have h1' : G.adj b a = true := by rw [G.sym b a]; exact h1
  have h2' : G.adj c a = true := by rw [G.sym c a]; exact h2
  have h3' : G.adj c b = true := by rw [G.sym c b]; exact h3
  have habv : (a : Nat) ≠ (b : Nat) := by
    intro h
    rw [Fin.ext h, G.irr b] at h1
    exact Bool.noConfusion h1
  have hacv : (a : Nat) ≠ (c : Nat) := by
    intro h
    rw [Fin.ext h, G.irr c] at h2
    exact Bool.noConfusion h2
  have hbcv : (b : Nat) ≠ (c : Nat) := by
    intro h
    rw [Fin.ext h, G.irr c] at h3
    exact Bool.noConfusion h3
  by_cases o1 : (a : Nat) < (b : Nat)
  · by_cases o2 : (b : Nat) < (c : Nat)
    · -- a < b < c
      apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
      apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
      apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
      simp [triTerm, o1, o2, h1, h2, h3]
    · by_cases o3 : (a : Nat) < (c : Nat)
      · by_cases o4 : (c : Nat) < (b : Nat)
        · -- a < c < b
          apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
          simp [triTerm, o3, o4, h2, h3', h1]
        · -- c = b, contradicting h3
          have hce : c = b := Fin.ext (by omega)
          rw [hce, G.irr b] at h3
          exact Bool.noConfusion h3
      · by_cases o4 : (c : Nat) < (a : Nat)
        · -- c < a < b
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_self : c ∈ c :: [])))
          apply one_le_ssum_of_mem (List.mem_cons_self : a ∈ a :: b :: c :: [])
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_self : b ∈ b :: c :: []))
          simp [triTerm, o4, o1, h2', h3', h1]
        · -- c = a, contradicting h2
          have hce : c = a := Fin.ext (by omega)
          rw [hce, G.irr a] at h2
          exact Bool.noConfusion h2
  · by_cases o2 : (a : Nat) < (c : Nat)
    · by_cases o3 : (b : Nat) < (a : Nat)
      · -- b < a < c
        apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
        apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
        apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
        simp [triTerm, o3, o2, h1', h2, h3]
      · -- b = a, contradicting h1
        have hbe : b = a := Fin.ext (by omega)
        rw [hbe, G.irr a] at h1
        exact Bool.noConfusion h1
    · by_cases o3 : (b : Nat) < (c : Nat)
      · by_cases o4 : (c : Nat) < (a : Nat)
        · -- b < c < a
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
          apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
          simp [triTerm, o3, o4, h3, h2', h1']
        · -- c = a, contradicting h2
          have hce : c = a := Fin.ext (by omega)
          rw [hce, G.irr a] at h2
          exact Bool.noConfusion h2
      · by_cases o5 : (c : Nat) < (b : Nat)
        · -- c < b < a
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_self : c ∈ c :: [])))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_self : b ∈ b :: c :: []))
          apply one_le_ssum_of_mem (List.mem_cons_self : a ∈ a :: b :: c :: [])
          have o6 : (b : Nat) < (a : Nat) := by omega
          simp [triTerm, o5, o6, h2', h3', h1']
        · -- c = b, contradicting h3
          have hce : c = b := Fin.ext (by omega)
          rw [hce, G.irr b] at h3
          exact Bool.noConfusion h3

/-! ## Rademacher's theorem -/

/-- **Rademacher's theorem** (list form): a simple graph with more than
`⌊m²/4⌋` edges among `m` vertices contains at least `⌊m/2⌋` triangles.

Proof: Erdős's 1955 induction (remove a vertex of minimal degree). -/
theorem rademacher_list : ∀ (m : Nat) (n : Nat) (G : Gph n) (l : List (Fin n)), l.Nodup →
    l.length = m → m * m / 4 + 1 ≤ ecountIn G.adj l → m / 2 ≤ tcountIn G.adj l := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n G l nd hm he
    -- WLOG exactly `⌊m²/4⌋ + 1` edges (deleting edges only lowers the triangle count).
    obtain ⟨G₁, hE1, hmono₁⟩ := shrink nd G (m * m / 4 + 1) he
    refine Nat.le_trans ?_ hmono₁
    by_cases hm2 : m ≤ 2
    · -- Vacuous: too few edges exist.
      have hb : ecountIn G₁.adj l ≤ l.length - 1 := ecountIn_le_of_length_le_two G₁.adj (by omega)
      rw [hm, hE1] at hb
      have h2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      obtain h0 | h1 | h2 := h2
      · subst h0; omega
      · subst h1; omega
      · subst h2; omega
    · by_cases hm3 : m = 3
      · -- Base: three vertices, three edges.
        subst hm3
        have h3l : ∃ a b c : Fin n, l = [a, b, c] := by
          cases l with
          | nil => simp at hm
          | cons a l =>
            cases l with
            | nil => simp at hm
            | cons b l =>
              cases l with
              | nil => simp at hm
              | cons c l =>
                cases l with
                | nil => exact ⟨a, b, c, rfl⟩
                | cons d l =>
                  simp only [List.length_cons] at hm
                  omega
        obtain ⟨a, b, c, rfl⟩ := h3l
        have hE : ecountIn G₁.adj [a, b, c] = 3 := by
          have h := hE1
          simp at h
          exact h
        have hexp : ecountIn G₁.adj [a, b, c] ≤
            (G₁.adj a b).toNat + ((G₁.adj a c).toNat + (G₁.adj b c).toNat) := by
          have pairle : ∀ x y : Fin n, (if (x : Nat) < (y : Nat) then (G₁.adj x y).toNat else 0) +
              (if (y : Nat) < (x : Nat) then (G₁.adj y x).toNat else 0) ≤ (G₁.adj x y).toNat := by
            intro x y
            by_cases h : (x : Nat) < (y : Nat)
            · have h2 : ¬ (y : Nat) < (x : Nat) := by omega
              simp [h, h2]
            · by_cases h2 : (y : Nat) < (x : Nat)
              · simp [h, h2, G₁.sym y x]
              · simp [h, h2]
          simp [ecountIn, ssum_cons, ssum_nil]
          rw [G₁.sym b a, G₁.sym c a, G₁.sym c b]
          have p1 := pairle a b
          have p2 := pairle a c
          have p3 := pairle b c
          rw [G₁.sym b a] at p1
          rw [G₁.sym c a] at p2
          rw [G₁.sym c b] at p3
          omega
        have h1 : G₁.adj a b = true := by
          have hb1 := Bool.toNat_le_one (G₁.adj a c)
          have hb2 := Bool.toNat_le_one (G₁.adj b c)
          by_cases h : G₁.adj a b = true
          · exact h
          · have h0 : (G₁.adj a b).toNat = 0 := by simp [bool_eq_false_of_ne_true h]
            omega
        have h2 : G₁.adj a c = true := by
          have hb1 := Bool.toNat_le_one (G₁.adj a b)
          have hb2 := Bool.toNat_le_one (G₁.adj b c)
          by_cases h : G₁.adj a c = true
          · exact h
          · have h0 : (G₁.adj a c).toNat = 0 := by simp [bool_eq_false_of_ne_true h]
            omega
        have h3 : G₁.adj b c = true := by
          have hb1 := Bool.toNat_le_one (G₁.adj a b)
          have hb2 := Bool.toNat_le_one (G₁.adj a c)
          by_cases h : G₁.adj b c = true
          · exact h
          · have h0 : (G₁.adj b c).toNat = 0 := by simp [bool_eq_false_of_ne_true h]
            omega
        have ht := base_three G₁ h1 h2 h3
        exact ht
      · -- Inductive step, m ≥ 4.
        have hm4 : 4 ≤ m := by omega
        obtain ⟨q, hq⟩ : ∃ q, m = 2 * q + 1 ∨ m = 2 * q + 2 := by
          by_cases hodd : m % 2 = 1
          · exact ⟨m / 2, Or.inl (by omega)⟩
          · exact ⟨m / 2 - 1, Or.inr (by omega)⟩
        have hshake : ssum l (fun v => degIn G₁.adj l v) = 2 * ecountIn G₁.adj l := handshake G₁ l
        cases hq with
        | inl hodd =>
          -- m = 2q + 1 odd, q ≥ 2: some vertex has degree ≤ q; delete it.
          have hq2 : 2 ≤ q := by omega
          have hsq1 : m * m = 4 * (q * q) + 4 * q + 1 := by
            rw [hodd, sq_add_one, sq_two_mul]; omega
          rw [hsq1] at hE1
          have hmin : ∃ y ∈ l, degIn G₁.adj l y ≤ q := by
            by_cases hc : ∃ y ∈ l, degIn G₁.adj l y ≤ q
            · exact hc
            · have hall : ∀ v ∈ l, q + 1 ≤ degIn G₁.adj l v := by
                intro v hv
                by_cases hcv : degIn G₁.adj l v ≤ q
                · exact absurd ⟨v, hv, hcv⟩ hc
                · omega
              have hge : ssum l (fun v => degIn G₁.adj l v) ≥ ssum l (fun _ => q + 1) :=
                ssum_ge hall
              rw [ssum_const, hm] at hge
              have hexp4 : (q + 1) * (2 * q + 1) = 2 * (q * q) + 3 * q + 1 := by
                have h1 : q * (2 * q) = 2 * (q * q) := by
                  rw [Nat.mul_comm q (2 * q), Nat.mul_assoc]
                rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                omega
              rw [hodd] at hge
              rw [hexp4] at hge
              omega
          obtain ⟨y, hy, hydeg⟩ := hmin
          have hE' := ecountIn_eq_filter_add_deg G₁ nd hy
          have hlen' : (delVertex l y).length = m - 1 := by
            have h := length_filter_neq_of_mem nd hy
            rwa [hm] at h
          have hnd' : (delVertex l y).Nodup := nd.filter _
          have hE'' : (m - 1) * (m - 1) / 4 + 1 ≤ ecountIn G₁.adj (delVertex l y) := by
            have hsub : (m - 1) * (m - 1) = 4 * (q * q) := by
              rw [hodd]
              have h1 : 2 * q + 1 - 1 = 2 * q := by omega
              rw [h1]
              exact sq_two_mul q
            rw [hsub]
            omega
          have hIH := ih (m - 1) (by omega) n G₁ (delVertex l y) hnd' hlen' hE''
          have hmono2 := tcountIn_delVertex_le G₁ l y
          omega
        | inr heven =>
          -- m = 2q + 2 even, q ≥ 1.
          have hq1 : 1 ≤ q := by omega
          have hsq2 : m * m = 4 * (q * q) + 8 * q + 4 := by
            rw [heven, sq_add_two, sq_two_mul]; omega
          rw [hsq2] at hE1
          by_cases hmin : ∃ w ∈ l, degIn G₁.adj l w ≤ q
          · -- Sub-case 1: delete a low-degree vertex, destroy one triangle, induct.
            obtain ⟨w, hw, hwdeg⟩ := hmin
            have hE' := ecountIn_eq_filter_add_deg G₁ nd hw
            have hlen' : (delVertex l w).length = m - 1 := by
              have h := length_filter_neq_of_mem nd hw
              rwa [hm] at h
            have hnd' : (delVertex l w).Nodup := nd.filter _
            have hmantel : (m - 1) * (m - 1) / 4 + 1 ≤ ecountIn G₁.adj (delVertex l w) := by
              have hsub : (m - 1) * (m - 1) = 4 * (q * q) + 4 * q + 1 := by
                rw [heven]
                have h1 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
                rw [h1, sq_add_one, sq_two_mul]
                omega
              rw [hsub]
              omega
            obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hAab, hAac, hAbc⟩ :=
              mantel G₁ (m - 1) (delVertex l w) hnd' hlen' hmantel
            have hcount := ecountIn_deleteEdge G₁ hnd' ha hb hab hAab
            have hE'' : (m - 1) * (m - 1) / 4 + 1 ≤
                ecountIn (deleteEdge G₁ a b).adj (delVertex l w) := by
              have hsub : (m - 1) * (m - 1) = 4 * (q * q) + 4 * q + 1 := by
                rw [heven]
                have h1 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
                rw [h1, sq_add_one, sq_two_mul]
                omega
              rw [hsub]
              omega
            have hIH := ih (m - 1) (by omega) n (deleteEdge G₁ a b) (delVertex l w) hnd' hlen' hE''
            have hdrop := tcountIn_deleteEdge_add_one_le G₁ ha hb hc hab hac hbc hAab hAac hAbc
            have hmono2 := tcountIn_delVertex_le G₁ l w
            omega
          · -- Sub-case 2: all degrees are q + 1 or more; at most two vertices exceed q + 1.
            have hall : ∀ v ∈ l, q + 1 ≤ degIn G₁.adj l v := by
              intro v hv
              by_cases hcv : degIn G₁.adj l v ≤ q
              · exact absurd ⟨v, hv, hcv⟩ hmin
              · omega
            have hmantel : m * m / 4 + 1 ≤ ecountIn G₁.adj l := by omega
            obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hAab, hAac, hAbc⟩ :=
              mantel G₁ m l nd hm hmantel
            -- Some vertex of the triangle has degree exactly q + 1.
            have hex : ∃ y ∈ l, (y = a ∨ y = b ∨ y = c) ∧ degIn G₁.adj l y ≤ q + 1 := by
              by_cases hcase : ∃ y ∈ l, (y = a ∨ y = b ∨ y = c) ∧ degIn G₁.adj l y ≤ q + 1
              · exact hcase
              · have h3hi : ∀ y ∈ l, y = a ∨ y = b ∨ y = c → q + 2 ≤ degIn G₁.adj l y := by
                  intro y hy hyor
                  by_cases hcy : degIn G₁.adj l y ≤ q + 1
                  · exact absurd ⟨y, hy, hyor, hcy⟩ hcase
                  · omega
                have hpoint : ∀ v ∈ l,
                    q + 1 + (if v = a ∨ v = b ∨ v = c then 1 else 0) ≤ degIn G₁.adj l v := by
                  intro v hv
                  by_cases hv3 : v = a ∨ v = b ∨ v = c
                  · simp [hv3]
                    exact h3hi v hv hv3
                  · simp [hv3]
                    exact hall v hv
                have hsum := ssum_ge hpoint
                rw [ssum_add, ssum_const, hm] at hsum
                have hind : ssum l (fun v => if v = a ∨ v = b ∨ v = c then 1 else 0) = 3 := by
                  have hp : ∀ v ∈ l, (if v = a ∨ v = b ∨ v = c then (1 : Nat) else 0) =
                      (if v = a then 1 else 0) + ((if v = b then 1 else 0) +
                        (if v = c then 1 else 0)) := by
                    intro v _
                    by_cases h1 : v = a
                    · subst h1
                      simp [hab, hac]
                    · by_cases h2 : v = b
                      · subst h2
                        simp [hab.symm, hbc]
                      · by_cases h3 : v = c
                        · subst h3
                          simp [hac.symm, hbc.symm]
                        · simp [h1, h2, h3]
                  rw [ssum_congr hp, ssum_add, ssum_add]
                  rw [ssum_eq_single nd ha, ssum_eq_single nd hb, ssum_eq_single nd hc]
                rw [hind] at hsum
                have hexp3 : (q + 1) * (2 * q + 2) = 2 * (q * q) + 4 * q + 2 := by
                  have h1 : q * (2 * q) = 2 * (q * q) := by
                    rw [Nat.mul_comm q (2 * q), Nat.mul_assoc]
                  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                  omega
                rw [heven] at hsum
                rw [hexp3] at hsum
                have hshake2 : ssum l (degIn G₁.adj l) = 2 * ecountIn G₁.adj l := hshake
                have hcontra : (0 : Nat) < 0 := by omega
                exact (Nat.lt_irrefl 0 hcontra).elim
            obtain ⟨y, hy, hyor, hydeg⟩ := hex
            have hydeg2 : degIn G₁.adj l y = q + 1 := by
              have h := hall y hy
              omega
            have hE' := ecountIn_eq_filter_add_deg G₁ nd hy
            have hlen' : (delVertex l y).length = m - 1 := by
              have h := length_filter_neq_of_mem nd hy
              rwa [hm] at h
            have hnd' : (delVertex l y).Nodup := nd.filter _
            have hE'' : (m - 1) * (m - 1) / 4 + 1 ≤ ecountIn G₁.adj (delVertex l y) := by
              have hsub : (m - 1) * (m - 1) = 4 * (q * q) + 4 * q + 1 := by
                rw [heven]
                have h1 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
                rw [h1, sq_add_one, sq_two_mul]
                omega
              rw [hsub]
              omega
            have hIH := ih (m - 1) (by omega) n G₁ (delVertex l y) hnd' hlen' hE''
            -- y lies on the triangle, so deletion destroys at least one triangle.
            have htri : tcountIn G₁.adj (delVertex l y) + 1 ≤ tcountIn G₁.adj l := by
              cases hyor with
              | inl hya =>
                rw [hya]
                exact tcountIn_ge_delVertex_add_one G₁ nd ha hb hc hab hac hbc hAab hAac hAbc
              | inr hrest =>
                cases hrest with
                | inl hyb =>
                  rw [hyb]
                  have hAba : G₁.adj b a = true := by rw [G₁.sym b a]; exact hAab
                  exact tcountIn_ge_delVertex_add_one G₁ nd hb ha hc hab.symm hbc hac hAba hAbc hAac
                | inr hyc =>
                  rw [hyc]
                  have hAca : G₁.adj c a = true := by rw [G₁.sym c a]; exact hAac
                  have hAcb : G₁.adj c b = true := by rw [G₁.sym c b]; exact hAbc
                  exact tcountIn_ge_delVertex_add_one G₁ nd hc ha hb hac.symm hbc.symm hab hAca hAcb hAab
            omega

/-! ## Flattened triple lists and triangle extraction (JSP-000839) -/

/-- Componentwise equality of triples. -/
theorem triple_eq_of_eq {a b c a' b' c' : α} (h : (a, b, c) = (a', b', c')) :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := Prod.ext_iff.mp h
  have h2 := Prod.ext_iff.mp h1.2
  exact ⟨h1.1, h2.1, h2.2⟩

/-- All ordered triples with components from `l`, as a flat list. -/
def triples (l : List α) : List (α × α × α) :=
  l.flatMap fun i => l.flatMap fun j => l.map fun k => (i, j, k)

theorem mem_triples {l : List α} {t : α × α × α} :
    t ∈ triples l ↔ t.1 ∈ l ∧ t.2.1 ∈ l ∧ t.2.2 ∈ l := by
  constructor
  · intro h
    rw [triples, List.mem_flatMap] at h
    obtain ⟨i, hi, h⟩ := h
    rw [List.mem_flatMap] at h
    obtain ⟨j, hj, h⟩ := h
    rw [List.mem_map] at h
    obtain ⟨k, hk, hijk⟩ := h
    rw [← hijk]
    exact ⟨hi, hj, hk⟩
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    rw [triples, List.mem_flatMap]
    exact ⟨t.1, h1, List.mem_flatMap.mpr ⟨t.2.1, h2, List.mem_map.mpr ⟨t.2.2, h3, rfl⟩⟩⟩

theorem nodup_triples {l : List α} (nd : l.Nodup) : (triples l).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at nd ⊢
  rw [triples, List.pairwise_flatMap]
  constructor
  · intro i _
    rw [List.pairwise_flatMap]
    constructor
    · intro j _
      rw [List.pairwise_map]
      exact nd.imp fun hab h => hab (triple_eq_of_eq h).2.2
    · refine nd.imp fun {j₁ j₂} hjj x hx y hy hxy => hjj ?_
      rw [List.mem_map] at hx hy
      obtain ⟨k₁, _, hk₁⟩ := hx
      obtain ⟨k₂, _, hk₂⟩ := hy
      rw [← hk₁, ← hk₂] at hxy
      exact (triple_eq_of_eq hxy).2.1
  · refine nd.imp fun {i₁ i₂} hii x hx y hy hxy => hii ?_
    rw [List.mem_flatMap] at hx hy
    obtain ⟨j₁, _, hx⟩ := hx
    obtain ⟨j₂, _, hy⟩ := hy
    rw [List.mem_map] at hx hy
    obtain ⟨k₁, _, hk₁⟩ := hx
    obtain ⟨k₂, _, hk₂⟩ := hy
    rw [← hk₁, ← hk₂] at hxy
    exact (triple_eq_of_eq hxy).1

/-- Sums split over `List.flatMap`. -/
theorem ssum_flatMap (l : List α) (g : α → List β) (f : β → Nat) :
    ssum (l.flatMap g) f = ssum l (fun a => ssum (g a) f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h1 : ssum (List.flatMap g (a :: l)) f = ssum (g a) f + ssum (l.flatMap g) f := by
      rw [List.flatMap_cons]
      simp only [ssum, List.map_append, List.sum_append]
    rw [h1, ih, ssum_cons]

/-- Sums commute with `List.map`. -/
theorem ssum_map (l : List α) (g : α → β) (f : β → Nat) :
    ssum (l.map g) f = ssum l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ssum_cons, ssum_cons, ih]

/-- The nested triangle count equals the flat sum over `triples l`. -/
theorem tcountIn_eq_triples (A : Fin n → Fin n → Bool) (l : List (Fin n)) :
    tcountIn A l = ssum (triples l) (fun t => triTerm A t.1 t.2.1 t.2.2) := by
  have step1 : ssum (triples l) (fun t => triTerm A t.1 t.2.1 t.2.2)
      = ssum l (fun i => ssum (l.flatMap fun j => l.map fun k => (i, j, k))
          (fun t => triTerm A t.1 t.2.1 t.2.2)) := ssum_flatMap l _ _
  have step2 : ∀ i ∈ l, ssum (l.flatMap fun j => l.map fun k => (i, j, k))
          (fun t => triTerm A t.1 t.2.1 t.2.2)
      = ssum l (fun j => ssum (l.map fun k => (i, j, k))
          (fun t => triTerm A t.1 t.2.1 t.2.2)) := fun i _ => ssum_flatMap l _ _
  have step3 : ∀ i j, ssum (l.map fun k => (i, j, k)) (fun t => triTerm A t.1 t.2.1 t.2.2)
      = ssum l (fun k => triTerm A i j k) := fun i j => ssum_map l _ _
  rw [step1, ssum_congr step2]
  show ssum l (fun i => ssum l (fun j => ssum l (fun k => triTerm A i j k))) = _
  apply ssum_congr
  intro i _
  apply ssum_congr
  intro j _
  exact (step3 i j).symm

theorem triTerm_le_one (A : Fin n → Fin n → Bool) (i j k : Fin n) : triTerm A i j k ≤ 1 := by
  rw [triTerm]
  split
  · exact Bool.toNat_le_one _
  · exact Nat.zero_le _

theorem triTerm_eq_one {A : Fin n → Fin n → Bool} {i j k : Fin n}
    (h : triTerm A i j k = 1) :
    (i : Nat) < (j : Nat) ∧ (j : Nat) < (k : Nat) ∧
    A i j = true ∧ A j k = true ∧ A i k = true := by
  rw [triTerm] at h
  split at h
  · rename_i hlt
    obtain ⟨hij, hjk⟩ := hlt
    have h1 : 1 ≤ ((A i j && A j k) && A i k).toNat := by omega
    obtain ⟨h2, h3⟩ := bool_and_true_of_toNat_pos h1
    have h4 : 1 ≤ (A i j && A j k).toNat := by rw [h2]; exact Nat.le_refl 1
    obtain ⟨h5, h6⟩ := bool_and_true_of_toNat_pos h4
    exact ⟨hij, hjk, h5, h6, h3⟩
  · omega

/-- A duplicate-free list with term bound `1` and total `≥ 2` has two distinct
positive terms. -/
theorem ssum_two_witness [DecidableEq α] {l : List α} (nd : l.Nodup) {f : α → Nat}
    (h1 : ∀ x ∈ l, f x ≤ 1) (h2 : 2 ≤ ssum l f) :
    ∃ x ∈ l, ∃ y ∈ l, x ≠ y ∧ 1 ≤ f x ∧ 1 ≤ f y := by
  obtain ⟨x, hx, hfx⟩ := ssum_pos_of_pos (l := l) (f := f) (by omega)
  have hsplit : ssum l f = f x + ssum (l.filter (fun v => !(v == x))) f := by
    have h := ssum_filter_add (fun v => v == x) l f
    rw [ssum_filter_eq_single nd hx] at h
    omega
  have hrest : 1 ≤ ssum (l.filter (fun v => !(v == x))) f := by
    have hfx1 : f x ≤ 1 := h1 x hx
    omega
  obtain ⟨y, hy, hfy⟩ := ssum_pos_of_pos hrest
  rw [List.mem_filter] at hy
  refine ⟨x, hx, y, hy.1, ?_, hfx, hfy⟩
  intro hxy
  rw [hxy] at hy
  simp at hy

/-- Triangle-count `≥ 2` yields two distinct sorted triangle triples. -/
theorem exists_two_tris {n : Nat} {A : Fin n → Fin n → Bool} {l : List (Fin n)}
    (nd : l.Nodup) (h : 2 ≤ tcountIn A l) :
    ∃ t₁ t₂ : Fin n × Fin n × Fin n, t₁ ≠ t₂ ∧ t₁ ∈ triples l ∧ t₂ ∈ triples l ∧
      triTerm A t₁.1 t₁.2.1 t₁.2.2 = 1 ∧ triTerm A t₂.1 t₂.2.1 t₂.2.2 = 1 := by
  rw [tcountIn_eq_triples] at h
  obtain ⟨x, hx, y, hy, hne, hfx, hfy⟩ :=
    ssum_two_witness (nodup_triples nd) (fun t _ => triTerm_le_one A t.1 t.2.1 t.2.2) h
  have hfx1 : triTerm A x.1 x.2.1 x.2.2 = 1 := Nat.le_antisymm (triTerm_le_one ..) hfx
  have hfy1 : triTerm A y.1 y.2.1 y.2.2 = 1 := Nat.le_antisymm (triTerm_le_one ..) hfy
  exact ⟨x, y, hne, hx, hy, hfx1, hfy1⟩

/-! ## Injective counting: triangles through a fixed edge -/

/-- Adjacency between any two distinct vertices of a triangle triple. -/
theorem adj_of_mem_tri {n : Nat} {G : Gph n} {a b c p q : Fin n}
    (ht : triTerm G.adj a b c = 1) (hp : a = p ∨ b = p ∨ c = p)
    (hq : a = q ∨ b = q ∨ c = q) (hpq : p ≠ q) : G.adj p q = true := by
  obtain ⟨-, -, hab, hbc, hac⟩ := triTerm_eq_one ht
  have hba : G.adj b a = true := by rw [G.sym b a]; exact hab
  have hcb : G.adj c b = true := by rw [G.sym c b]; exact hbc
  have hca : G.adj c a = true := by rw [G.sym c a]; exact hac
  rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> simp_all

theorem eq_or_symm {p a b c : α} (h : a = p ∨ b = p ∨ c = p) :
    p = a ∨ p = b ∨ p = c :=
  h.elim (fun h => Or.inl h.symm)
    (fun h => h.elim (fun h2 => Or.inr (Or.inl h2.symm)) (fun h2 => Or.inr (Or.inr h2.symm)))

theorem eq_or_symm' {w a b c : α} (h : w = a ∨ w = b ∨ w = c) :
    a = w ∨ b = w ∨ c = w :=
  h.elim (fun h => Or.inl h.symm)
    (fun h => h.elim (fun h2 => Or.inr (Or.inl h2.symm)) (fun h2 => Or.inr (Or.inr h2.symm)))

/-- The component of `t` different from both `u` and `v` (fallback: third). -/
def thirdOf (u v : Fin n) (t : Fin n × Fin n × Fin n) : Fin n :=
  if t.1 ≠ u ∧ t.1 ≠ v then t.1 else if t.2.1 ≠ u ∧ t.2.1 ≠ v then t.2.1 else t.2.2

/-- In a sorted triangle triple containing distinct `u` and `v`, `thirdOf`
picks out the unique third vertex `w`, and every component is `u`, `v` or `w`. -/
theorem thirdOf_spec {n : Nat} {A : Fin n → Fin n → Bool} {u v a b c : Fin n}
    (hne : u ≠ v) (ht : triTerm A a b c = 1)
    (hu : a = u ∨ b = u ∨ c = u) (hv : a = v ∨ b = v ∨ c = v) :
    (thirdOf u v (a, b, c) ≠ u ∧ thirdOf u v (a, b, c) ≠ v) ∧
    (thirdOf u v (a, b, c) = a ∨ thirdOf u v (a, b, c) = b ∨ thirdOf u v (a, b, c) = c) ∧
    (a = u ∨ a = v ∨ a = thirdOf u v (a, b, c)) ∧
    (b = u ∨ b = v ∨ b = thirdOf u v (a, b, c)) ∧
    (c = u ∨ c = v ∨ c = thirdOf u v (a, b, c)) := by
  obtain ⟨hab, hbc, -, -, -⟩ := triTerm_eq_one ht
  have d_ab : a ≠ b := fun h => by rw [Fin.ext_iff] at h; omega
  have d_bc : b ≠ c := fun h => by rw [Fin.ext_iff] at h; omega
  have d_ac : a ≠ c := fun h => by rw [Fin.ext_iff] at h; omega
  unfold thirdOf
  split
  · rename_i h1
    obtain ⟨hau, hav⟩ := h1
    have hub : b = u ∨ b = v := by
      rcases hu with h|h|h
      · exact absurd h hau
      · exact Or.inl h
      · rcases hv with h2|h2|h2
        · exact absurd h2 hav
        · exact Or.inr h2
        · exact absurd (h.symm.trans h2) hne
    have hvc : c = u ∨ c = v := by
      rcases hu with h|h|h
      · exact absurd h hau
      · rcases hv with h2|h2|h2
        · exact absurd h2 hav
        · exact absurd (h.symm.trans h2) hne
        · exact Or.inr h2
      · exact Or.inl h
    exact ⟨⟨hau, hav⟩, Or.inl rfl, Or.inr (Or.inr rfl),
      hub.elim Or.inl (fun h => Or.inr (Or.inl h)),
      hvc.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  · split
    · rename_i hna hb
      obtain ⟨hbu, hbv⟩ := hb
      have hau' : a = u ∨ a = v := by
        by_cases h : a = u
        · exact Or.inl h
        · by_cases h2 : a = v
          · exact Or.inr h2
          · exact absurd ⟨h, h2⟩ hna
      have hcc : c = u ∨ c = v := by
        rcases hu with h|h|h
        · rcases hv with h2|h2|h2
          · exact absurd (h.symm.trans h2) hne
          · exact absurd h2 hbv
          · exact Or.inr h2
        · exact absurd h hbu
        · exact Or.inl h
      exact ⟨⟨hbu, hbv⟩, Or.inr (Or.inl rfl),
        hau'.elim Or.inl (fun h => Or.inr (Or.inl h)), Or.inr (Or.inr rfl),
        hcc.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    · rename_i hna hnb
      have hau' : a = u ∨ a = v := by
        by_cases h : a = u
        · exact Or.inl h
        · by_cases h2 : a = v
          · exact Or.inr h2
          · exact absurd ⟨h, h2⟩ hna
      have hbv' : b = u ∨ b = v := by
        by_cases h : b = u
        · exact Or.inl h
        · by_cases h2 : b = v
          · exact Or.inr h2
          · exact absurd ⟨h, h2⟩ hnb
      have hcu : c ≠ u := by
        intro h
        have hav' : a = v := by
          rcases hau' with h1|h1
          · exact absurd (h1.trans h.symm) d_ac
          · exact h1
        have hbv'' : b = v := by
          rcases hbv' with h1|h1
          · exact absurd (h1.trans h.symm) d_bc
          · exact h1
        exact d_ab (hav'.trans hbv''.symm)
      have hcv : c ≠ v := by
        intro h
        have hau'' : a = u := by
          rcases hau' with h1|h1
          · exact h1
          · exact absurd (h1.trans h.symm) d_ac
        have hbu'' : b = u := by
          rcases hbv' with h1|h1
          · exact h1
          · exact absurd (h1.trans h.symm) d_bc
        exact d_ab (hau''.trans hbu''.symm)
      exact ⟨⟨hcu, hcv⟩, Or.inr (Or.inr rfl),
        hau'.elim Or.inl (fun h => Or.inr (Or.inl h)),
        hbv'.elim Or.inl (fun h => Or.inr (Or.inl h)), Or.inr (Or.inr rfl)⟩

/-- Strictly increasing triples with equal component sets are equal. -/
theorem sorted_triple_eq {n : Nat} {a b c a' b' c' : Fin n}
    (h1 : (a : Nat) < b) (h2 : (b : Nat) < c)
    (h1' : (a' : Nat) < b') (h2' : (b' : Nat) < c')
    (hs : ∀ x : Fin n, (x = a ∨ x = b ∨ x = c) ↔ (x = a' ∨ x = b' ∨ x = c')) :
    a = a' ∧ b = b' ∧ c = c' := by
  have e1 : (a : Nat) = a' ∨ (a : Nat) = b' ∨ (a : Nat) = c' := by
    rcases (hs a).mp (Or.inl rfl) with h|h|h
    · exact Or.inl (Fin.ext_iff.mp h)
    · exact Or.inr (Or.inl (Fin.ext_iff.mp h))
    · exact Or.inr (Or.inr (Fin.ext_iff.mp h))
  have e1' : (a' : Nat) = a ∨ (a' : Nat) = b ∨ (a' : Nat) = c := by
    rcases (hs a').mpr (Or.inl rfl) with h|h|h
    · exact Or.inl (Fin.ext_iff.mp h)
    · exact Or.inr (Or.inl (Fin.ext_iff.mp h))
    · exact Or.inr (Or.inr (Fin.ext_iff.mp h))
  have ea : (a : Nat) = (a' : Nat) := by omega
  have e2 : (b : Nat) = a' ∨ (b : Nat) = b' ∨ (b : Nat) = c' := by
    rcases (hs b).mp (Or.inr (Or.inl rfl)) with h|h|h
    · exact Or.inl (Fin.ext_iff.mp h)
    · exact Or.inr (Or.inl (Fin.ext_iff.mp h))
    · exact Or.inr (Or.inr (Fin.ext_iff.mp h))
  have e2' : (b' : Nat) = a ∨ (b' : Nat) = b ∨ (b' : Nat) = c := by
    rcases (hs b').mpr (Or.inr (Or.inl rfl)) with h|h|h
    · exact Or.inl (Fin.ext_iff.mp h)
    · exact Or.inr (Or.inl (Fin.ext_iff.mp h))
    · exact Or.inr (Or.inr (Fin.ext_iff.mp h))
  have eb : (b : Nat) = (b' : Nat) := by omega
  have e3 : (c : Nat) = a' ∨ (c : Nat) = b' ∨ (c : Nat) = c' := by
    rcases (hs c).mp (Or.inr (Or.inr rfl)) with h|h|h
    · exact Or.inl (Fin.ext_iff.mp h)
    · exact Or.inr (Or.inl (Fin.ext_iff.mp h))
    · exact Or.inr (Or.inr (Fin.ext_iff.mp h))
  have e3' : (c' : Nat) = a ∨ (c' : Nat) = b ∨ (c' : Nat) = c := by
    rcases (hs c').mpr (Or.inr (Or.inr rfl)) with h|h|h
    · exact Or.inl (Fin.ext_iff.mp h)
    · exact Or.inr (Or.inl (Fin.ext_iff.mp h))
    · exact Or.inr (Or.inr (Fin.ext_iff.mp h))
  have ec : (c : Nat) = (c' : Nat) := by omega
  exact ⟨Fin.ext_iff.mpr ea, Fin.ext_iff.mpr eb, Fin.ext_iff.mpr ec⟩

/-- Injection bound for weighted sums: if `φ` maps `L` injectively into `M`
and dominates pointwise, the sums compare. -/
theorem ssum_le_of_inj [DecidableEq α] [DecidableEq β] {L : List α} {M : List β}
    (ndL : L.Nodup) (ndM : M.Nodup) (φ : α → β) {f : α → Nat} {g : β → Nat}
    (hmem : ∀ x ∈ L, φ x ∈ M)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, φ x = φ y → x = y)
    (hle : ∀ x ∈ L, f x ≤ g (φ x)) :
    ssum L f ≤ ssum M g := by
  induction L generalizing M with
  | nil => exact Nat.zero_le _
  | cons a L ih =>
    rw [List.nodup_cons] at ndL
    rw [ssum_cons]
    have hφa : φ a ∈ M := hmem a (List.mem_cons_self ..)
    have hM : ssum M g = g (φ a) + ssum (M.filter (fun v => !(v == φ a))) g := by
      have h := ssum_filter_add (fun v => v == φ a) M g
      rw [ssum_filter_eq_single ndM hφa] at h
      omega
    rw [hM]
    have hmem' : ∀ x ∈ L, φ x ∈ M.filter (fun v => !(v == φ a)) := by
      intro x hx
      rw [List.mem_filter]
      have hxL : x ∈ a :: L := List.mem_cons_of_mem _ hx
      refine ⟨hmem x hxL, ?_⟩
      have hne : φ x ≠ φ a := by
        intro h
        have hxa : x = a := hinj x hxL a (List.mem_cons_self ..) h
        rw [hxa] at hx
        exact ndL.1 hx
      simp [hne]
    have hinj' : ∀ x ∈ L, ∀ y ∈ L, φ x = φ y → x = y :=
      fun x hx y hy hxy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy
    have hle'' : ∀ x ∈ L, f x ≤ g (φ x) :=
      fun x hx => hle x (List.mem_cons_of_mem _ hx)
    have hle' : ssum L f ≤ ssum (M.filter (fun v => !(v == φ a))) g :=
      ih ndL.2 (ndM.filter _) hmem' hinj' hle''
    have hfa : f a ≤ g (φ a) := hle a (List.mem_cons_self ..)
    omega

/-- If every triangle contains the vertices `u` and `v` (`u ≠ v`), the triangle
count is at most the common-neighbor count of `u` and `v`. -/
theorem tcountIn_le_commonIn {n : Nat} (G : Gph n) {l : List (Fin n)}
    (nd : l.Nodup) {u v : Fin n} (hne : u ≠ v)
    (huv : ∀ t : Fin n × Fin n × Fin n, t ∈ triples l → triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
       (t.1 = u ∨ t.2.1 = u ∨ t.2.2 = u) ∧ (t.1 = v ∨ t.2.1 = v ∨ t.2.2 = v)) :
    tcountIn G.adj l ≤ commonIn G.adj l u v := by
  rw [tcountIn_eq_triples]
  show _ ≤ ssum l (fun j => (G.adj u j && G.adj v j).toNat)
  have hv : ssum (triples l) (fun t => triTerm G.adj t.1 t.2.1 t.2.2) =
      ssum ((triples l).filter (fun t => triTerm G.adj t.1 t.2.1 t.2.2 == 1))
        (fun t => triTerm G.adj t.1 t.2.1 t.2.2) := by
    apply ssum_filter_of_vanish
    intro x _ hp
    have h1 : triTerm G.adj x.1 x.2.1 x.2.2 ≤ 1 := triTerm_le_one ..
    have h2 : triTerm G.adj x.1 x.2.1 x.2.2 ≠ 1 := by
      intro hc
      rw [hc] at hp
      simp at hp
    omega
  rw [hv]
  apply ssum_le_of_inj ((nodup_triples nd).filter _) nd (thirdOf u v)
  · intro x hx
    have hxm := mem_triples.mp (List.mem_filter.mp hx).1
    rw [thirdOf]
    split
    · exact hxm.1
    · split
      · exact hxm.2.1
      · exact hxm.2.2
  · intro x hx y hy hxy
    rw [List.mem_filter] at hx hy
    have htx : triTerm G.adj x.1 x.2.1 x.2.2 = 1 := beq_iff_eq.mp hx.2
    have hty : triTerm G.adj y.1 y.2.1 y.2.2 = 1 := beq_iff_eq.mp hy.2
    obtain ⟨hux, hvx⟩ := huv x hx.1 htx
    obtain ⟨huy, hvy⟩ := huv y hy.1 hty
    obtain ⟨hijx, hjkx, -, -, -⟩ := triTerm_eq_one htx
    obtain ⟨hijy, hjky, -, -, -⟩ := triTerm_eq_one hty
    obtain ⟨⟨hwxu, hwxv⟩, hwxc, hax, hbx, hcx⟩ := thirdOf_spec hne htx hux hvx
    obtain ⟨⟨hwyu, hwyv⟩, hwyc, hay, hby, hcy⟩ := thirdOf_spec hne hty huy hvy
    have hxy' : thirdOf u v (x.1, x.2.1, x.2.2) = thirdOf u v (y.1, y.2.1, y.2.2) := hxy
    rw [← hxy'] at hwyu hwyv hwyc hay hby hcy
    have hs : ∀ z : Fin n, (z = x.1 ∨ z = x.2.1 ∨ z = x.2.2) ↔
        (z = y.1 ∨ z = y.2.1 ∨ z = y.2.2) := by
      intro z
      constructor
      · intro hz
        have h3 : z = u ∨ z = v ∨ z = thirdOf u v (x.1, x.2.1, x.2.2) := by
          rcases hz with h|h|h
          · rw [h]; exact hax
          · rw [h]; exact hbx
          · rw [h]; exact hcx
        rcases h3 with h|h|h
        · rw [h]; exact eq_or_symm huy
        · rw [h]; exact eq_or_symm hvy
        · rw [h]; exact hwyc
      · intro hz
        have h3 : z = u ∨ z = v ∨ z = thirdOf u v (x.1, x.2.1, x.2.2) := by
          rcases hz with h|h|h
          · rw [h]; exact hay
          · rw [h]; exact hby
          · rw [h]; exact hcy
        rcases h3 with h|h|h
        · rw [h]; exact eq_or_symm hux
        · rw [h]; exact eq_or_symm hvx
        · rw [h]; exact hwxc
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hijx hjkx hijy hjky hs
    exact Prod.ext e1 (Prod.ext e2 e3)
  · intro x hx
    obtain ⟨hxl, hxf⟩ := List.mem_filter.mp hx
    have htx : triTerm G.adj x.1 x.2.1 x.2.2 = 1 := beq_iff_eq.mp hxf
    obtain ⟨hux, hvx⟩ := huv x hxl htx
    obtain ⟨⟨hwu, hwv⟩, hwc, -, -, -⟩ := thirdOf_spec hne htx hux hvx
    have hadj1 : G.adj u (thirdOf u v x) = true :=
      adj_of_mem_tri htx hux (eq_or_symm' hwc) (Ne.symm hwu)
    have hadj2 : G.adj v (thirdOf u v x) = true :=
      adj_of_mem_tri htx hvx (eq_or_symm' hwc) (Ne.symm hwv)
    rw [hadj1, hadj2]
    exact triTerm_le_one ..

/-! ## Edge-partition machine (JSP-000839) -/

/-- Edge indicator of an ordered pair (same body as `ecountIn`'s inner term). -/
def eTerm (A : Fin n → Fin n → Bool) (i j : Fin n) : Nat :=
  if (i : Nat) < (j : Nat) then (A i j).toNat else 0

theorem ecountIn_eq_ssum_eTerm (A : Fin n → Fin n → Bool) (l : List (Fin n)) :
    ecountIn A l = ssum l (fun i => ssum l (fun j => eTerm A i j)) := rfl

/-- Number of edges between lists `P` and `Q` (each cross pair counted once
from the `P` side). -/
def crossCount (A : Fin n → Fin n → Bool) (P Q : List (Fin n)) : Nat :=
  ssum P (fun i => ssum Q (fun j => (A i j).toNat))

theorem crossCount_le (A : Fin n → Fin n → Bool) (P Q : List (Fin n)) :
    crossCount A P Q ≤ P.length * Q.length := by
  have h1 : crossCount A P Q ≤ ssum P (fun _ => Q.length) := by
    apply ssum_le
    intro i _
    have h2 : ssum Q (fun j => (A i j).toNat) ≤ ssum Q (fun _ => 1) :=
      ssum_le (fun j _ => Bool.toNat_le_one _)
    rw [ssum_const, Nat.one_mul] at h2
    exact h2
  rw [ssum_const] at h1
  have hc := Nat.mul_comm Q.length P.length
  omega

theorem crossCount_eq_zero (A : Fin n → Fin n → Bool) (P Q : List (Fin n))
    (h : ∀ i ∈ P, ∀ j ∈ Q, A i j = false) : crossCount A P Q = 0 := by
  apply ssum_eq_zero
  intro i hi
  apply ssum_eq_zero
  intro j hj
  rw [h i hi j hj]
  rfl

theorem degIn_filter_add' (A : Fin n → Fin n → Bool) (l : List (Fin n)) (p : Fin n → Bool)
    (x : Fin n) :
    degIn A l x = degIn A (l.filter p) x + degIn A (l.filter (fun v => !p v)) x :=
  ssum_filter_add p l _

theorem crossCount_filter_add (A : Fin n → Fin n → Bool) (P Q : List (Fin n))
    (p : Fin n → Bool) :
    crossCount A P Q = crossCount A P (Q.filter p) + crossCount A P (Q.filter (fun v => !p v)) := by
  have h : ∀ i, ssum Q (fun j => (A i j).toNat) =
      ssum (Q.filter p) (fun j => (A i j).toNat) +
      ssum (Q.filter (fun v => !p v)) (fun j => (A i j).toNat) :=
    fun i => ssum_filter_add p Q _
  show ssum P (fun i => ssum Q (fun j => (A i j).toNat)) =
    ssum P (fun i => ssum (Q.filter p) (fun j => (A i j).toNat)) +
    ssum P (fun i => ssum (Q.filter (fun v => !p v)) (fun j => (A i j).toNat))
  rw [ssum_congr (fun i _ => h i)]
  exact ssum_add _ _ _

/-- Edge count splits along a Boolean predicate: inside parts plus cross part. -/
theorem ecountIn_partition (G : Gph n) (l : List (Fin n)) (p : Fin n → Bool) :
    ecountIn G.adj l =
      ecountIn G.adj (l.filter p) + ecountIn G.adj (l.filter (fun v => !p v)) +
      crossCount G.adj (l.filter p) (l.filter (fun v => !p v)) := by
  have h1 : ecountIn G.adj l =
      ssum (l.filter p) (fun i => ssum l (fun j => eTerm G.adj i j)) +
      ssum (l.filter (fun v => !p v)) (fun i => ssum l (fun j => eTerm G.adj i j)) := by
    rw [ecountIn_eq_ssum_eTerm]
    exact ssum_filter_add p l _
  have h2 : ssum (l.filter p) (fun i => ssum l (fun j => eTerm G.adj i j)) =
      ssum (l.filter p) (fun i => ssum (l.filter p) (fun j => eTerm G.adj i j)) +
      ssum (l.filter p) (fun i => ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj i j)) := by
    have hj : ∀ i, ssum l (fun j => eTerm G.adj i j) =
        ssum (l.filter p) (fun j => eTerm G.adj i j) +
        ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj i j) :=
      fun i => ssum_filter_add p l _
    rw [ssum_congr (fun i _ => hj i)]
    exact ssum_add _ _ _
  have h3 : ssum (l.filter (fun v => !p v)) (fun i => ssum l (fun j => eTerm G.adj i j)) =
      ssum (l.filter (fun v => !p v)) (fun i => ssum (l.filter p) (fun j => eTerm G.adj i j)) +
      ssum (l.filter (fun v => !p v))
        (fun i => ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj i j)) := by
    have hj : ∀ i, ssum l (fun j => eTerm G.adj i j) =
        ssum (l.filter p) (fun j => eTerm G.adj i j) +
        ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj i j) :=
      fun i => ssum_filter_add p l _
    rw [ssum_congr (fun i _ => hj i)]
    exact ssum_add _ _ _
  have hswap : ssum (l.filter (fun v => !p v)) (fun i => ssum (l.filter p) (fun j => eTerm G.adj i j)) =
      ssum (l.filter p) (fun i => ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj j i)) :=
    ssum_swap _ _ _
  have hpt : ∀ i ∈ l.filter p, ∀ j ∈ l.filter (fun v => !p v),
      eTerm G.adj i j + eTerm G.adj j i = (G.adj i j).toNat := by
    intro i hi j hj
    rw [List.mem_filter] at hi hj
    have hne : (i : Nat) ≠ (j : Nat) := by
      intro he
      have hij : i = j := Fin.ext he
      rw [← hij] at hj
      rw [hi.2] at hj
      simp at hj
    unfold eTerm
    by_cases hlt : (i : Nat) < (j : Nat)
    · have hlt2 : ¬ (j : Nat) < (i : Nat) := by omega
      simp [hlt, hlt2]
    · have hlt2 : (j : Nat) < (i : Nat) := by omega
      simp [hlt, hlt2, G.sym j i]
  have hX : ssum (l.filter p) (fun i => ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj i j)) +
      ssum (l.filter p) (fun i => ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj j i)) =
      crossCount G.adj (l.filter p) (l.filter (fun v => !p v)) := by
    rw [← ssum_add]
    apply ssum_congr
    intro i hi
    rw [← ssum_add]
    apply ssum_congr
    intro j hj
    exact hpt i hi j hj
  have hPP : ecountIn G.adj (l.filter p) =
      ssum (l.filter p) (fun i => ssum (l.filter p) (fun j => eTerm G.adj i j)) :=
    ecountIn_eq_ssum_eTerm _ _
  have hQQ : ecountIn G.adj (l.filter (fun v => !p v)) =
      ssum (l.filter (fun v => !p v))
        (fun i => ssum (l.filter (fun v => !p v)) (fun j => eTerm G.adj i j)) :=
    ecountIn_eq_ssum_eTerm _ _
  omega

/-- Edge count on a two-element list. -/
theorem ecountIn_pair {n : Nat} (G : Gph n) (a b : Fin n) (hab : a ≠ b) :
    ecountIn G.adj [a, b] = (G.adj a b).toNat := by
  have h2 : ecountIn G.adj [a, b] =
      (if (a : Nat) < (b : Nat) then (G.adj a b).toNat else 0) +
      (if (b : Nat) < (a : Nat) then (G.adj b a).toNat else 0) := by
    simp [ecountIn, ssum]
  rw [h2]
  by_cases h : (a : Nat) < (b : Nat)
  · have h3 : ¬ (b : Nat) < (a : Nat) := by omega
    simp [h, h3]
  · have h3 : (b : Nat) < (a : Nat) := by
      have hne : (a : Nat) ≠ (b : Nat) := fun he => hab (Fin.ext he)
      omega
    simp [h, h3, G.sym b a]

/-- A duplicate-free list of length `2` is an explicit pair. -/
theorem exists_pair {l : List α} (nd : l.Nodup) (h : l.length = 2) :
    ∃ a b : α, a ≠ b ∧ l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a l =>
    cases l with
    | nil => simp at h
    | cons b l =>
      cases l with
      | nil =>
        rw [List.nodup_cons] at nd
        exact ⟨a, b, fun h => nd.1 (List.mem_singleton.mpr h), rfl⟩
      | cons c l => simp at h

/-- A nodup length-2 list containing distinct `u`, `v` has edge count `1`
when `u`, `v` are adjacent. -/
theorem ecountIn_eq_one_of_pair {n : Nat} (G : Gph n) {l : List (Fin n)}
    (nd : l.Nodup) (hlen : l.length = 2) {u v : Fin n}
    (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) (hA : G.adj u v = true) :
    ecountIn G.adj l = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := exists_pair nd hlen
  rw [List.mem_cons, List.mem_singleton] at hu hv
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact absurd (hu.trans hv.symm) huv
    · rw [← hu, ← hv, ecountIn_pair G u v huv, hA]
      rfl
  · rcases hv with hv | hv
    · rw [← hu, ← hv, ecountIn_pair G v u (Ne.symm huv), G.sym v u, hA]
      rfl
    · exact absurd (hu.trans hv.symm) huv

/-- `ecountIn` vanishes on an independent list. -/
theorem ecountIn_eq_zero_of_indep {n : Nat} (G : Gph n) {l : List (Fin n)}
    (h : ∀ x y : Fin n, x ∈ l → y ∈ l → x ≠ y → G.adj x y = false) :
    ecountIn G.adj l = 0 := by
  by_cases hc : ecountIn G.adj l = 0
  · exact hc
  · exfalso
    obtain ⟨x, hx, y, hy, hxy, hAxy⟩ := exists_edge_of_pos G (l := l) (by omega)
    have hne : x ≠ y := fun he => by rw [Fin.ext_iff] at he; omega
    rw [h x y hx hy hne] at hAxy
    simp at hAxy

/-- Mantel contrapositive: a triangle-free nodup list has at most `⌊m²/4⌋` edges. -/
theorem mantel_bound {n : Nat} (G : Gph n) {l : List (Fin n)} (nd : l.Nodup)
    (htri : ∀ x y z : Fin n, x ∈ l → y ∈ l → z ∈ l → x ≠ y → y ≠ z → x ≠ z →
      ¬(G.adj x y = true ∧ G.adj y z = true ∧ G.adj x z = true)) :
    ecountIn G.adj l ≤ l.length * l.length / 4 := by
  by_cases h : ecountIn G.adj l ≤ l.length * l.length / 4
  · exact h
  · exfalso
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hAxy, hAxz, hAyz⟩ :=
      mantel G _ l nd rfl (by omega)
    exact htri x y z hx hy hz hxy hyz hxz ⟨hAxy, hAyz, hAxz⟩

/-- Any three pairwise-adjacent distinct vertices yield a sorted triangle triple. -/
theorem triTerm_one_of_triangle {n : Nat} {G : Gph n} {x y z : Fin n}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hAxy : G.adj x y = true) (hAyz : G.adj y z = true) (hAxz : G.adj x z = true) :
    ∃ a b c : Fin n, triTerm G.adj a b c = 1 ∧
      (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧ (z = a ∨ z = b ∨ z = c) ∧
      (a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ (c = x ∨ c = y ∨ c = z) := by
  have hyx : G.adj y x = true := by rw [G.sym]; exact hAxy
  have hzy : G.adj z y = true := by rw [G.sym]; exact hAyz
  have hzx : G.adj z x = true := by rw [G.sym]; exact hAxz
  rcases Nat.lt_trichotomy (x : Nat) (y : Nat) with h1 | h1 | h1
  · rcases Nat.lt_trichotomy (y : Nat) (z : Nat) with h2 | h2 | h2
    · exact ⟨x, y, z, by simp [triTerm, h1, h2, hAxy, hAyz, hAxz],
        Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl),
        Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    · exact absurd (Fin.ext h2) hyz
    · rcases Nat.lt_trichotomy (x : Nat) (z : Nat) with h3 | h3 | h3
      · exact ⟨x, z, y, by simp [triTerm, h3, h2, hAxz, hzy, hAxy],
          Or.inl rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl),
          Or.inl rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
      · exact absurd (Fin.ext h3) hxz
      · exact ⟨z, x, y, by simp [triTerm, h3, h1, hzx, hAxy, hzy],
          Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), Or.inl rfl,
          Or.inr (Or.inr rfl), Or.inl rfl, Or.inr (Or.inl rfl)⟩
  · exact absurd (Fin.ext h1) hxy
  · rcases Nat.lt_trichotomy (y : Nat) (z : Nat) with h2 | h2 | h2
    · rcases Nat.lt_trichotomy (x : Nat) (z : Nat) with h3 | h3 | h3
      · exact ⟨y, x, z, by simp [triTerm, h1, h3, hyx, hAxz, hAyz],
          Or.inr (Or.inl rfl), Or.inl rfl, Or.inr (Or.inr rfl),
          Or.inr (Or.inl rfl), Or.inl rfl, Or.inr (Or.inr rfl)⟩
      · exact absurd (Fin.ext h3) hxz
      · exact ⟨y, z, x, by simp [triTerm, h2, h3, hAyz, hzx, hyx],
          Or.inr (Or.inr rfl), Or.inl rfl, Or.inr (Or.inl rfl),
          Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), Or.inl rfl⟩
    · exact absurd (Fin.ext h2) hyz
    · exact ⟨z, y, x, by simp [triTerm, h2, h1, hzy, hyx, hzx],
        Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), Or.inl rfl,
        Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), Or.inl rfl⟩

/-! ## The classification lemma (common edge or K₄) -/

/-- Component membership for a triple. -/
def memTri (t : Fin n × Fin n × Fin n) (x : Fin n) : Prop :=
  t.1 = x ∨ t.2.1 = x ∨ t.2.2 = x

/-- Two triples share an edge: they have two distinct common vertices. -/
def share2 (s t : Fin n × Fin n × Fin n) : Prop :=
  ∃ p q : Fin n, p ≠ q ∧ memTri s p ∧ memTri s q ∧ memTri t p ∧ memTri t q

theorem memTri_of_eq {n : Nat} {t : Fin n × Fin n × Fin n} {x y : Fin n}
    (h : memTri t x) (hxy : x = y) : memTri t y := hxy ▸ h

/-- If every component of `t` lies in `{p,q,r}`, so does every vertex of `t`. -/
theorem mem_of_memTri_subset {n : Nat} {t : Fin n × Fin n × Fin n} {x p q r : Fin n}
    (h1 : t.1 = p ∨ t.1 = q ∨ t.1 = r) (h2 : t.2.1 = p ∨ t.2.1 = q ∨ t.2.1 = r)
    (h3 : t.2.2 = p ∨ t.2.2 = q ∨ t.2.2 = r) (hx : memTri t x) :
    x = p ∨ x = q ∨ x = r := by
  rcases hx with h | h | h
  · rw [← h]; exact h1
  · rw [← h]; exact h2
  · rw [← h]; exact h3

/-- Two distinct elements of a two-element set cover it. -/
theorem eq_of_two_mem_pair {x y p q : α} (hne : x ≠ y)
    (hx : x = p ∨ x = q) (hy : y = p ∨ y = q) :
    (x = p ∧ y = q) ∨ (x = q ∧ y = p) := by
  rcases hx with h | h <;> rcases hy with h2 | h2
  · exact absurd (h.trans h2.symm) hne
  · exact Or.inl ⟨h, h2⟩
  · exact Or.inr ⟨h, h2⟩
  · exact absurd (h.trans h2.symm) hne

/-- **Classification**: a pairwise edge-sharing family of triangles (with at
least two members) either has a common edge `uv` contained in every triangle,
or all its triangles live inside a `K₄`. -/
theorem classification {n : Nat} (G : Gph n)
    (H : ∀ s t : Fin n × Fin n × Fin n,
      triTerm G.adj s.1 s.2.1 s.2.2 = 1 → triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
      s ≠ t → share2 s t)
    {t₁ t₂ : Fin n × Fin n × Fin n}
    (h1 : triTerm G.adj t₁.1 t₁.2.1 t₁.2.2 = 1)
    (h2 : triTerm G.adj t₂.1 t₂.2.1 t₂.2.2 = 1)
    (hne : t₁ ≠ t₂) :
    (∃ u v : Fin n, u ≠ v ∧ G.adj u v = true ∧
      ∀ t : Fin n × Fin n × Fin n, triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
        memTri t u ∧ memTri t v) ∨
    (∃ p q r s : Fin n, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      G.adj p q = true ∧ G.adj p r = true ∧ G.adj p s = true ∧
      G.adj q r = true ∧ G.adj q s = true ∧ G.adj r s = true ∧
      ∀ t : Fin n × Fin n × Fin n, triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
        (t.1 = p ∨ t.1 = q ∨ t.1 = r ∨ t.1 = s) ∧
        (t.2.1 = p ∨ t.2.1 = q ∨ t.2.1 = r ∨ t.2.1 = s) ∧
        (t.2.2 = p ∨ t.2.2 = q ∨ t.2.2 = r ∨ t.2.2 = s)) := by
  obtain ⟨p, q, hpq, hp1, hq1, hp2, hq2⟩ := H t₁ t₂ h1 h2 hne
  -- `r`: the third vertex of `t₁`; `d`: the third vertex of `t₂`.
  generalize hr_def : thirdOf p q (t₁.1, t₁.2.1, t₁.2.2) = r
  generalize hd_def : thirdOf p q (t₂.1, t₂.2.1, t₂.2.2) = d
  obtain ⟨⟨hrp, hrq⟩, hrc, ha1, hb1, hc1⟩ := thirdOf_spec hpq h1 hp1 hq1
  obtain ⟨⟨hdp, hdq⟩, hdc, ha2, hb2, hc2⟩ := thirdOf_spec hpq h2 hp2 hq2
  rw [hr_def] at hrp hrq hrc ha1 hb1 hc1
  rw [hd_def] at hdp hdq hdc ha2 hb2 hc2
  have hr1 : memTri t₁ r := eq_or_symm' hrc
  have hd2 : memTri t₂ d := eq_or_symm' hdc
  -- `r ≠ d`, otherwise `t₁ = t₂`.
  have hrd : r ≠ d := by
    intro h
    have hs : ∀ x : Fin n, (x = t₁.1 ∨ x = t₁.2.1 ∨ x = t₁.2.2) ↔
        (x = t₂.1 ∨ x = t₂.2.1 ∨ x = t₂.2.2) := by
      intro x
      have hS1 : (x = t₁.1 ∨ x = t₁.2.1 ∨ x = t₁.2.2) ↔ (x = p ∨ x = q ∨ x = r) := by
        constructor
        · intro hx
          rcases hx with hx | hx | hx
          · rw [hx]; exact ha1
          · rw [hx]; exact hb1
          · rw [hx]; exact hc1
        · intro hx
          rcases hx with hx | hx | hx
          · rw [hx]; exact eq_or_symm hp1
          · rw [hx]; exact eq_or_symm hq1
          · rw [hx]; exact hrc
      have hS2 : (x = t₂.1 ∨ x = t₂.2.1 ∨ x = t₂.2.2) ↔ (x = p ∨ x = q ∨ x = d) := by
        constructor
        · intro hx
          rcases hx with hx | hx | hx
          · rw [hx]; exact ha2
          · rw [hx]; exact hb2
          · rw [hx]; exact hc2
        · intro hx
          rcases hx with hx | hx | hx
          · rw [hx]; exact eq_or_symm hp2
          · rw [hx]; exact eq_or_symm hq2
          · rw [hx]; exact hdc
      rw [hS1, hS2, h]
    obtain ⟨hij1, hjk1, -, -, -⟩ := triTerm_eq_one h1
    obtain ⟨hij2, hjk2, -, -, -⟩ := triTerm_eq_one h2
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hij1 hjk1 hij2 hjk2 hs
    exact hne (Prod.ext e1 (Prod.ext e2 e3))
  -- Case split: either every triangle contains both `p` and `q`, or not.
  by_cases hA : ∀ t : Fin n × Fin n × Fin n, triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
      memTri t p ∧ memTri t q
  · exact Or.inl ⟨p, q, hpq, adj_of_mem_tri h1 hp1 hq1 hpq, hA⟩
  · obtain ⟨t₃, hnpq⟩ := Classical.not_forall.mp hA
    obtain ⟨h3, hnpq⟩ := Classical.not_imp.mp hnpq
    have ht₃1 : t₃ ≠ t₁ := fun h => hnpq (h ▸ ⟨hp1, hq1⟩)
    have ht₃2 : t₃ ≠ t₂ := fun h => hnpq (h ▸ ⟨hp2, hq2⟩)
    obtain ⟨x₁, x₂, hx12, hx₁3, hx₂3, hx₁1, hx₂1⟩ := H t₃ t₁ h3 h1 ht₃1
    obtain ⟨y₁, y₂, hy12, hy₁3, hy₂3, hy₁2, hy₂2⟩ := H t₃ t₂ h3 h2 ht₃2
    have hS1x : ∀ x, memTri t₁ x → x = p ∨ x = q ∨ x = r :=
      fun x hx => mem_of_memTri_subset ha1 hb1 hc1 hx
    have hS2x : ∀ x, memTri t₂ x → x = p ∨ x = q ∨ x = d :=
      fun x hx => mem_of_memTri_subset ha2 hb2 hc2 hx
    -- `r` and `d` both lie in `t₃`.
    have hr3 : memTri t₃ r := by
      by_cases hcr : memTri t₃ r
      · exact hcr
      · exfalso
        have hx₁' : x₁ = p ∨ x₁ = q := by
          rcases hS1x x₁ hx₁1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (memTri_of_eq hx₁3 h) hcr
        have hx₂' : x₂ = p ∨ x₂ = q := by
          rcases hS1x x₂ hx₂1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (memTri_of_eq hx₂3 h) hcr
        rcases eq_of_two_mem_pair hx12 hx₁' hx₂' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact hnpq ⟨memTri_of_eq hx₁3 h1', memTri_of_eq hx₂3 h2'⟩
        · exact hnpq ⟨memTri_of_eq hx₂3 h2', memTri_of_eq hx₁3 h1'⟩
    have hd3 : memTri t₃ d := by
      by_cases hcd : memTri t₃ d
      · exact hcd
      · exfalso
        have hy₁' : y₁ = p ∨ y₁ = q := by
          rcases hS2x y₁ hy₁2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (memTri_of_eq hy₁3 h) hcd
        have hy₂' : y₂ = p ∨ y₂ = q := by
          rcases hS2x y₂ hy₂2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd (memTri_of_eq hy₂3 h) hcd
        rcases eq_of_two_mem_pair hy12 hy₁' hy₂' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact hnpq ⟨memTri_of_eq hy₁3 h1', memTri_of_eq hy₂3 h2'⟩
        · exact hnpq ⟨memTri_of_eq hy₂3 h2', memTri_of_eq hy₁3 h1'⟩
    -- `e`: the third vertex of `t₃`, which must be `p` or `q`.
    generalize he_def : thirdOf r d (t₃.1, t₃.2.1, t₃.2.2) = e
    obtain ⟨⟨her, hed⟩, hec, ha3, hb3, hc3⟩ := thirdOf_spec hrd h3 hr3 hd3
    rw [he_def] at her hed hec ha3 hb3 hc3
    have hS3x : ∀ x, memTri t₃ x → x = r ∨ x = d ∨ x = e :=
      fun x hx => mem_of_memTri_subset ha3 hb3 hc3 hx
    have hx1re : x₁ = r ∨ x₁ = e := by
      rcases hS1x x₁ hx₁1 with h | h | h
      · rcases hS3x x₁ hx₁3 with h2 | h2 | h2
        · exact absurd (h.symm.trans h2) (Ne.symm hrp)
        · exact absurd (h.symm.trans h2) (Ne.symm hdp)
        · exact Or.inr h2
      · rcases hS3x x₁ hx₁3 with h2 | h2 | h2
        · exact absurd (h.symm.trans h2) (Ne.symm hrq)
        · exact absurd (h.symm.trans h2) (Ne.symm hdq)
        · exact Or.inr h2
      · exact Or.inl h
    have hx2re : x₂ = r ∨ x₂ = e := by
      rcases hS1x x₂ hx₂1 with h | h | h
      · rcases hS3x x₂ hx₂3 with h2 | h2 | h2
        · exact absurd (h.symm.trans h2) (Ne.symm hrp)
        · exact absurd (h.symm.trans h2) (Ne.symm hdp)
        · exact Or.inr h2
      · rcases hS3x x₂ hx₂3 with h2 | h2 | h2
        · exact absurd (h.symm.trans h2) (Ne.symm hrq)
        · exact absurd (h.symm.trans h2) (Ne.symm hdq)
        · exact Or.inr h2
      · exact Or.inl h
    have he_pq : e = p ∨ e = q := by
      have hone : x₁ = e ∨ x₂ = e := by
        rcases hx1re with h | h
        · rcases hx2re with h2 | h2
          · exact absurd (h.trans h2.symm) hx12
          · exact Or.inr h2
        · exact Or.inl h
      rcases hone with h | h
      · have := hS1x x₁ hx₁1
        rcases this with h1' | h1' | h1'
        · exact Or.inl (h.symm.trans h1')
        · exact Or.inr (h.symm.trans h1')
        · exact absurd (h.symm.trans h1') her
      · have := hS1x x₂ hx₂1
        rcases this with h1' | h1' | h1'
        · exact Or.inl (h.symm.trans h1')
        · exact Or.inr (h.symm.trans h1')
        · exact absurd (h.symm.trans h1') her
    -- The K₄ adjacencies.
    have hp_r : p ≠ r := Ne.symm hrp
    have hq_r : q ≠ r := Ne.symm hrq
    have hp_d : p ≠ d := Ne.symm hdp
    have hq_d : q ≠ d := Ne.symm hdq
    have hA_pq : G.adj p q = true := adj_of_mem_tri h1 hp1 hq1 hpq
    have hA_pr : G.adj p r = true := adj_of_mem_tri h1 hp1 hr1 hp_r
    have hA_qr : G.adj q r = true := adj_of_mem_tri h1 hq1 hr1 hq_r
    have hA_pd : G.adj p d = true := adj_of_mem_tri h2 hp2 hd2 hp_d
    have hA_qd : G.adj q d = true := adj_of_mem_tri h2 hq2 hd2 hq_d
    have hA_rd : G.adj r d = true := adj_of_mem_tri h3 hr3 hd3 hrd
    -- Every triangle lives inside `{p, q, r, d}`.
    refine Or.inr ⟨p, q, r, d, hpq, hp_r, hp_d, hq_r, hq_d, hrd,
      hA_pq, hA_pr, hA_pd, hA_qr, hA_qd, hA_rd, ?_⟩
    intro t₄ h4
    have hsub : ∀ z : Fin n, memTri t₄ z → z = p ∨ z = q ∨ z = r ∨ z = d := by
      intro z hz
      by_cases hz4 : z = p ∨ z = q ∨ z = r ∨ z = d
      · exact hz4
      · exfalso
        have hzp : z ≠ p := fun h => hz4 (Or.inl h)
        have hzq : z ≠ q := fun h => hz4 (Or.inr (Or.inl h))
        have hzr : z ≠ r := fun h => hz4 (Or.inr (Or.inr (Or.inl h)))
        have hzd : z ≠ d := fun h => hz4 (Or.inr (Or.inr (Or.inr h)))
        have hze : z ≠ e := fun h => hz4 (he_pq.elim (fun he => Or.inl (h.trans he))
          (fun he => Or.inr (Or.inl (h.trans he))))
        have ht₄1 : t₄ ≠ t₁ := by
          intro h
          rcases hS1x z (h ▸ hz) with h2 | h2 | h2
          · exact hzp h2
          · exact hzq h2
          · exact hzr h2
        have ht₄2 : t₄ ≠ t₂ := by
          intro h
          rcases hS2x z (h ▸ hz) with h2 | h2 | h2
          · exact hzp h2
          · exact hzq h2
          · exact hzd h2
        have ht₄3 : t₄ ≠ t₃ := by
          intro h
          rcases hS3x z (h ▸ hz) with h2 | h2 | h2
          · exact hzr h2
          · exact hzd h2
          · exact hze h2
        obtain ⟨u₁, u₂, hu12, hu₁4, hu₂4, hu₁1, hu₂1⟩ := H t₄ t₁ h4 h1 ht₄1
        obtain ⟨v₁, v₂, hv12, hv₁4, hv₂4, hv₁2, hv₂2⟩ := H t₄ t₂ h4 h2 ht₄2
        obtain ⟨w₁, w₂, hw12, hw₁4, hw₂4, hw₁3, hw₂3⟩ := H t₄ t₃ h4 h3 ht₄3
        -- `p ∈ t₄`: otherwise `{q, r, d} ∪ {z}` would sit in `t₄`.
        have hp4 : memTri t₄ p := by
          by_cases hcp : memTri t₄ p
          · exact hcp
          · exfalso
            have hu₁' : u₁ = q ∨ u₁ = r := by
              rcases hS1x u₁ hu₁1 with h | h | h
              · exact absurd (memTri_of_eq hu₁4 h) hcp
              · exact Or.inl h
              · exact Or.inr h
            have hu₂' : u₂ = q ∨ u₂ = r := by
              rcases hS1x u₂ hu₂1 with h | h | h
              · exact absurd (memTri_of_eq hu₂4 h) hcp
              · exact Or.inl h
              · exact Or.inr h
            have hq4 : memTri t₄ q := by
              rcases eq_of_two_mem_pair hu12 hu₁' hu₂' with ⟨h1', -⟩ | ⟨-, h2'⟩
              · exact memTri_of_eq hu₁4 h1'
              · exact memTri_of_eq hu₂4 h2'
            have hr4 : memTri t₄ r := by
              rcases eq_of_two_mem_pair hu12 hu₁' hu₂' with ⟨-, h2'⟩ | ⟨h1', -⟩
              · exact memTri_of_eq hu₂4 h2'
              · exact memTri_of_eq hu₁4 h1'
            have hv₁' : v₁ = q ∨ v₁ = d := by
              rcases hS2x v₁ hv₁2 with h | h | h
              · exact absurd (memTri_of_eq hv₁4 h) hcp
              · exact Or.inl h
              · exact Or.inr h
            have hv₂' : v₂ = q ∨ v₂ = d := by
              rcases hS2x v₂ hv₂2 with h | h | h
              · exact absurd (memTri_of_eq hv₂4 h) hcp
              · exact Or.inl h
              · exact Or.inr h
            have hd4 : memTri t₄ d := by
              rcases eq_of_two_mem_pair hv12 hv₁' hv₂' with ⟨-, h2'⟩ | ⟨h1', -⟩
              · exact memTri_of_eq hv₂4 h2'
              · exact memTri_of_eq hv₁4 h1'
            -- thirdOf q r on t₄: comps ⊆ {q, r, w'}, and d = w', so z ∈ {q,r,d}.
            generalize hw'_def : thirdOf q r (t₄.1, t₄.2.1, t₄.2.2) = w'
            obtain ⟨⟨hw'q, hw'r⟩, hw'c, ha4, hb4, hc4⟩ := thirdOf_spec hq_r h4 hq4 hr4
            rw [hw'_def] at hw'q hw'r hw'c ha4 hb4 hc4
            have hd_eq : d = w' := by
              rcases mem_of_memTri_subset ha4 hb4 hc4 hd4 with h | h | h
              · exact absurd h.symm hq_d
              · exact absurd h.symm hrd
              · exact h
            have hz_in : z = q ∨ z = r ∨ z = w' :=
              mem_of_memTri_subset ha4 hb4 hc4 hz
            rcases hz_in with h | h | h
            · exact hzq h
            · exact hzr h
            · exact hzd (h.trans hd_eq.symm)
        have hq4 : memTri t₄ q := by
          by_cases hcq : memTri t₄ q
          · exact hcq
          · exfalso
            have hu₁' : u₁ = p ∨ u₁ = r := by
              rcases hS1x u₁ hu₁1 with h | h | h
              · exact Or.inl h
              · exact absurd (memTri_of_eq hu₁4 h) hcq
              · exact Or.inr h
            have hu₂' : u₂ = p ∨ u₂ = r := by
              rcases hS1x u₂ hu₂1 with h | h | h
              · exact Or.inl h
              · exact absurd (memTri_of_eq hu₂4 h) hcq
              · exact Or.inr h
            have hr4 : memTri t₄ r := by
              rcases eq_of_two_mem_pair hu12 hu₁' hu₂' with ⟨-, h2'⟩ | ⟨h1', -⟩
              · exact memTri_of_eq hu₂4 h2'
              · exact memTri_of_eq hu₁4 h1'
            have hv₁' : v₁ = p ∨ v₁ = d := by
              rcases hS2x v₁ hv₁2 with h | h | h
              · exact Or.inl h
              · exact absurd (memTri_of_eq hv₁4 h) hcq
              · exact Or.inr h
            have hv₂' : v₂ = p ∨ v₂ = d := by
              rcases hS2x v₂ hv₂2 with h | h | h
              · exact Or.inl h
              · exact absurd (memTri_of_eq hv₂4 h) hcq
              · exact Or.inr h
            have hd4 : memTri t₄ d := by
              rcases eq_of_two_mem_pair hv12 hv₁' hv₂' with ⟨-, h2'⟩ | ⟨h1', -⟩
              · exact memTri_of_eq hv₂4 h2'
              · exact memTri_of_eq hv₁4 h1'
            generalize hw'_def : thirdOf p r (t₄.1, t₄.2.1, t₄.2.2) = w'
            obtain ⟨⟨hw'p, hw'r⟩, hw'c, ha4, hb4, hc4⟩ := thirdOf_spec hp_r h4 hp4 hr4
            rw [hw'_def] at hw'p hw'r hw'c ha4 hb4 hc4
            have hd_eq : d = w' := by
              rcases mem_of_memTri_subset ha4 hb4 hc4 hd4 with h | h | h
              · exact absurd h.symm hp_d
              · exact absurd h.symm hrd
              · exact h
            have hz_in : z = p ∨ z = r ∨ z = w' :=
              mem_of_memTri_subset ha4 hb4 hc4 hz
            rcases hz_in with h | h | h
            · exact hzp h
            · exact hzr h
            · exact hzd (h.trans hd_eq.symm)
        -- Now `{p, q, z} = t₄`'s components, but `t₄` shares only `e` with `t₃`.
        generalize hw''_def : thirdOf p q (t₄.1, t₄.2.1, t₄.2.2) = w''
        obtain ⟨⟨hw''p, hw''q⟩, hw''c, ha4, hb4, hc4⟩ := thirdOf_spec hpq h4 hp4 hq4
        rw [hw''_def] at hw''p hw''q hw''c ha4 hb4 hc4
        have hz_eq : z = w'' := by
          rcases mem_of_memTri_subset ha4 hb4 hc4 hz with h | h | h
          · exact absurd h hzp
          · exact absurd h hzq
          · exact h
        have hw1e : w₁ = e := by
          rcases mem_of_memTri_subset ha4 hb4 hc4 hw₁4 with h | h | h
          · rcases hS3x w₁ hw₁3 with h2 | h2 | h2
            · exact absurd (h.symm.trans h2) (Ne.symm hrp)
            · exact absurd (h.symm.trans h2) (Ne.symm hdp)
            · exact h2
          · rcases hS3x w₁ hw₁3 with h2 | h2 | h2
            · exact absurd (h.symm.trans h2) (Ne.symm hrq)
            · exact absurd (h.symm.trans h2) (Ne.symm hdq)
            · exact h2
          · rcases hS3x w₁ hw₁3 with h2 | h2 | h2
            · exact absurd ((h.trans hz_eq.symm).symm.trans h2) hzr
            · exact absurd ((h.trans hz_eq.symm).symm.trans h2) hzd
            · exact absurd ((h.trans hz_eq.symm).symm.trans h2) hze
        have hw2e : w₂ = e := by
          rcases mem_of_memTri_subset ha4 hb4 hc4 hw₂4 with h | h | h
          · rcases hS3x w₂ hw₂3 with h2 | h2 | h2
            · exact absurd (h.symm.trans h2) (Ne.symm hrp)
            · exact absurd (h.symm.trans h2) (Ne.symm hdp)
            · exact h2
          · rcases hS3x w₂ hw₂3 with h2 | h2 | h2
            · exact absurd (h.symm.trans h2) (Ne.symm hrq)
            · exact absurd (h.symm.trans h2) (Ne.symm hdq)
            · exact h2
          · rcases hS3x w₂ hw₂3 with h2 | h2 | h2
            · exact absurd ((h.trans hz_eq.symm).symm.trans h2) hzr
            · exact absurd ((h.trans hz_eq.symm).symm.trans h2) hzd
            · exact absurd ((h.trans hz_eq.symm).symm.trans h2) hze
        exact hw12 (hw1e.trans hw2e.symm)
    exact ⟨hsub t₄.1 (Or.inl rfl), hsub t₄.2.1 (Or.inr (Or.inl rfl)),
      hsub t₄.2.2 (Or.inr (Or.inr rfl))⟩

/-! ## Case B: all triangles inside a K₄ -/

theorem crossCount_sym (G : Gph n) (P Q : List (Fin n)) :
    crossCount G.adj P Q = ssum Q (fun j => degIn G.adj P j) := by
  show ssum P (fun i => ssum Q (fun j => (G.adj i j).toNat)) =
    ssum Q (fun j => ssum P (fun i => (G.adj j i).toNat))
  rw [ssum_swap]
  apply ssum_congr
  intro i _
  apply ssum_congr
  intro j _
  rw [G.sym i j]

/-- Edge count is at most `m choose 2` on a nodup list. -/
theorem ecountIn_le_choose_two (G : Gph n) : ∀ l : List (Fin n), l.Nodup →
    ecountIn G.adj l ≤ l.length * (l.length - 1) / 2 := by
  intro l
  induction l with
  | nil => intro _; simp [ecountIn, ssum]
  | cons a l ih =>
    intro nd
    have ndl : l.Nodup := (List.nodup_cons.mp nd).2
    have ha : a ∉ l := (List.nodup_cons.mp nd).1
    have hsplit := ecountIn_eq_filter_add_deg G nd (List.mem_cons_self ..)
    have hdel : delVertex (a :: l) a = l := by
      show (a :: l).filter (fun v => !(v == a)) = l
      have h1 : (a :: l).filter (fun v => !(v == a)) = l.filter (fun v => !(v == a)) := by
        simp [List.filter, beq_self_eq_true]
      rw [h1, List.filter_eq_self]
      intro x hx
      have hne : x ≠ a := fun h => ha (h ▸ hx)
      simp [hne]
    have hdeg : degIn G.adj (a :: l) a ≤ l.length := by
      show ssum (a :: l) (fun j => (G.adj a j).toNat) ≤ l.length
      rw [ssum_cons, G.irr a]
      have h1 : ssum l (fun j => (G.adj a j).toNat) ≤ ssum l (fun _ => 1) :=
        ssum_le (fun j _ => Bool.toNat_le_one _)
      rw [ssum_const, Nat.one_mul] at h1
      show (0 : Nat) + ssum l (fun j => (G.adj a j).toNat) ≤ l.length
      omega
    have hec := ih ndl
    rw [hsplit, hdel, List.length_cons]
    have hm1 : (l.length + 1) * (l.length + 1 - 1) = l.length * l.length + l.length := by
      rw [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
    have hm2 : l.length * (l.length - 1) = l.length * l.length - l.length := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hL : l.length ≤ l.length * l.length := Nat.le_mul_self _
    rw [hm1]
    rw [hm2] at hec
    omega

/-- Case B algebra: `6 + (n-4) + ⌊(n-4)²/4⌋ ≤ ⌊n²/4⌋ + 1` for `n ≥ 5`. -/
theorem caseB_algebra (n : Nat) (h5 : 5 ≤ n) :
    6 + (n - 4) + (n - 4) * (n - 4) / 4 ≤ n * n / 4 + 1 := by
  have hb : 4 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
  have hm : (n - 4) * (n - 4) = n * n + 16 - 8 * n := by
    rw [Nat.mul_sub_right_distrib, Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    omega
  have ha : 8 * n ≤ n * n + 16 := by
    by_cases h8 : 8 ≤ n
    · have h1 : 8 * n ≤ n * n := Nat.mul_le_mul_right n h8
      omega
    · have h567 : n = 5 ∨ n = 6 ∨ n = 7 := by omega
      rcases h567 with h | h | h <;> subst h <;> decide
  omega

/-- Membership predicate of a four-element set. -/
def mem4 (p q r s : Fin n) (x : Fin n) : Bool :=
  (x == p) || (x == q) || (x == r) || (x == s)

/-- A nodup list has exactly `4` elements of `{p,q,r,s}` (all distinct, all in). -/
theorem ssum_mem4 {n : Nat} (l : List (Fin n)) (nd : l.Nodup) {p q r s : Fin n}
    (hp : p ∈ l) (hq : q ∈ l) (hr : r ∈ l) (hs : s ∈ l)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    ssum l (fun x => (mem4 p q r s x).toNat) = 4 := by
  have h1 := ssum_filter_add (fun v => v == p) l (fun x => (mem4 p q r s x).toNat)
  rw [ssum_filter_eq_single nd hp] at h1
  have hfp : (l.filter fun v => !(v == p)).Nodup := nd.filter _
  have hq' : q ∈ l.filter (fun v => !(v == p)) := by
    rw [List.mem_filter]
    exact ⟨hq, by simp [Bool.not_eq_true, beq_iff_eq, Ne.symm hpq]⟩
  have h2 := ssum_filter_add (fun v => v == q) (l.filter (fun v => !(v == p)))
    (fun x => (mem4 p q r s x).toNat)
  rw [ssum_filter_eq_single hfp hq'] at h2
  have hfq : ((l.filter fun v => !(v == p)).filter fun v => !(v == q)).Nodup := hfp.filter _
  have hr' : r ∈ (l.filter fun v => !(v == p)).filter (fun v => !(v == q)) := by
    rw [List.mem_filter, List.mem_filter]
    exact ⟨⟨hr, by simp [Bool.not_eq_true, beq_iff_eq, Ne.symm hpr]⟩,
      by simp [Bool.not_eq_true, beq_iff_eq, Ne.symm hqr]⟩
  have h3 := ssum_filter_add (fun v => v == r)
    ((l.filter fun v => !(v == p)).filter fun v => !(v == q)) (fun x => (mem4 p q r s x).toNat)
  rw [ssum_filter_eq_single hfq hr'] at h3
  have hfr : (((l.filter fun v => !(v == p)).filter fun v => !(v == q)).filter
      fun v => !(v == r)).Nodup := hfq.filter _
  have hs' : s ∈ ((l.filter fun v => !(v == p)).filter fun v => !(v == q)).filter
      (fun v => !(v == r)) := by
    rw [List.mem_filter, List.mem_filter, List.mem_filter]
    exact ⟨⟨⟨hs, by simp [Bool.not_eq_true, beq_iff_eq, Ne.symm hps]⟩,
      by simp [Bool.not_eq_true, beq_iff_eq, Ne.symm hqs]⟩,
      by simp [Bool.not_eq_true, beq_iff_eq, Ne.symm hrs]⟩
  have h4 := ssum_filter_add (fun v => v == s)
    (((l.filter fun v => !(v == p)).filter fun v => !(v == q)).filter fun v => !(v == r))
    (fun x => (mem4 p q r s x).toNat)
  rw [ssum_filter_eq_single hfr hs'] at h4
  have hrest : ssum ((((l.filter fun v => !(v == p)).filter fun v => !(v == q)).filter
        fun v => !(v == r)).filter fun v => !(v == s)) (fun x => (mem4 p q r s x).toNat) = 0 := by
    apply ssum_eq_zero
    intro x hx
    rw [List.mem_filter, List.mem_filter, List.mem_filter, List.mem_filter] at hx
    obtain ⟨hx, hsx⟩ := hx
    obtain ⟨hx, hrx⟩ := hx
    obtain ⟨hx, hqx⟩ := hx
    obtain ⟨-, hpx⟩ := hx
    have hnp : x ≠ p := by
      intro h; rw [h] at hpx; simp at hpx
    have hnq : x ≠ q := by
      intro h; rw [h] at hqx; simp at hqx
    have hnr : x ≠ r := by
      intro h; rw [h] at hrx; simp at hrx
    have hns : x ≠ s := by
      intro h; rw [h] at hsx; simp at hsx
    have hm : mem4 p q r s x = false := by
      apply bool_eq_false_of_ne_true
      intro hctrue
      simp only [mem4, Bool.or_eq_true, beq_iff_eq] at hctrue
      rcases hctrue with ((h | h) | h) | h
      · exact hnp h
      · exact hnq h
      · exact hnr h
      · exact hns h
    rw [hm]
    rfl
  have hvp : (mem4 p q r s p).toNat = 1 := by simp [mem4]
  have hvq : (mem4 p q r s q).toNat = 1 := by simp [mem4]
  have hvr : (mem4 p q r s r).toNat = 1 := by simp [mem4]
  have hvs : (mem4 p q r s s).toNat = 1 := by simp [mem4]
  omega

/-- **Case B bound**: if every triangle lives inside the K₄ `{p,q,r,s}`, then
`e ≤ ⌊n²/4⌋ + 1`. -/
theorem caseB_bound {n : Nat} (G : Gph n) (h5 : 5 ≤ n)
    {p q r s : Fin n} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s)
    (hApq : G.adj p q = true) (hApr : G.adj p r = true) (hAps : G.adj p s = true)
    (hAqr : G.adj q r = true) (hAqs : G.adj q s = true) (hArs : G.adj r s = true)
    (hsub : ∀ t : Fin n × Fin n × Fin n, triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
      (t.1 = p ∨ t.1 = q ∨ t.1 = r ∨ t.1 = s) ∧
      (t.2.1 = p ∨ t.2.1 = q ∨ t.2.1 = r ∨ t.2.1 = s) ∧
      (t.2.2 = p ∨ t.2.2 = q ∨ t.2.2 = r ∨ t.2.2 = s)) :
    ecountIn G.adj (List.finRange n) ≤ n * n / 4 + 1 := by
  have hnd : (List.finRange n).Nodup := List.nodup_finRange n
  have hnd4 : ((List.finRange n).filter (mem4 p q r s)).Nodup := hnd.filter _
  have hndY : ((List.finRange n).filter (fun x => !mem4 p q r s x)).Nodup := hnd.filter _
  have hlen4 : ((List.finRange n).filter (mem4 p q r s)).length = 4 := by
    rw [filter_length_eq]
    exact ssum_mem4 _ hnd (List.mem_finRange p) (List.mem_finRange q)
      (List.mem_finRange r) (List.mem_finRange s) hpq hpr hps hqr hqs hrs
  have hlenY : ((List.finRange n).filter (fun x => !mem4 p q r s x)).length = n - 4 := by
    have h := filter_length_add (mem4 p q r s) (List.finRange n)
    rw [hlen4, List.length_finRange] at h
    omega
  -- B2: every vertex outside the K₄ has at most one neighbor inside it.
  have hB2 : ∀ y ∈ (List.finRange n).filter (fun x => !mem4 p q r s x),
      degIn G.adj ((List.finRange n).filter (mem4 p q r s)) y ≤ 1 := by
    intro y hy
    by_cases hdeg : degIn G.adj ((List.finRange n).filter (mem4 p q r s)) y ≤ 1
    · exact hdeg
    · exfalso
      have h2' : 2 ≤ degIn G.adj ((List.finRange n).filter (mem4 p q r s)) y := by omega
      obtain ⟨x₁, hx₁, x₂, hx₂, hne12, h1x, h2x⟩ :=
        ssum_two_witness hnd4 (fun x _ => Bool.toNat_le_one _) h2'
      have hA1 : G.adj y x₁ = true := bool_true_of_toNat_pos h1x
      have hA2 : G.adj y x₂ = true := bool_true_of_toNat_pos h2x
      have hx₁4 : ((x₁ = p ∨ x₁ = q) ∨ x₁ = r) ∨ x₁ = s := by
        have hm := (List.mem_filter.mp hx₁).2
        simp only [mem4, Bool.or_eq_true, beq_iff_eq] at hm
        exact hm
      have hx₂4 : ((x₂ = p ∨ x₂ = q) ∨ x₂ = r) ∨ x₂ = s := by
        have hm := (List.mem_filter.mp hx₂).2
        simp only [mem4, Bool.or_eq_true, beq_iff_eq] at hm
        exact hm
      have hym : ((y ≠ p ∧ y ≠ q) ∧ y ≠ r) ∧ y ≠ s := by
        have hm := (List.mem_filter.mp hy).2
        have hm' : mem4 p q r s y = false := by
          cases hb : mem4 p q r s y
          · rfl
          · rw [hb] at hm; simp at hm
        by_cases h1 : y = p
        · rw [h1] at hm'; simp [mem4] at hm'
        by_cases h2 : y = q
        · rw [h2] at hm'; simp [mem4] at hm'
        by_cases h3 : y = r
        · rw [h3] at hm'; simp [mem4] at hm'
        by_cases h4 : y = s
        · rw [h4] at hm'; simp [mem4] at hm'
        exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      have hyx1 : y ≠ x₁ := by
        intro h
        rcases hx₁4 with ((h1 | h1) | h1) | h1
        · exact hym.1.1.1 (h.trans h1)
        · exact hym.1.1.2 (h.trans h1)
        · exact hym.1.2 (h.trans h1)
        · exact hym.2 (h.trans h1)
      have hyx2 : y ≠ x₂ := by
        intro h
        rcases hx₂4 with ((h1 | h1) | h1) | h1
        · exact hym.1.1.1 (h.trans h1)
        · exact hym.1.1.2 (h.trans h1)
        · exact hym.1.2 (h.trans h1)
        · exact hym.2 (h.trans h1)
      have hadj : G.adj x₁ x₂ = true := by
        rcases hx₁4 with ((h | h) | h) | h <;> rcases hx₂4 with ((h2 | h2) | h2) | h2 <;>
          subst h <;> subst h2 <;>
          first
            | exact absurd rfl hne12
            | assumption
            | (rw [G.sym]; assumption)
      obtain ⟨a, b, c, hT, hTy, -, -⟩ := triTerm_one_of_triangle hyx1 hne12 hyx2 hA1 hadj hA2
      obtain ⟨ha, hb, hc⟩ := hsub (a, b, c) hT
      have hy4 : y = p ∨ y = q ∨ y = r ∨ y = s := by
        rcases hTy with h | h | h
        · rw [h]; exact ha
        · rw [h]; exact hb
        · rw [h]; exact hc
      rcases hy4 with h | h | h | h
      · exact hym.1.1.1 h
      · exact hym.1.1.2 h
      · exact hym.1.2 h
      · exact hym.2 h
  -- B3: the outside has no triangle.
  have htriY : ∀ x y z : Fin n,
      x ∈ (List.finRange n).filter (fun x => !mem4 p q r s x) →
      y ∈ (List.finRange n).filter (fun x => !mem4 p q r s x) →
      z ∈ (List.finRange n).filter (fun x => !mem4 p q r s x) →
      x ≠ y → y ≠ z → x ≠ z →
      ¬(G.adj x y = true ∧ G.adj y z = true ∧ G.adj x z = true) := by
    intro x y z hx hy hz hxy hyz hxz ⟨hAxy, hAyz, hAxz⟩
    obtain ⟨a, b, c, hT, hTx, -, -⟩ := triTerm_one_of_triangle hxy hyz hxz hAxy hAyz hAxz
    obtain ⟨ha, hb, hc⟩ := hsub (a, b, c) hT
    have hx4 : x = p ∨ x = q ∨ x = r ∨ x = s := by
      rcases hTx with h | h | h
      · rw [h]; exact ha
      · rw [h]; exact hb
      · rw [h]; exact hc
    have hxm0 := (List.mem_filter.mp hx).2
    have hxm : mem4 p q r s x = false := by
      cases hb : mem4 p q r s x
      · rfl
      · rw [hb] at hxm0; simp at hxm0
    rcases hx4 with h | h | h | h <;> rw [h] at hxm <;> simp [mem4] at hxm
  -- assemble
  have hpart := ecountIn_partition G (List.finRange n) (mem4 p q r s)
  have hec4 : ecountIn G.adj ((List.finRange n).filter (mem4 p q r s)) ≤ 6 := by
    have hh := ecountIn_le_choose_two G _ hnd4
    rw [hlen4] at hh
    omega
  have hecY : ecountIn G.adj ((List.finRange n).filter (fun x => !mem4 p q r s x)) ≤
      ((List.finRange n).filter (fun x => !mem4 p q r s x)).length *
        ((List.finRange n).filter (fun x => !mem4 p q r s x)).length / 4 :=
    mantel_bound G hndY htriY
  have hcross : crossCount G.adj ((List.finRange n).filter (mem4 p q r s))
      ((List.finRange n).filter (fun x => !mem4 p q r s x)) ≤
      ((List.finRange n).filter (fun x => !mem4 p q r s x)).length := by
    rw [crossCount_sym]
    have h1 : ssum ((List.finRange n).filter (fun x => !mem4 p q r s x))
        (fun j => degIn G.adj ((List.finRange n).filter (mem4 p q r s)) j) ≤
        ssum ((List.finRange n).filter (fun x => !mem4 p q r s x)) (fun _ => 1) :=
      ssum_le (fun j hj => hB2 j hj)
    rw [ssum_const, Nat.one_mul] at h1
    exact h1
  rw [hlenY] at hecY hcross
  have halg := caseB_algebra n h5
  omega

/-! ## Case A infrastructure -/

/-- Membership predicate of a two-element set. -/
def mem2 (u v : Fin n) (x : Fin n) : Bool := (x == u) || (x == v)

/-- Sublists of a list (self-contained replacement; core has no `List.sublists`). -/
def sublists (l : List α) : List (List α) :=
  match l with
  | [] => [[]]
  | a :: l => sublists l ++ (sublists l).map (a :: ·)

theorem sublist_of_mem_sublists {l₁ l₂ : List α} (h : l₁ ∈ sublists l₂) : l₁.Sublist l₂ := by
  induction l₂ generalizing l₁ with
  | nil =>
    have h2 : sublists ([] : List α) = [[]] := rfl
    rw [h2, List.mem_singleton] at h
    rw [h]
    exact List.Sublist.slnil
  | cons a l ih =>
    have h' : l₁ ∈ sublists l ++ (sublists l).map (a :: ·) := h
    rw [List.mem_append] at h'
    cases h' with
    | inl h => exact List.Sublist.cons a (ih h)
    | inr h =>
      rw [List.mem_map] at h
      obtain ⟨b, hb, rfl⟩ := h
      exact List.Sublist.cons_cons a (ih hb)

theorem mem_sublists_of_sublist {l₁ l₂ : List α} (h : l₁.Sublist l₂) : l₁ ∈ sublists l₂ := by
  induction h with
  | slnil => exact List.mem_cons_self ..
  | cons a s ih =>
    exact List.mem_append.mpr (Or.inl ih)
  | cons_cons a s ih =>
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, ih, rfl⟩))

/-- A nodup list has exactly `2` elements of `{u,v}` (`u ≠ v`, both in). -/
theorem ssum_mem2 {n : Nat} (l : List (Fin n)) (nd : l.Nodup) {u v : Fin n}
    (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) :
    ssum l (fun x => (mem2 u v x).toNat) = 2 := by
  have h1 := ssum_filter_add (fun x => x == u) l (fun x => (mem2 u v x).toNat)
  rw [ssum_filter_eq_single nd hu] at h1
  have hfn : (l.filter fun x => !(x == u)).Nodup := nd.filter _
  have hv' : v ∈ l.filter (fun x => !(x == u)) := by
    rw [List.mem_filter]
    exact ⟨hv, by simp [beq_iff_eq, Bool.not_eq_true, Ne.symm huv]⟩
  have h2 := ssum_filter_add (fun x => x == v) (l.filter (fun x => !(x == u)))
    (fun x => (mem2 u v x).toNat)
  rw [ssum_filter_eq_single hfn hv'] at h2
  have hrest : ssum ((l.filter fun x => !(x == u)).filter fun x => !(x == v))
      (fun x => (mem2 u v x).toNat) = 0 := by
    apply ssum_eq_zero
    intro x hx
    rw [List.mem_filter, List.mem_filter] at hx
    obtain ⟨⟨-, hux⟩, hxv⟩ := hx
    have hnu : x ≠ u := by intro h; rw [h] at hux; simp at hux
    have hnv : x ≠ v := by intro h; rw [h] at hxv; simp at hxv
    have hm : mem2 u v x = false := by
      apply bool_eq_false_of_ne_true
      intro hctrue
      simp only [mem2, Bool.or_eq_true, beq_iff_eq] at hctrue
      rcases hctrue with h | h
      · exact hnu h
      · exact hnv h
    rw [hm]
    rfl
  have hvu : (mem2 u v u).toNat = 1 := by simp [mem2]
  have hvv : (mem2 u v v).toNat = 1 := by simp [mem2]
  omega

/-- Degree into the `{u,v}` part is the sum of the two adjacencies. -/
theorem degIn_mem2 {n : Nat} (G : Gph n) {l : List (Fin n)} (nd : l.Nodup) {u v : Fin n}
    (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) (x : Fin n) :
    degIn G.adj (l.filter (mem2 u v)) x = (G.adj x u).toNat + (G.adj x v).toNat := by
  have hu' : u ∈ l.filter (mem2 u v) := by
    rw [List.mem_filter]
    exact ⟨hu, by simp [mem2]⟩
  have h1 := ssum_filter_add (fun w => w == u) (l.filter (mem2 u v)) (fun j => (G.adj x j).toNat)
  rw [ssum_filter_eq_single (nd.filter _) hu'] at h1
  have hv' : v ∈ (l.filter (mem2 u v)).filter (fun w => !(w == u)) := by
    rw [List.mem_filter, List.mem_filter]
    exact ⟨⟨hv, by simp [mem2]⟩, by simp [beq_iff_eq, Bool.not_eq_true, Ne.symm huv]⟩
  have h2 := ssum_filter_add (fun w => w == v) ((l.filter (mem2 u v)).filter (fun w => !(w == u)))
    (fun j => (G.adj x j).toNat)
  rw [ssum_filter_eq_single ((nd.filter _).filter _) hv'] at h2
  have hrest : ssum (((l.filter (mem2 u v)).filter (fun w => !(w == u))).filter (fun w => !(w == v)))
      (fun j => (G.adj x j).toNat) = 0 := by
    have hem : (((l.filter (mem2 u v)).filter (fun w => !(w == u))).filter (fun w => !(w == v))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hy
      obtain ⟨h1, hyu⟩ := List.mem_filter.mp hy
      obtain ⟨-, hym⟩ := List.mem_filter.mp h1
      have hnu : y ≠ u := by
        intro h; rw [h] at hyu; simp at hyu
      simp only [mem2, Bool.or_eq_true, beq_iff_eq] at hym
      have hyv : y = v := by
        rcases hym with h | h
        · exact absurd h hnu
        · exact h
      rw [hyv]
      simp
    rw [hem, ssum_nil]
  have hdx : degIn G.adj (l.filter (mem2 u v)) x =
      ssum (l.filter (mem2 u v)) (fun j => (G.adj x j).toNat) := rfl
  rw [hdx]
  omega

/-- `(a+b)²` expansion. -/
theorem sq_add (a b : Nat) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]
  omega

/-- `4ab ≤ (a+b)²`. -/
theorem four_mul_le_sq (a b : Nat) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  by_cases h : a ≤ b
  · obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
    have e1 : a * (a + c) = a * a + a * c := Nat.mul_add ..
    have e2 := sq_add a c
    rw [sq_add, e1]
    omega
  · obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
    have e1 : (b + c) * b = b * b + b * c := by
      rw [Nat.add_mul, Nat.mul_comm c b]
    have e2 := sq_add b c
    rw [sq_add, e1]
    omega

/-- `foldl Nat.max` is at least its starting value. -/
theorem foldl_max_ge (l : List Nat) (b : Nat) : b ≤ l.foldl Nat.max b := by
  induction l generalizing b with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    rw [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left ..) (ih _)

/-- Every list element is below the `foldl Nat.max`. -/
theorem le_foldl_max (l : List Nat) (b : Nat) : ∀ x ∈ l, x ≤ l.foldl Nat.max b := by
  induction l generalizing b with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx
    rw [List.foldl_cons]
    rw [List.mem_cons] at hx
    cases hx with
    | inl h =>
      rw [← h]
      exact Nat.le_trans (Nat.le_max_right ..) (foldl_max_ge l _)
    | inr h => exact ih _ x h

/-- The `foldl Nat.max` value is the start or a list element. -/
theorem foldl_max_mem (l : List Nat) (b : Nat) :
    l.foldl Nat.max b = b ∨ l.foldl Nat.max b ∈ l := by
  induction l generalizing b with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    cases ih (Nat.max b a) with
    | inl h =>
      by_cases hba : b ≤ a
      · have h2 : Nat.max b a = a := Nat.max_eq_right hba
        rw [h, h2]
        exact Or.inr (List.mem_cons_self ..)
      · have h2 : Nat.max b a = b := Nat.max_eq_left (by omega : a ≤ b)
        rw [h, h2]
        exact Or.inl rfl
    | inr h => exact Or.inr (List.mem_cons_of_mem _ h)

/-- Independence predicate as a Bool. -/
def indepB (G : Gph n) (l : List (Fin n)) : Bool :=
  decide (∀ x ∈ l, ∀ y ∈ l, x ≠ y → G.adj x y = false)

/-- Maximal independent sublist of `X₀` exists (via finite enumeration). -/
theorem exists_max_indep (G : Gph n) (X₀ : List (Fin n)) (ndX : X₀.Nodup) :
    ∃ I₀ : List (Fin n), I₀.Sublist X₀ ∧ I₀.Nodup ∧
      (∀ x ∈ I₀, ∀ y ∈ I₀, x ≠ y → G.adj x y = false) ∧
      (∀ J : List (Fin n), J.Sublist X₀ → (∀ x ∈ J, ∀ y ∈ J, x ≠ y → G.adj x y = false) →
        J.length ≤ I₀.length) := by
  have hbound : ∀ J : List (Fin n), J.Sublist X₀ →
      (∀ x ∈ J, ∀ y ∈ J, x ≠ y → G.adj x y = false) →
      J.length ≤ (((sublists X₀).filter (indepB G)).map List.length).foldl Nat.max 0 := by
    intro J hJ hind
    have h1 : J ∈ (sublists X₀).filter (indepB G) := by
      rw [List.mem_filter]
      exact ⟨mem_sublists_of_sublist hJ, decide_eq_true hind⟩
    have h2 : J.length ∈ ((sublists X₀).filter (indepB G)).map List.length :=
      List.mem_map.mpr ⟨J, h1, rfl⟩
    exact le_foldl_max _ _ _ h2
  cases hc : (((sublists X₀).filter (indepB G)).map List.length).foldl Nat.max 0 with
  | zero =>
    refine ⟨[], List.nil_sublist _, List.nodup_nil, fun x hx => by simp at hx, ?_⟩
    intro J hJ hind
    have := hbound J hJ hind
    rw [hc] at this
    exact this
  | succ k =>
    have hmem : k + 1 ∈ ((sublists X₀).filter (indepB G)).map List.length := by
      have hm := foldl_max_mem (((sublists X₀).filter (indepB G)).map List.length) 0
      rw [hc] at hm
      cases hm with
      | inl h => simp at h
      | inr h => exact h
    rw [List.mem_map] at hmem
    obtain ⟨I₀, hI₀, hlen⟩ := hmem
    rw [List.mem_filter] at hI₀
    refine ⟨I₀, sublist_of_mem_sublists hI₀.1,
      List.Nodup.sublist (sublist_of_mem_sublists hI₀.1) ndX, of_decide_eq_true hI₀.2, ?_⟩
    intro J hJ hind
    have := hbound J hJ hind
    rw [hc, ← hlen] at this
    exact this

/-- A nodup list filtered by membership in a sublist returns the sublist. -/
theorem filter_mem_eq_of_sublist [DecidableEq α] {l₁ l₂ : List α} (hs : l₁.Sublist l₂)
    (nd : l₂.Nodup) :
    l₂.filter (fun x => decide (x ∈ l₁)) = l₁ := by
  induction hs with
  | slnil => rfl
  | cons a hs ih =>
    rename_i t₁ t₂
    rw [List.nodup_cons] at nd
    have ha : a ∉ t₁ := fun h => nd.1 (List.Sublist.mem h hs)
    have h1 : (a :: t₂).filter (fun x => decide (x ∈ t₁)) = t₂.filter (fun x => decide (x ∈ t₁)) := by
      simp [List.filter, decide_eq_false ha]
    rw [h1]
    exact ih nd.2
  | cons_cons a hs ih =>
    rename_i t₁ t₂
    rw [List.nodup_cons] at nd
    have h1 : (a :: t₂).filter (fun x => decide (x ∈ a :: t₁)) =
        a :: t₂.filter (fun x => decide (x ∈ a :: t₁)) := by
      simp [List.filter, decide_eq_true (List.mem_cons_self ..)]
    have h2 : t₂.filter (fun x => decide (x ∈ a :: t₁)) = t₂.filter (fun x => decide (x ∈ t₁)) := by
      apply List.filter_congr
      intro x hx
      have hne : x ≠ a := fun h => nd.1 (h ▸ hx)
      by_cases hc : x ∈ t₁
      · have h3 : x ∈ a :: t₁ := List.mem_cons_of_mem _ hc
        rw [decide_eq_true h3, decide_eq_true hc]
      · have h4 : ¬ x ∈ a :: t₁ := by
          intro h
          rw [List.mem_cons] at h
          cases h with
          | inl h => exact hne h
          | inr h => exact hc h
        rw [decide_eq_false h4, decide_eq_false hc]
    rw [h1, h2, ih nd.2]

/-- `d² + 4 ≥ 4d` for naturals. -/
theorem d_sq_ge (d : Nat) : 4 * d ≤ d * d + 4 := by
  by_cases h : d ≤ 2
  · have h012 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases h012 with h | h | h <;> subst h <;> decide
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
    have e1 : (e + 3) * (e + 3) = e * e + 6 * e + 9 := by
      rw [sq_add]
      omega
    rw [e1]
    omega

/-- **Case A algebra**: the bound `B′ ≤ ⌊n²/4⌋ + 1`. -/
theorem caseA_algebra (n t z x₁ : Nat) (ht : n / 2 ≤ t) (ht2 : t ≤ n - 2) (h5 : 5 ≤ n)
    (hxz : x₁ + z = n - 2 - t) :
    1 + 2 * t + x₁ + t * z + z * x₁ + x₁ * x₁ / 4 ≤ n * n / 4 + 1 := by
  have hzt : z ≤ t := by omega
  generalize hd : t - z = d
  have htd : t = z + d := by omega
  have hnd : n = 2 * z + d + x₁ + 2 := by omega
  have hE : 4 * (1 + 2 * t + x₁ + t * z + z * x₁) + x₁ * x₁ + d * d + 2 * (d * x₁)
      = n * n + 4 * d := by
    rw [htd, hnd]
    have l1 : 4 * (1 + 2 * (z + d) + x₁ + (z + d) * z + z * x₁) =
        4 + 8 * z + 8 * d + 4 * x₁ + 4 * (z * z) + 4 * (z * d) + 4 * (z * x₁) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      rw [Nat.add_mul]
      rw [Nat.mul_comm d z]
      rw [Nat.mul_add]
      omega
    have r1 : (2 * z + d + x₁ + 2) * (2 * z + d + x₁ + 2) =
        4 * (z * z) + 4 * (z * d) + 4 * (z * x₁) + 8 * z + d * d + 2 * (d * x₁) +
          4 * d + x₁ * x₁ + 4 * x₁ + 4 := by
      rw [sq_add, sq_add, sq_add (2 * z) d, sq_two_mul, Nat.mul_assoc 2 z d,
        Nat.add_mul (2 * z) d x₁, Nat.mul_assoc 2 z x₁,
        Nat.add_mul (2 * z + d) x₁ 2, Nat.add_mul (2 * z) d 2]
      omega
    rw [l1, r1]
    omega
  have hdiv : 4 * (x₁ * x₁ / 4) ≤ x₁ * x₁ := Nat.mul_div_le ..
  have hdsq := d_sq_ge d
  omega

/-! ## Case A: all triangles through a common edge -/

/-- Cross-count is symmetric for a graph adjacency. -/
theorem crossCount_symm (G : Gph n) (P Q : List (Fin n)) :
    crossCount G.adj P Q = crossCount G.adj Q P := by
  show ssum P (fun i => ssum Q (fun j => (G.adj i j).toNat)) = _
  rw [ssum_swap]
  apply ssum_congr
  intro x _
  apply ssum_congr
  intro y _
  rw [G.sym y x]

/-- The edge count of a list is at most its self cross-count. -/
theorem ecountIn_le_cross_self (G : Gph n) (S : List (Fin n)) :
    ecountIn G.adj S ≤ crossCount G.adj S S := by
  rw [ecountIn_eq_ssum_eTerm]
  show ssum S (fun i => ssum S (fun j => eTerm G.adj i j)) ≤
    ssum S (fun i => ssum S (fun j => (G.adj i j).toNat))
  apply ssum_le
  intro i _
  apply ssum_le
  intro j _
  unfold eTerm
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- Sum over the `{u,v}`-membership filter of a nodup list. -/
theorem ssum_filter_mem2 {n : Nat} (l : List (Fin n)) (nd : l.Nodup) {u v : Fin n}
    (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) (f : Fin n → Nat) :
    ssum (l.filter (mem2 u v)) f = f u + f v := by
  have h1 := ssum_filter_add (fun x => x == u) (l.filter (mem2 u v)) f
  have hcongr1 : (l.filter (mem2 u v)).filter (fun x => x == u) =
      l.filter (fun x => x == u) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    cases h : (x == u) <;> simp [mem2, h]
  rw [hcongr1, ssum_filter_eq_single nd hu] at h1
  have hfn : (l.filter fun x => !(x == u)).Nodup := nd.filter _
  have hv' : v ∈ l.filter (fun x => !(x == u)) := by
    rw [List.mem_filter]
    exact ⟨hv, by simp [beq_iff_eq, Bool.not_eq_true, Ne.symm huv]⟩
  have hcongr2 : (l.filter (mem2 u v)).filter (fun x => !(x == u)) =
      (l.filter (fun x => !(x == u))).filter (fun x => x == v) := by
    rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro x _
    cases h1x : (x == u) <;> simp [mem2, h1x]
  rw [hcongr2, ssum_filter_eq_single hfn hv'] at h1
  omega

/-- `t·a + a·(z−a) ≤ t·z` when `a ≤ t` and `a ≤ z`. -/
theorem az_le_tz {a t z : Nat} (hat : a ≤ t) (haz : a ≤ z) :
    t * a + a * (z - a) ≤ t * z := by
  have e1 : t * z = t * a + t * (z - a) := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' haz]
  have h2 : a * (z - a) ≤ t * (z - a) := Nat.mul_le_mul hat (Nat.le_refl _)
  omega

/-- **Case A bound**: if every triangle contains the edge `uv`, then
`e ≤ ⌊n²/4⌋ + 1`. -/
theorem caseA_bound {n : Nat} (G : Gph n) (h5 : 5 ≤ n)
    (h : n * n / 4 + 2 ≤ ecountIn G.adj (List.finRange n))
    {u v : Fin n} (huv : u ≠ v) (hAuv : G.adj u v = true)
    (hcov : ∀ t : Fin n × Fin n × Fin n, triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
      memTri t u ∧ memTri t v) :
    ecountIn G.adj (List.finRange n) ≤ n * n / 4 + 1 := by
  have hnd : (List.finRange n).Nodup := List.nodup_finRange n
  have memV : ∀ x : Fin n,
      x ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) → x ≠ u ∧ x ≠ v := by
    intro x hx
    have h := (List.mem_filter.mp hx).2
    rw [Bool.and_eq_true] at h
    exact ⟨fun he => by rw [he] at h; simp at h,
      fun he => by rw [he] at h; simp at h⟩
  -- A sorted triangle triple whose components all avoid `{u,v}` contradicts `hcov`.
  have hcov_elim : ∀ a b c : Fin n, triTerm G.adj a b c = 1 →
      (∀ w : Fin n, (w = a ∨ w = b ∨ w = c) → w ≠ u ∧ w ≠ v) → False := by
    intro a b c hT h_avoid
    obtain ⟨huT, -⟩ := hcov (a, b, c) hT
    rcases huT with h | h | h
    · exact (h_avoid a (Or.inl rfl)).1 h
    · exact (h_avoid b (Or.inr (Or.inl rfl))).1 h
    · exact (h_avoid c (Or.inr (Or.inr rfl))).1 h
  -- A1: no triangle inside `V'`.
  have triFreeV : ∀ x y z : Fin n,
      x ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) →
      y ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) →
      z ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) →
      x ≠ y → y ≠ z → x ≠ z →
      ¬(G.adj x y = true ∧ G.adj y z = true ∧ G.adj x z = true) := by
    intro x y z hx hy hz hxy hyz hxz ⟨hAxy, hAyz, hAxz⟩
    obtain ⟨a, b, c, hT, -, -, -, ha, hb, hc⟩ := triTerm_one_of_triangle hxy hyz hxz hAxy hAyz hAxz
    have h_avoid : ∀ w : Fin n, (w = a ∨ w = b ∨ w = c) → w ≠ u ∧ w ≠ v := by
      intro w hw
      rcases hw with h | h | h
      · rw [h]
        rcases ha with h2 | h2 | h2
        · rw [h2]; exact memV x hx
        · rw [h2]; exact memV y hy
        · rw [h2]; exact memV z hz
      · rw [h]
        rcases hb with h2 | h2 | h2
        · rw [h2]; exact memV x hx
        · rw [h2]; exact memV y hy
        · rw [h2]; exact memV z hz
      · rw [h]
        rcases hc with h2 | h2 | h2
        · rw [h2]; exact memV x hx
        · rw [h2]; exact memV y hy
        · rw [h2]; exact memV z hz
    exact hcov_elim a b c hT h_avoid
  -- A2/A3/A5: no triangle `u x y` with `x, y ∈ V'`.
  have noTriU : ∀ x y : Fin n,
      x ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) →
      y ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) →
      x ≠ y → G.adj u x = true → G.adj u y = true → G.adj x y = false := by
    intro x y hx hy hxy hAux hAuy
    apply bool_eq_false_of_ne_true
    intro hAxy
    obtain ⟨hux0, -⟩ := memV x hx
    obtain ⟨huy0, -⟩ := memV y hy
    have hux' : u ≠ x := Ne.symm hux0
    have huy' : u ≠ y := Ne.symm huy0
    obtain ⟨a, b, c, hT, -, -, -, ha, hb, hc⟩ := triTerm_one_of_triangle hux' hxy huy' hAux hAxy hAuy
    have h_avoid : ∀ w : Fin n, (w = a ∨ w = b ∨ w = c) → w ≠ v := by
      intro w hw
      rcases hw with h | h | h
      · rw [h]
        rcases ha with h2 | h2 | h2
        · rw [h2]; exact huv
        · rw [h2]; exact (memV x hx).2
        · rw [h2]; exact (memV y hy).2
      · rw [h]
        rcases hb with h2 | h2 | h2
        · rw [h2]; exact huv
        · rw [h2]; exact (memV x hx).2
        · rw [h2]; exact (memV y hy).2
      · rw [h]
        rcases hc with h2 | h2 | h2
        · rw [h2]; exact huv
        · rw [h2]; exact (memV x hx).2
        · rw [h2]; exact (memV y hy).2
    obtain ⟨-, hvT⟩ := hcov (a, b, c) hT
    rcases hvT with h | h | h
    · exact h_avoid a (Or.inl rfl) h
    · exact h_avoid b (Or.inr (Or.inl rfl)) h
    · exact h_avoid c (Or.inr (Or.inr rfl)) h
  -- Same with the roles of `u` and `v` swapped.
  have noTriV : ∀ x y : Fin n,
      x ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) →
      y ∈ (List.finRange n).filter (fun x => !(x == u) && !(x == v)) →
      x ≠ y → G.adj v x = true → G.adj v y = true → G.adj x y = false := by
    intro x y hx hy hxy hAvx hAvy
    apply bool_eq_false_of_ne_true
    intro hAxy
    obtain ⟨-, hvx0⟩ := memV x hx
    obtain ⟨-, hvy0⟩ := memV y hy
    have hvx' : v ≠ x := Ne.symm hvx0
    have hvy' : v ≠ y := Ne.symm hvy0
    obtain ⟨a, b, c, hT, -, -, -, ha, hb, hc⟩ := triTerm_one_of_triangle hvx' hxy hvy' hAvx hAxy hAvy
    have h_avoid : ∀ w : Fin n, (w = a ∨ w = b ∨ w = c) → w ≠ u := by
      intro w hw
      rcases hw with h | h | h
      · rw [h]
        rcases ha with h2 | h2 | h2
        · rw [h2]; exact Ne.symm huv
        · rw [h2]; exact (memV x hx).1
        · rw [h2]; exact (memV y hy).1
      · rw [h]
        rcases hb with h2 | h2 | h2
        · rw [h2]; exact Ne.symm huv
        · rw [h2]; exact (memV x hx).1
        · rw [h2]; exact (memV y hy).1
      · rw [h]
        rcases hc with h2 | h2 | h2
        · rw [h2]; exact Ne.symm huv
        · rw [h2]; exact (memV x hx).1
        · rw [h2]; exact (memV y hy).1
    obtain ⟨huT, -⟩ := hcov (a, b, c) hT
    rcases huT with h | h | h
    · exact h_avoid a (Or.inl rfl) h
    · exact h_avoid b (Or.inr (Or.inl rfl)) h
    · exact h_avoid c (Or.inr (Or.inr rfl)) h
  -- Lengths.
  have hlenV : ((List.finRange n).filter (fun x => !(x == u) && !(x == v))).length = n - 2 := by
    rw [filter_length_eq]
    have h1 := ssum_filter_add (fun x => x == u) (List.finRange n)
      (fun x => ((!(x == u) && !(x == v)) : Bool).toNat)
    rw [ssum_filter_eq_single hnd (List.mem_finRange u)] at h1
    have hfn : ((List.finRange n).filter fun x => !(x == u)).Nodup := hnd.filter _
    have hv' : v ∈ (List.finRange n).filter (fun x => !(x == u)) := by
      rw [List.mem_filter]
      exact ⟨List.mem_finRange v, by simp [beq_iff_eq, Bool.not_eq_true, Ne.symm huv]⟩
    have h2 := ssum_filter_add (fun x => x == v) ((List.finRange n).filter fun x => !(x == u))
      (fun x => ((!(x == u) && !(x == v)) : Bool).toNat)
    rw [ssum_filter_eq_single hfn hv'] at h2
    have hcongr : ssum (((List.finRange n).filter fun x => !(x == u)).filter fun x => !(x == v))
        (fun x => ((!(x == u) && !(x == v)) : Bool).toNat) =
        ssum (((List.finRange n).filter fun x => !(x == u)).filter fun x => !(x == v))
        (fun _ => 1) := by
      apply ssum_congr
      intro x hx
      obtain ⟨h1x, h2x⟩ := List.mem_filter.mp hx
      have hux := (List.mem_filter.mp h1x).2
      rw [hux, h2x]
      rfl
    have hrest : ssum (((List.finRange n).filter fun x => !(x == u)).filter fun x => !(x == v))
        (fun x => ((!(x == u) && !(x == v)) : Bool).toNat) = n - 2 := by
      rw [hcongr, ssum_const, Nat.one_mul]
      have h3 := length_filter_neq_of_mem hfn hv'
      have h4 := length_filter_neq_of_mem hnd (List.mem_finRange u)
      rw [List.length_finRange] at h4
      omega
    have hfu : ((!(u == u) && !(u == v)) : Bool).toNat = 0 := by simp
    have hfv : ((!(v == u) && !(v == v)) : Bool).toNat = 0 := by simp
    omega
  -- `|W| = commonIn u v`, and Rademacher gives `|W| ≥ ⌊n/2⌋`.
  have htW : (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
      (fun x => G.adj u x && G.adj v x)).length = commonIn G.adj (List.finRange n) u v := by
    have h1 : commonIn G.adj (List.finRange n) u v =
        ssum ((List.finRange n).filter (fun x => !(x == u) && !(x == v)))
          (fun j => (G.adj u j && G.adj v j).toNat) := by
      show ssum (List.finRange n) (fun j => (G.adj u j && G.adj v j).toNat) = _
      apply ssum_filter_of_vanish
      intro x _ hpx
      by_cases hu' : x = u
      · rw [hu', G.irr u]
        simp
      · by_cases hv' : x = v
        · rw [hv', G.irr v]
          simp
        · exfalso
          have h2 : (x == u) = false := beq_eq_false_iff_ne.mpr hu'
          have h3 : (x == v) = false := beq_eq_false_iff_ne.mpr hv'
          have h4 : (!(x == u) && !(x == v)) = true := by rw [h2, h3]; rfl
          rw [h4] at hpx
          simp at hpx
    rw [h1, filter_length_eq]
  have ht : n / 2 ≤ (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
      (fun x => G.adj u x && G.adj v x)).length := by
    have h1 : n * n / 4 + 1 ≤ ecountIn G.adj (List.finRange n) := by omega
    have h2 := rademacher_list n n G (List.finRange n) hnd List.length_finRange h1
    have h3 := tcountIn_le_commonIn G hnd huv (fun t _ ht' => hcov t ht')
    rw [← htW] at h3
    omega
  have ht2 : (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
      (fun x => G.adj u x && G.adj v x)).length ≤ n - 2 := by
    have h1 := List.Sublist.length_le (List.filter_sublist
      (p := fun x => G.adj u x && G.adj v x) (l := (List.finRange n).filter
        (fun x => !(x == u) && !(x == v))))
    rw [hlenV] at h1
    exact h1
  have hlenX : (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
      (fun x => !(G.adj u x && G.adj v x))).length =
      n - 2 - (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => G.adj u x && G.adj v x)).length := by
    have h1 := filter_length_add (fun x => G.adj u x && G.adj v x)
      ((List.finRange n).filter (fun x => !(x == u) && !(x == v)))
    rw [hlenV] at h1
    omega
  -- The `Aₓ`/`Bₓ` vs `X₁` length identity (A4).
  have hX1A : ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (fun x => G.adj u x || G.adj v x)).filter
        (G.adj u) =
      (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (G.adj u) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    cases G.adj u x <;> simp
  have hX1B : ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (fun x => G.adj u x || G.adj v x)).filter
        (fun x => !(G.adj u x)) =
      (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (G.adj v) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x hx
    have hX2 : (!(G.adj u x && G.adj v x)) = true := (List.mem_filter.mp hx).2
    cases ha : G.adj u x with
    | false => cases hb : G.adj v x <;> simp [ha, hb]
    | true =>
      cases hb : G.adj v x with
      | false => simp [ha, hb]
      | true => rw [ha, hb] at hX2; simp at hX2
  have hAB : ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (G.adj u)).length +
      ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (G.adj v)).length =
      ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (fun x => G.adj u x || G.adj v x)).length := by
    have h := filter_length_add (G.adj u)
      ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (fun x => G.adj u x || G.adj v x))
    rw [hX1A, hX1B] at h
    exact h
  have hx1z : ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (fun x => G.adj u x || G.adj v x)).length +
      ((((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).filter (fun x => !(G.adj u x || G.adj v x))).length =
      (((List.finRange n).filter (fun x => !(x == u) && !(x == v))).filter
        (fun x => !(G.adj u x && G.adj v x))).length :=
    filter_length_add (fun x => G.adj u x || G.adj v x) _
  -- The edge count splits off the `{u,v}` part.
  have hpart1 := ecountIn_partition G (List.finRange n) (mem2 u v)
  have hQ : (List.finRange n).filter (fun v' => !mem2 u v v') =
      (List.finRange n).filter (fun x => !(x == u) && !(x == v)) := by
    apply List.filter_congr
    intro x _
    simp [mem2, Bool.not_or]
  rw [hQ] at hpart1
  have heP2 : ecountIn G.adj ((List.finRange n).filter (mem2 u v)) = 1 := by
    apply ecountIn_eq_one_of_pair G (hnd.filter _) _ (u := u) (v := v)
        (by rw [List.mem_filter]; exact ⟨List.mem_finRange u, by simp [mem2]⟩)
        (by rw [List.mem_filter]; exact ⟨List.mem_finRange v, by simp [mem2]⟩) huv hAuv
    rw [filter_length_eq]
    exact ssum_mem2 _ hnd (List.mem_finRange u) (List.mem_finRange v) huv
  -- Abbreviations for the vertex parts (via `generalize` + folding).
  generalize hl' : (List.finRange n).filter (fun x => !(x == u) && !(x == v)) = l'
  rw [hl'] at hlenV ht ht2 hlenX hX1A hX1B hAB hx1z hpart1 hQ triFreeV noTriU noTriV memV
  generalize hWd : l'.filter (fun x => G.adj u x && G.adj v x) = W
  rw [hWd] at ht ht2 hlenX
  generalize hXd : l'.filter (fun x => !(G.adj u x && G.adj v x)) = X
  rw [hXd] at hlenX hX1A hX1B hAB hx1z
  generalize hX1d : X.filter (fun x => G.adj u x || G.adj v x) = X₁
  rw [hX1d] at hX1A hX1B hAB hx1z
  generalize hX0d : X.filter (fun x => !(G.adj u x || G.adj v x)) = X₀
  rw [hX0d] at hx1z
  generalize htd : W.length = t
  rw [htd] at ht ht2 hlenX
  generalize hx1d : X₁.length = x₁
  rw [hx1d] at hAB hx1z
  generalize hzd : X₀.length = z
  rw [hzd] at hx1z
  have hsubW : W.Sublist l' := by rw [← hWd]; exact List.filter_sublist
  have hsubX : X.Sublist l' := by rw [← hXd]; exact List.filter_sublist
  have hsubX1l : X₁.Sublist l' := by
    rw [← hX1d, ← hXd]
    exact List.filter_sublist.trans List.filter_sublist
  have hsubX0l : X₀.Sublist l' := by
    rw [← hX0d, ← hXd]
    exact List.filter_sublist.trans List.filter_sublist
  have hndX1 : X₁.Nodup := by
    rw [← hX1d, ← hXd, ← hl']
    exact ((hnd.filter _).filter _).filter _
  have hndX0 : X₀.Nodup := by
    rw [← hX0d, ← hXd, ← hl']
    exact ((hnd.filter _).filter _).filter _
  -- Membership unfolds.
  have memW : ∀ y : Fin n, y ∈ W → y ∈ l' ∧ G.adj u y = true ∧ G.adj v y = true := by
    intro y hy
    rw [← hWd] at hy
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hy
    exact ⟨h1, (Bool.and_eq_true_iff.mp h2).1, (Bool.and_eq_true_iff.mp h2).2⟩
  have memX : ∀ y : Fin n, y ∈ X → y ∈ l' ∧ (G.adj u y && G.adj v y) = false := by
    intro y hy
    rw [← hXd] at hy
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hy
    refine ⟨h1, ?_⟩
    cases hb : (G.adj u y && G.adj v y) with
    | false => rfl
    | true => rw [hb] at h2; simp at h2
  have memX1 : ∀ y : Fin n, y ∈ X₁ → y ∈ X ∧ (G.adj u y || G.adj v y) = true := by
    intro y hy
    rw [← hX1d] at hy
    exact List.mem_filter.mp hy
  have memX0 : ∀ y : Fin n, y ∈ X₀ → y ∈ X ∧ (G.adj u y || G.adj v y) = false := by
    intro y hy
    rw [← hX0d] at hy
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hy
    refine ⟨h1, ?_⟩
    cases hb : (G.adj u y || G.adj v y) with
    | false => rfl
    | true => rw [hb] at h2; simp at h2
  -- A7: no edges between `W` and `X₁` (a `uwx`/`vwx` triangle would avoid `{u,v}`).
  have hE3 : crossCount G.adj W X₁ = 0 := by
    apply crossCount_eq_zero
    intro i hi j hj
    have hil := (memW i hi).1
    have hui := (memW i hi).2.1
    have hvi := (memW i hi).2.2
    have hjl := List.Sublist.mem (memX1 j hj).1 hsubX
    have hor := Bool.or_eq_true_iff.mp (memX1 j hj).2
    have hij : i ≠ j := by
      intro heq
      subst heq
      have h1 := (Bool.and_eq_true_iff.mpr ⟨hui, hvi⟩)
      have h2 := (memX i (memX1 i hj).1).2
      rw [h1] at h2
      simp at h2
    cases hor with
    | inl huj => exact noTriU i j hil hjl hij hui huj
    | inr hvj => exact noTriV i j hil hjl hij hvi hvj
  -- A2: `W` is independent.
  have heW : ecountIn G.adj W = 0 := by
    apply ecountIn_eq_zero_of_indep G
    intro x y hx hy hxy
    exact noTriU x y (memW x hx).1 (memW y hy).1 hxy
      (memW x hx).2.1 (memW y hy).2.1
  -- Cross from `{u,v}` to `V'` equals `2t + x₁`.
  have hfu : ssum l' (fun j => (G.adj u j).toNat) = t + (X.filter (G.adj u)).length := by
    have h1 : ssum l' (fun j => (G.adj u j).toNat) =
        ssum W (fun j => (G.adj u j).toNat) + ssum X (fun j => (G.adj u j).toNat) := by
      rw [← hWd, ← hXd]
      exact ssum_filter_add _ _ _
    have hW1 : ssum W (fun j => (G.adj u j).toNat) = t := by
      have hc : ssum W (fun j => (G.adj u j).toNat) = ssum W (fun _ => 1) := by
        apply ssum_congr
        intro y hy
        rw [(memW y hy).2.1]
        rfl
      rw [hc, ssum_const, Nat.one_mul]
      exact htd
    have hX0z : ssum X₀ (fun j => (G.adj u j).toNat) = 0 := by
      apply ssum_eq_zero
      intro y hy
      have hy2 := (memX0 y hy).2
      have hu' : G.adj u y = false := by
        by_cases hA : G.adj u y = true
        · rw [hA] at hy2; simp at hy2
        · exact bool_eq_false_of_ne_true hA
      simp [hu']
    have h2 : ssum X (fun j => (G.adj u j).toNat) =
        ssum X₁ (fun j => (G.adj u j).toNat) + ssum X₀ (fun j => (G.adj u j).toNat) := by
      rw [← hX1d, ← hX0d]
      exact ssum_filter_add _ _ _
    have hX1s : ssum X₁ (fun j => (G.adj u j).toNat) = (X.filter (G.adj u)).length := by
      rw [← hX1A, filter_length_eq]
    omega
  have hfv : ssum l' (fun j => (G.adj v j).toNat) = t + (X.filter (G.adj v)).length := by
    have h1 : ssum l' (fun j => (G.adj v j).toNat) =
        ssum W (fun j => (G.adj v j).toNat) + ssum X (fun j => (G.adj v j).toNat) := by
      rw [← hWd, ← hXd]
      exact ssum_filter_add _ _ _
    have hW1 : ssum W (fun j => (G.adj v j).toNat) = t := by
      have hc : ssum W (fun j => (G.adj v j).toNat) = ssum W (fun _ => 1) := by
        apply ssum_congr
        intro y hy
        rw [(memW y hy).2.2]
        rfl
      rw [hc, ssum_const, Nat.one_mul]
      exact htd
    have hX0z : ssum X₀ (fun j => (G.adj v j).toNat) = 0 := by
      apply ssum_eq_zero
      intro y hy
      have hy2 := (memX0 y hy).2
      have hv' : G.adj v y = false := by
        by_cases hA : G.adj v y = true
        · rw [hA] at hy2; simp at hy2
        · exact bool_eq_false_of_ne_true hA
      simp [hv']
    have h2 : ssum X (fun j => (G.adj v j).toNat) =
        ssum X₁ (fun j => (G.adj v j).toNat) + ssum X₀ (fun j => (G.adj v j).toNat) := by
      rw [← hX1d, ← hX0d]
      exact ssum_filter_add _ _ _
    have hX1s : ssum X₁ (fun j => (G.adj v j).toNat) = (X.filter (G.adj v)).length := by
      rw [← hX1B]
      have hc : X₁.filter (fun x => !(G.adj u x)) = X₁.filter (G.adj v) := by
        apply List.filter_congr
        intro x hx
        have hor := Bool.or_eq_true_iff.mp (memX1 x hx).2
        have hnand := (memX x (memX1 x hx).1).2
        cases ha : G.adj u x with
        | false =>
          cases hb : G.adj v x with
          | false => rw [ha, hb] at hor; simp at hor
          | true => rfl
        | true =>
          cases hb : G.adj v x with
          | false => rfl
          | true => rw [ha, hb] at hnand; simp at hnand
      rw [hc, filter_length_eq]
    omega
  have hcross2 : crossCount G.adj ((List.finRange n).filter (mem2 u v)) l' =
      ssum l' (fun j => (G.adj u j).toNat) + ssum l' (fun j => (G.adj v j).toNat) := by
    show ssum ((List.finRange n).filter (mem2 u v)) (fun i => ssum l' (fun j => (G.adj i j).toNat)) = _
    exact ssum_filter_mem2 _ hnd (List.mem_finRange u) (List.mem_finRange v) huv _
  -- First edge count identity: `e = 1 + 2t + x₁ + e(V')`.
  have hS1 : ecountIn G.adj (List.finRange n) = 1 + 2 * t + x₁ + ecountIn G.adj l' := by
    omega
  -- Split `e(V')` further.
  have hpart2 : ecountIn G.adj l' = ecountIn G.adj W + ecountIn G.adj X + crossCount G.adj W X := by
    rw [← hWd, ← hXd]
    exact ecountIn_partition G l' _
  have hpart3 : ecountIn G.adj X = ecountIn G.adj X₁ + ecountIn G.adj X₀ + crossCount G.adj X₁ X₀ := by
    rw [← hX1d, ← hX0d]
    exact ecountIn_partition G X _
  have hcrossWX : crossCount G.adj W X = crossCount G.adj W X₁ + crossCount G.adj W X₀ := by
    rw [← hX1d, ← hX0d]
    exact crossCount_filter_add G.adj W X _
  have hE1 : ecountIn G.adj X₁ ≤ x₁ * x₁ / 4 := by
    rw [← hx1d]
    apply mantel_bound G hndX1
    intro x y z1 hx hy hz1 hxy hyz hxz1
    exact triFreeV x y z1 (List.Sublist.mem hx hsubX1l) (List.Sublist.mem hy hsubX1l)
      (List.Sublist.mem hz1 hsubX1l) hxy hyz hxz1
  have hE2 : crossCount G.adj X₁ X₀ ≤ x₁ * z := by
    rw [← hx1d, ← hzd]
    exact crossCount_le ..
  -- A maximal independent set `I₀` of `X₀`, of size `a`.
  obtain ⟨I₀, hI0sub, hI0nd, hI0indep, hI0max⟩ := exists_max_indep G X₀ hndX0
  generalize had : I₀.length = a
  rw [had] at hI0max
  have haz : a ≤ z := by
    rw [← had, ← hzd]
    exact List.Sublist.length_le hI0sub
  -- A6/A6': for any `i ∈ V'`, its `X₀`-neighborhood is independent, hence `≤ a`.
  have hnb : ∀ i : Fin n, i ∈ l' → (X₀.filter (G.adj i)).length ≤ a := by
    intro i hi
    apply hI0max _ List.filter_sublist
    intro x hx y hy hxy
    apply bool_eq_false_of_ne_true
    intro hAxy
    have hx0 := (List.mem_filter.mp hx).1
    have hy0 := (List.mem_filter.mp hy).1
    have hAx := (List.mem_filter.mp hx).2
    have hAy := (List.mem_filter.mp hy).2
    have hix : i ≠ x := fun he => by subst he; rw [G.irr i] at hAx; simp at hAx
    have hiy : i ≠ y := fun he => by subst he; rw [G.irr i] at hAy; simp at hAy
    obtain ⟨a1, b1, c1, hT, -, -, -, ha1, hb1, hc1⟩ :=
      triTerm_one_of_triangle hix hxy hiy hAx hAxy hAy
    exact hcov_elim a1 b1 c1 hT (by
      intro w hw
      have hxl := List.Sublist.mem hx0 hsubX0l
      have hyl := List.Sublist.mem hy0 hsubX0l
      rcases hw with h | h | h
      · rw [h]
        rcases ha1 with h2 | h2 | h2
        · rw [h2]; exact memV i hi
        · rw [h2]; exact memV x hxl
        · rw [h2]; exact memV y hyl
      · rw [h]
        rcases hb1 with h2 | h2 | h2
        · rw [h2]; exact memV i hi
        · rw [h2]; exact memV x hxl
        · rw [h2]; exact memV y hyl
      · rw [h]
        rcases hc1 with h2 | h2 | h2
        · rw [h2]; exact memV i hi
        · rw [h2]; exact memV x hxl
        · rw [h2]; exact memV y hyl)
  -- `e(W–X₀) ≤ t·a`.
  have hE4 : crossCount G.adj W X₀ ≤ t * a := by
    have h1 : ∀ i ∈ W, ssum X₀ (fun j => (G.adj i j).toNat) ≤ a := by
      intro i hi
      rw [← filter_length_eq]
      exact hnb i (List.Sublist.mem hi hsubW)
    have h2 := ssum_le h1
    have h3 : ssum W (fun _ => a) = a * t := by
      rw [← htd]
      exact ssum_const W a
    show ssum W (fun i => ssum X₀ (fun j => (G.adj i j).toNat)) ≤ t * a
    rw [Nat.mul_comm t a, ← h3]
    exact h2
  -- `e(X₀) ≤ a·(z−a)`: every edge of `X₀` has an endpoint in `X₀ ∖ I₀`, and
  -- each such endpoint has at most `a` neighbors in `X₀`.
  have hE5 : ecountIn G.adj X₀ ≤ a * (z - a) := by
    have hfI0 : X₀.filter (fun x => decide (x ∈ I₀)) = I₀ :=
      filter_mem_eq_of_sublist hI0sub hndX0
    have hpart0 := ecountIn_partition G X₀ (fun x => decide (x ∈ I₀))
    rw [hfI0] at hpart0
    have heI0 : ecountIn G.adj I₀ = 0 := by
      apply ecountIn_eq_zero_of_indep G
      intro x y hx hy hxy
      exact hI0indep x hx y hy hxy
    have hlenXr : (X₀.filter (fun x => !decide (x ∈ I₀))).length = z - a := by
      have h3 := filter_length_add (fun x => decide (x ∈ I₀)) X₀
      rw [hfI0] at h3
      omega
    have hself := ecountIn_le_cross_self G (X₀.filter (fun x => !decide (x ∈ I₀)))
    have hcs := crossCount_symm G (X₀.filter (fun x => !decide (x ∈ I₀))) I₀
    have hcover := crossCount_filter_add G.adj (X₀.filter (fun x => !decide (x ∈ I₀))) X₀
      (fun x => decide (x ∈ I₀))
    rw [hfI0] at hcover
    have hdeg : ∀ i ∈ X₀.filter (fun x => !decide (x ∈ I₀)),
        ssum X₀ (fun j => (G.adj i j).toNat) ≤ a := by
      intro i hi
      rw [← filter_length_eq]
      exact hnb i (List.Sublist.mem (List.Sublist.mem hi List.filter_sublist) hsubX0l)
    have hsum : ssum (X₀.filter (fun x => !decide (x ∈ I₀)))
        (fun i => ssum X₀ (fun j => (G.adj i j).toNat)) ≤ (z - a) * a := by
      have h2 := ssum_le hdeg
      have h4 := ssum_const (X₀.filter (fun x => !decide (x ∈ I₀))) a
      rw [hlenXr] at h4
      rw [Nat.mul_comm (z - a) a, ← h4]
      exact h2
    have hXrX0 : crossCount G.adj (X₀.filter (fun x => !decide (x ∈ I₀))) X₀ =
        ssum (X₀.filter (fun x => !decide (x ∈ I₀)))
          (fun i => ssum X₀ (fun j => (G.adj i j).toNat)) := rfl
    have hmc2 : (z - a) * a = a * (z - a) := Nat.mul_comm _ _
    omega
  -- Final assembly via `caseA_algebra`.
  have hxz' : x₁ + z = n - 2 - t := by omega
  have hzt : z ≤ t := by
    have hzX : z ≤ X.length := by
      rw [← hzd, ← hX0d]
      exact List.Sublist.length_le List.filter_sublist
    omega
  have hB := caseA_algebra n t z x₁ ht ht2 h5 hxz'
  have hat : a ≤ t := by omega
  have hazt : t * a + a * (z - a) ≤ t * z := az_le_tz hat haz
  have hmc1 : x₁ * z = z * x₁ := Nat.mul_comm _ _
  omega
/-! ## Triangle witnesses and edge-disjointness -/

/-- The ordered triple `(a, b, c)` is a triangle of `G`: three pairwise distinct
vertices with all three adjacencies present. -/
def IsTri (G : Gph n) (t : Fin n × Fin n × Fin n) : Prop :=
  t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 ∧
  G.adj t.1 t.2.1 = true ∧ G.adj t.2.1 t.2.2 = true ∧ G.adj t.1 t.2.2 = true

/-- The unordered pair `{a, b}` equals the unordered pair `{c, d}`. -/
def EdgeEq (a b c d : Fin n) : Prop := (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Two triangles are edge-disjoint: no edge of the first equals an edge of the
second (as unordered pairs), over all 3×3 pairs of edges. -/
def EdgeDisj (t₁ t₂ : Fin n × Fin n × Fin n) : Prop :=
  ¬ EdgeEq t₁.1 t₁.2.1 t₂.1 t₂.2.1 ∧ ¬ EdgeEq t₁.1 t₁.2.1 t₂.2.1 t₂.2.2 ∧
  ¬ EdgeEq t₁.1 t₁.2.1 t₂.1 t₂.2.2 ∧
  ¬ EdgeEq t₁.2.1 t₁.2.2 t₂.1 t₂.2.1 ∧ ¬ EdgeEq t₁.2.1 t₁.2.2 t₂.2.1 t₂.2.2 ∧
  ¬ EdgeEq t₁.2.1 t₁.2.2 t₂.1 t₂.2.2 ∧
  ¬ EdgeEq t₁.1 t₁.2.2 t₂.1 t₂.2.1 ∧ ¬ EdgeEq t₁.1 t₁.2.2 t₂.2.1 t₂.2.2 ∧
  ¬ EdgeEq t₁.1 t₁.2.2 t₂.1 t₂.2.2

/-- A sorted triangle triple is a triangle. -/
theorem isTri_of_triTerm {n : Nat} (G : Gph n) {t : Fin n × Fin n × Fin n}
    (h : triTerm G.adj t.1 t.2.1 t.2.2 = 1) : IsTri G t := by
  obtain ⟨hij, hjk, hA1, hA2, hA3⟩ := triTerm_eq_one h
  have h12 : t.1 ≠ t.2.1 := fun he => by have h2 := Fin.ext_iff.mp he; omega
  have h23 : t.2.1 ≠ t.2.2 := fun he => by have h2 := Fin.ext_iff.mp he; omega
  have h13 : t.1 ≠ t.2.2 := fun he => by have h2 := Fin.ext_iff.mp he; omega
  exact ⟨h12, h23, h13, hA1, hA2, hA3⟩

/-- Two triangles sharing no two vertices are edge-disjoint. -/
theorem edgeDisj_of_not_share2 {n : Nat} (G : Gph n) {s t : Fin n × Fin n × Fin n}
    (hs : IsTri G s) (hns : ¬ share2 s t) : EdgeDisj s t := by
  obtain ⟨h12, h23, h13, -, -, -⟩ := hs
  have key : ∀ (x y z w : Fin n), x ≠ y → memTri s x → memTri s y →
      memTri t z → memTri t w → EdgeEq x y z w → False := by
    intro x y z w hxy hx hy hz hw hEq
    apply hns
    refine ⟨x, y, hxy, hx, hy, ?_, ?_⟩
    · rcases hEq with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact memTri_of_eq hz h1.symm
      · exact memTri_of_eq hw h1.symm
    · rcases hEq with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact memTri_of_eq hw h2.symm
      · exact memTri_of_eq hz h2.symm
  have ms1 : memTri s s.1 := Or.inl rfl
  have ms2 : memTri s s.2.1 := Or.inr (Or.inl rfl)
  have ms3 : memTri s s.2.2 := Or.inr (Or.inr rfl)
  have mt1 : memTri t t.1 := Or.inl rfl
  have mt2 : memTri t t.2.1 := Or.inr (Or.inl rfl)
  have mt3 : memTri t t.2.2 := Or.inr (Or.inr rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => key s.1 s.2.1 t.1 t.2.1 h12 ms1 ms2 mt1 mt2 h
  · exact fun h => key s.1 s.2.1 t.2.1 t.2.2 h12 ms1 ms2 mt2 mt3 h
  · exact fun h => key s.1 s.2.1 t.1 t.2.2 h12 ms1 ms2 mt1 mt3 h
  · exact fun h => key s.2.1 s.2.2 t.1 t.2.1 h23 ms2 ms3 mt1 mt2 h
  · exact fun h => key s.2.1 s.2.2 t.2.1 t.2.2 h23 ms2 ms3 mt2 mt3 h
  · exact fun h => key s.2.1 s.2.2 t.1 t.2.2 h23 ms2 ms3 mt1 mt3 h
  · exact fun h => key s.1 s.2.2 t.1 t.2.1 h13 ms1 ms3 mt1 mt2 h
  · exact fun h => key s.1 s.2.2 t.2.1 t.2.2 h13 ms1 ms3 mt2 mt3 h
  · exact fun h => key s.1 s.2.2 t.1 t.2.2 h13 ms1 ms3 mt1 mt3 h

/-- **JSP-000839 (scoped component, k = 2).**
Every simple graph on `n ≥ 5` vertices with at least `⌊n²/4⌋ + 2` edges
contains two edge-disjoint triangles. -/
theorem jsp_000839 (n : Nat) (G : Gph n) (h5 : 5 ≤ n)
    (h : n * n / 4 + 2 ≤ ecountIn G.adj (List.finRange n)) :
    ∃ t₁ t₂ : Fin n × Fin n × Fin n, IsTri G t₁ ∧ IsTri G t₂ ∧ EdgeDisj t₁ t₂ := by
  by_cases hcon : ∃ t₁ t₂ : Fin n × Fin n × Fin n, IsTri G t₁ ∧ IsTri G t₂ ∧ EdgeDisj t₁ t₂
  · exact hcon
  · exfalso
    have hnd : (List.finRange n).Nodup := List.nodup_finRange n
    have h1 : n * n / 4 + 1 ≤ ecountIn G.adj (List.finRange n) := by omega
    have hrad := rademacher_list n n G (List.finRange n) hnd List.length_finRange h1
    have h2 : 2 ≤ tcountIn G.adj (List.finRange n) := by omega
    obtain ⟨t₁, t₂, hne, -, -, ht1, ht2⟩ := exists_two_tris hnd h2
    -- Any two distinct sorted triangle triples share two vertices.
    have H : ∀ s t : Fin n × Fin n × Fin n,
        triTerm G.adj s.1 s.2.1 s.2.2 = 1 → triTerm G.adj t.1 t.2.1 t.2.2 = 1 →
        s ≠ t → share2 s t := by
      intro s t hs ht hst
      by_cases hsh : share2 s t
      · exact hsh
      · exfalso
        exact hcon ⟨s, t, isTri_of_triTerm G hs, isTri_of_triTerm G ht,
          edgeDisj_of_not_share2 G (isTri_of_triTerm G hs) hsh⟩
    rcases classification G H ht1 ht2 hne with hA | hB
    · obtain ⟨u, v, huv, hAuv, hcov⟩ := hA
      have hb := caseA_bound G h5 h huv hAuv hcov
      omega
    · obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs,
        hApq, hApr, hAps, hAqr, hAqs, hArs, hsub⟩ := hB
      have hb := caseB_bound G h5 hpq hpr hps hqr hqs hrs
        hApq hApr hAps hAqr hAqs hArs hsub
      omega

/-! ## Sanity examples -/

/-- The graph `K₅` minus the edges `{0,3}` and `{0,4}` (8 edges). -/
def G5 : Gph 5 where
  adj i j := !(i == j) &&
    !((min i.val j.val == 0 && max i.val j.val == 3) ||
      (min i.val j.val == 0 && max i.val j.val == 4))
  sym := by
    intro i j
    have hb : (i == j) = (j == i) := by
      by_cases h : i = j
      · rw [h]
      · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]
    show (!(i == j) && !((min i.val j.val == 0 && max i.val j.val == 3) ||
        (min i.val j.val == 0 && max i.val j.val == 4))) =
      (!(j == i) && !((min j.val i.val == 0 && max j.val i.val == 3) ||
        (min j.val i.val == 0 && max j.val i.val == 4)))
    rw [hb, Nat.min_comm i.val j.val, Nat.max_comm i.val j.val]
  irr := by
    intro i
    show (!(i == i) && !_) = false
    rw [beq_self_eq_true]
    rfl

/-- Edge count sanity check: `K₅ − 2` edges has exactly `8 = ⌊25/4⌋ + 2` edges. -/
example : ecountIn G5.adj (List.finRange 5) = 8 := by decide

/-- Two explicit edge-disjoint triangles in `G5`. -/
example : IsTri G5 ((⟨0, by decide⟩ : Fin 5), (⟨1, by decide⟩ : Fin 5), (⟨2, by decide⟩ : Fin 5)) ∧
    IsTri G5 ((⟨2, by decide⟩ : Fin 5), (⟨3, by decide⟩ : Fin 5), (⟨4, by decide⟩ : Fin 5)) ∧
    EdgeDisj ((⟨0, by decide⟩ : Fin 5), (⟨1, by decide⟩ : Fin 5), (⟨2, by decide⟩ : Fin 5))
      ((⟨2, by decide⟩ : Fin 5), (⟨3, by decide⟩ : Fin 5), (⟨4, by decide⟩ : Fin 5)) := by
  unfold IsTri EdgeDisj EdgeEq
  decide

/-- The theorem applies to `G5`. -/
example : ∃ t₁ t₂ : Fin 5 × Fin 5 × Fin 5,
    IsTri G5 t₁ ∧ IsTri G5 t₂ ∧ EdgeDisj t₁ t₂ :=
  jsp_000839 5 G5 (by decide) (by decide)

end Jsp000839
