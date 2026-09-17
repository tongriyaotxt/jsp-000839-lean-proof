# JSP-000839 — Statement correspondence audit

Catalog entry (TheJustinSunPrize/awards, `problems/catalog-0801-0900.md#JSP-000839`):

> Just above the maximum bipartite edge count, how many edge-disjoint triangles are
> guaranteed?

Scoped component formalized here: the **k = 2 case** of Győri's theorem, i.e. the
first step past the one-triangle threshold. Upstream reference:
<https://www.erdosproblems.com/1009> ("if a graph on n vertices has at least ⌊n²/4⌋ + k
edges, and n is sufficiently large, then it contains k edge-disjoint triangles";
solved by Győri, 1988).

## Mapping table

| Informal concept | Lean formalization |
| --- | --- |
| simple graph on n vertices | `Gph n`: `adj : Fin n → Fin n → Bool` with `sym : ∀ i j, adj i j = adj j i`, `irr : ∀ i, adj i i = false` |
| edge (unordered pair) | counted once at the pair `i < j` (on `Fin.val`) |
| number of edges | `ecountIn G.adj (List.finRange n) = Σ_{i<j} (adj i j).toNat` |
| ⌊n²/4⌋ | `n * n / 4` (Nat division is floor) |
| triangle | `IsTri G (a,b,c)`: three pairwise-distinct vertices with all three adjacencies `= true` |
| two edge-disjoint triangles | `EdgeDisj t₁ t₂`: none of the 3 edges of `t₁` equals any of the 3 edges of `t₂` as unordered pairs (`EdgeEq`: `(a=c ∧ b=d) ∨ (a=d ∧ b=c)`), all 9 combinations negated |
| n ≥ 5 | explicit hypothesis `h5 : 5 ≤ n` |
| "e ≥ ⌊n²/4⌋ + 2 forces two edge-disjoint triangles" | `n*n/4 + 2 ≤ ecountIn … → ∃ t₁ t₂, IsTri … ∧ IsTri … ∧ EdgeDisj …` |

## Notes

- All quantifiers are first-order over `Nat`/`Fin n`; no extra premises, no classical
  axioms beyond the Lean default (`propext`, `Classical.choice`, `Quot.sound`).
- The hypothesis `5 ≤ n` is necessary: `K₄` has 6 = ⌊4²/4⌋ + 2 edges but any two of its
  four triangles share an edge. (`n = 5, 6` were also brute-force checked: 0
  counterexamples, consistent with the theorem.)
- Edge-disjointness of *triangles* is equivalent to sharing at most one vertex; the
  contrapositive used in the proof is `edgeDisj_of_not_share2`.
- The full Győri theorem (all `k`, `n` large) is NOT claimed; this submission is
  explicitly the `k = 2` component (with the sharp bound `n ≥ 5`, i.e. no largeness
  condition needed beyond excluding `K₄`).
- Rademacher's theorem (`rademacher_list`, e ≥ ⌊n²/4⌋ + 1 ⟹ ≥ ⌊n/2⌋ triangles, over an
  arbitrary vertex list) and Mantel's theorem (`mantel`) are proved in-file and used as
  lemmas; they are the same statements as JSP-000840's main theorem, here reused as
  infrastructure.
- No `sorry`, no `native_decide`; nothing trusted beyond the Lean 4 kernel (v4.34.0).
  The three sanity `example`s use kernel `decide` only.
