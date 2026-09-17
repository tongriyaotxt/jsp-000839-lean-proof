### Related problem or entry

JSP-000839 — "Just above the maximum bipartite edge count, how many edge-disjoint triangles are guaranteed?" (`problems/catalog-0801-0900.md#JSP-000839`; current record: Solved, Lean proof: No). Corresponds to Erdős problem #1009 (solved by E. Győri, *On the number of edge-disjoint triangles in graphs of given size*, 1988).

Relation to issue #567: that submission is a *packing-obstruction construction* (a
secondary-loss barrier example, using Mathlib, in a different direction); it is not a
formalization of the k = 2 existence theorem and does not conflict with this submission.
This submission follows the precedent of #413 (JSP-000840 / Erdős #1010, scoped t = 1
component): a scoped component of the solved problem, formalized in Lean 4 core.

### Recipient placeholder or confirmed public ID

RECIPIENT-JSP-000839-A (identity unconfirmed; submitter public ID: github.com/tongriyaotxt)

### Contributions and evidence

**Contribution type: formalization only (scoped component k = 2).** The mathematical
result is due to the published literature, not to this contribution:

- E. Győri, *On the number of edge-disjoint triangles in graphs of given size*,
  Colloq. Math. Soc. János Bolyai 52 (1988), 267–276 (full theorem, all k).

**New contribution (2026-09-17):** a complete machine-checked Lean 4 formalization of
the `k = 2` case: *every simple graph on n ≥ 5 vertices with at least ⌊n²/4⌋ + 2 edges
contains two edge-disjoint triangles*. The hypothesis `n ≥ 5` is sharp (`K₄` is the
unique small obstruction). The development includes from-scratch proofs of: Mantel's
theorem, Rademacher's theorem over arbitrary vertex lists (`rademacher_list`), Boolean
edge-partition counting identities (`ecountIn_partition`, cross-count bounds), a
*classification lemma* for pairwise edge-sharing triangle families (common edge, or all
triangles inside a `K₄`), and the two case-specific counting arguments.

Formal statement (top-level theorem):

```lean
theorem jsp_000839 (n : Nat) (G : Gph n) (h5 : 5 ≤ n)
    (h : n * n / 4 + 2 ≤ ecountIn G.adj (List.finRange n)) :
    ∃ t₁ t₂ : Fin n × Fin n × Fin n, IsTri G t₁ ∧ IsTri G t₂ ∧ EdgeDisj t₁ t₂
```

Statement correspondence notes: a simple graph on `n` vertices is a symmetric
irreflexive Boolean adjacency on `Fin n` (`Gph n`); edges are unordered pairs counted
once (`i < j`); `IsTri` = three pairwise-distinct pairwise-adjacent vertices;
`EdgeDisj` = no shared unordered edge pair over all 9 edge pairs; `n*n/4 = ⌊n²/4⌋`
(Nat division). No extra premises; all quantifiers first-order. See
`STATEMENT-CORRESPONDENCE.md` in the repository for the full mapping table.

**Pinned proof source:**

- Repository: https://github.com/tongriyaotxt/jsp-000839-lean-proof
- Pinned commit: `PINNED-COMMIT-SHA-TO-FILL`
- File: `Jsp000839.lean` (self-contained, **Lean 4 core only, no Mathlib dependency**, ~3800 lines)
- Toolchain: Lean v4.34.0 (pinned in `lean-toolchain`)

**Verification records:**

- Local kernel check (Lean v4.34.0, Windows, `lean Jsp000839.lean`): pass, no errors (2026-09-17).
- Axiom audit (`#print axioms jsp_000839`): `propext`, `Classical.choice`, `Quot.sound` only. **No `sorryAx`; no `native_decide`/`Lean.ofReduceBool`** — the entire development is kernel-checked reasoning with no trusted computation. The three sanity examples (`K₅` minus two edges: 8 edges, explicit edge-disjoint triangle pair, theorem instantiation) use kernel `decide` only.
- CI kernel check (GitHub Actions, ubuntu-latest, fresh elan + Lean v4.34.0, `lean Jsp000839.lean` plus automated sorryAx scan): CI-RUN-URL-TO-FILL.

If the record for JSP-000839 is updated to `Lean proof: Yes` (k = 2 component) following review, its claim-status screening flags would change accordingly; this issue supplies the evidence for that review. The submission covers only the `k = 2` case; the general Győri theorem (all `k`) is not part of this submission.

### Confirmation status

Pending. No written confirmation exists yet; the recipient identity is intentionally left as the placeholder above. The submitting GitHub account is the public point of contact.

### Attribution questions and conflicts

None. No conflicts to disclose. Mathematical priority belongs to the literature cited above; this contribution claims formalization authorship only.
