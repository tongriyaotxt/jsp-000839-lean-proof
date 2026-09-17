# Justin Sun Prize — JSP-000839 Lean 4 形式化证明（边不交三角形，k = 2 分量）

## 题目

**JSP-000839**: Just above the maximum bipartite edge count, how many edge-disjoint
triangles are guaranteed?
（边数刚刚超过二部图最大边数 ⌊n²/4⌋ 时，图中能保证多少个两两边不交的三角形？）

来源：<https://github.com/TheJustinSunPrize/awards> · `problems/catalog-0801-0900.md#JSP-000839`
对应 Erdős 问题 <https://www.erdosproblems.com/1009>（Győri 1988 已解决：
e ≥ ⌊n²/4⌋ + k 且 n 充分大时，保证 k 个边不交三角形）。

## 本仓库证明的内容（scoped component：k = 2）

**每个 n ≥ 5 顶点简单图，若边数 ≥ ⌊n²/4⌋ + 2，则存在两个边不交的三角形。**

这是 Győri 定理的 k = 2 情形。k = 1 是平凡的（Mantel：e > ⌊n²/4⌋ ⟹ 有三角形）；
一般 k 的 Győri 全定理不在本提交范围内。`n ≥ 5` 不可去：`n = 4` 的 `K₄`
（6 = ⌊16/4⌋ + 2 条边、4 个三角形两两共享边）是反例。

形式化陈述（`Jsp000839.lean`，纯 **Lean 4 core**，零依赖，不需要 Mathlib）：

```lean
theorem jsp_000839 (n : Nat) (G : Gph n) (h5 : 5 ≤ n)
    (h : n * n / 4 + 2 ≤ ecountIn G.adj (List.finRange n)) :
    ∃ t₁ t₂ : Fin n × Fin n × Fin n, IsTri G t₁ ∧ IsTri G t₂ ∧ EdgeDisj t₁ t₂
```

- 图：`Gph n` = `Fin n → Fin n → Bool` 邻接矩阵 + 对称性 + 无自环。
- 边数 `ecountIn`：无序点对 i < j 的计数（Nat 除法即向下取整，`n*n/4 = ⌊n²/4⌋`）。
- `IsTri G t`：三元组 `t = (a, b, c)` 两两互异且三边都在。
- `EdgeDisj t₁ t₂`：t₁ 的三条边与 t₂ 的三条边两两不作为无序对相等（9 个 `¬ EdgeEq`）。

## 证明思路

反证：若无两个边不交三角形，则（由 Rademacher 定理，本文件内对列表重新证明：
e ≥ ⌊n²/4⌋+1 ⟹ 三角形数 ≥ ⌊n/2⌋ ≥ 2）任取两个不同的三角形 `s ≠ t`；
它们不能边不交 ⟺ 必共享两个顶点（`share2`）。于是任意两个三角形都共享一条边。

**分类引理**（`classification`）：两两边共享的三角形族（≥ 2 个成员）必居其一：

- **Case A**：存在公共边 `uv` 含于每个三角形。设 `W = N(u) ∩ N(v)`（`|W| = t ≥ ⌊n/2⌋`，
  由 Rademacher），`X₁` = 与 `u` 或 `v` 恰一方相邻的其余顶点，`X₀` = 与两者均不相邻的
  其余顶点。取 `X₀` 的最大独立集 `I₀`（`|I₀| = a`）。事实：W 独立（A2）、`W–X₁` 无边（A7）、
  任意 `i ∈ V'` 的 `X₀`-邻域独立故 ≤ a（A6）。计数：
  `e = 1 + 2t + x₁ + e(W) + e(X₁) + e(X₀) + e(W–X₁) + e(W–X₀) + e(X₁–X₀)`
  `≤ 1 + 2t + x₁ + 0 + ⌊x₁²/4⌋ + a(z−a) + 0 + t·a + z·x₁`
  `≤ 1 + 2t + x₁ + t·z + z·x₁ + ⌊x₁²/4⌋ ≤ ⌊n²/4⌋ + 1`，
  其中 `t·a + a(z−a) ≤ t·z`（因 `a ≤ z ≤ t`），最后一步是恒等式
  `4B″ + d² + 2dx₁ = n² + 4d`（`d = t − z`）配合 `d² + 4 ≥ 4d`（`caseA_algebra`）。
  与假设 `e ≥ ⌊n²/4⌋ + 2` 矛盾。
- **Case B**：所有三角形落在某个 `K₄ = {p,q,r,s}` 内。`Y`（其余顶点）中每个顶点在
  `K₄` 中至多 1 个邻居（否则产生避开某条 `K₄` 边的三角形，违反两两边共享）；
  `Y` 无三角形（Mantel）。计数 `e ≤ 6 + (n−4) + ⌊(n−4)²/4⌋ ≤ ⌊n²/4⌋ + 1`，矛盾。

全部推理为内核可核查：列表加权和（`ssum`）、Bool 二分边剖分恒等式
（`ecountIn_partition`）、cross-count 上界、Mantel（本文件内证明）、
Rademacher（对任意顶点列表的加强版 `rademacher_list`）、子列表枚举取最大独立集
（`exists_max_indep`）。

## 构建与验证

安装 Lean 4（本证明在 v4.34.0 上验证通过；见 `lean-toolchain`）后：

```bash
lean Jsp000839.lean
```

公理审计（文件末尾 `#print axioms jsp_000839`）：仅 `propext`、`Classical.choice`、
`Quot.sound`。**无 `sorryAx`，未使用 `native_decide`**（全部推理为内核可核查的证明项；
三个 sanity `example` 仅用 `decide`：`K₅` 去掉边 `{0,3}`、`{0,4}` 的 8 边图恰有
`8 = ⌊25/4⌋ + 2` 条边，含显式边不交三角形对 `(0,1,2)`、`(2,3,4)`，且主定理对它适用）。

## 数学出处（原问题的解答，非本仓库贡献）

- E. Győri, *On the number of edge-disjoint triangles in graphs of given size*,
  Colloq. Math. Soc. János Bolyai 52 (1988), 267–276.

本仓库贡献：上述定理 k = 2 情形的机器可验证形式化（Lean 4 core）。
数学结果本身属于上述文献。
