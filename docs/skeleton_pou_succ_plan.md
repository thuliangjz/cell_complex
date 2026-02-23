# Proof Plan: `skeleton_pou_succ`

## Goal

Given a partition of unity `pou_n : CompatibleSkeletonPOU α s n` on the
n-skeleton, construct a partition of unity on the (n+1)-skeleton satisfying:

- **(i) Restriction:** the new POU restricts to `pou_n` on `Skeleton X n`.
- **(ii) Zero-extension:** for any open `V ⊆ Skeleton X n`, there is an open
  `V' ⊆ Skeleton X (n+1)` containing `V` such that whenever `pou_n.toFun a ≡ 0`
  on `V`, we have `pou_succ.toFun a ≡ 0` on `V'`. Crucially, `V'` depends only
  on `V`, not on `a`.

## Lemma statement

```lean
theorem skeleton_pou_succ
    {α : Type*} (s : α → Set X) (hs_open : ∀ a, IsOpen (s a))
    (hs_cover : ⋃ a, s a = Set.univ)
    (n : ℕ) (pou_n : CompatibleSkeletonPOU α s n) :
    ∃ pou_succ : CompatibleSkeletonPOU α s (n + 1),
      (∀ a (x : Skeleton X n),
        pou_succ.toFun a
          ⟨x.1, skeleton_mono n (n + 1) (Nat.le_add_right n 1) x.2⟩ =
          pou_n.toFun a x) ∧
      (∀ V : Set (Skeleton X n), IsOpen V →
        ∃ V' : Set (Skeleton X (n + 1)), IsOpen V' ∧
          (∀ x : Skeleton X n, x ∈ V →
            (⟨x.1, skeleton_mono n (n + 1) (Nat.le_add_right n 1) x.2⟩ :
              Skeleton X (n + 1)) ∈ V') ∧
          (∀ a, (∀ x ∈ V, pou_n.toFun a x = 0) →
            (∀ y ∈ V', pou_succ.toFun a y = 0)))
```

---

## Step 0 — Enhance `exists_cb_pou_on_cell` with collar agreement

**Target goal.** Add a fifth conjunct exporting the collar width `ε` and the
fact that on `boundary_collar (ε / 2)` (where `σ = 0`) the cell-level POU
equals the radial pullback of `pou_n`:

```
∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
  ∀ a (x : cb (n + 1)), x.1 ≠ 0 → (1 - ε / 2 : ℝ) < ‖x.1‖ →
    cb_pou a x = pou_n.toFun a
      ⟨characteristic_cn (n+1) γ (radial_proj x).1,
       char_cnp1_boundary_in_skn n γ (radial_proj x).1 (radial_proj x).2⟩
```

**Why needed.** Property (ii) requires that `cb_pou a` vanishes on a collar
whenever `pou_n.toFun a` vanishes on the corresponding boundary region. The
existing boundary-agreement conclusion covers only `∂D`, not the collar
interior.

**How (~10 lines).** The proof of `exists_cb_pou_on_cell` already constructs
`ε`, `σ`, `hσ_boundary`. On `boundary_collar (ε / 2)`, `σ x = 0`, so
`cb_pou_candidate a x = phi a x`. For `x.1 ≠ 0`,
`phi a x = boundary_pullback a (radial_proj x)` by definition. Unfolding
`boundary_pullback` gives the stated equality.

---

## Step 1 — Choose cell-level POUs for all cells

**Target goal.** For each `γ : CellOfDim (n + 1)`, obtain
`cb_pou γ : α → C(cb (n+1), ℝ)` and a collar width `cb_ε γ : ℝ` with all
five properties from the enhanced `exists_cb_pou_on_cell`.

**How (~15 lines).** Apply the enhanced `exists_cb_pou_on_cell` to each `γ`,
then use `choose` to extract:

- `cb_pou : CellOfDim (n+1) → α → C(cb (n+1), ℝ)`
- `cb_ε : CellOfDim (n+1) → ℝ`
- Five families of hypotheses: `h_nonneg`, `h_sum`, `h_sub`, `h_boundary`,
  `h_collar`.

---

## Step 2 — Define function on disjoint sum and show factoring

**Target goal.** For each `a : α`, define

```
pou_ext a : Skeleton X n ⊕ (Σ γ : CellOfDim (n+1), cb (n+1)) → ℝ
```

by `Sum.inl x ↦ pou_n.toFun a x` and `Sum.inr ⟨γ, y⟩ ↦ cb_pou γ a y`.
Then prove it factors through `glue_setoid`:

```
glue_setoid ... x₁ x₂ → pou_ext a x₁ = pou_ext a x₂
```

**How (~20 lines).** Case-split via `glue_rel_equiv_explicit`:

| Case | Why equal |
|------|----------|
| Both `Sum.inl` | `rfl` |
| `Sum.inl x` ~ `Sum.inr ⟨γ, y⟩` (boundary) | `h_boundary γ a y hy` |
| Both `Sum.inr`, same image | chain two boundary agreements |
| Reflexive | `rfl` |

---

## Step 3 — Lift to `Skeleton X (n+1)` and prove continuity

**Target goal.** Define `pou_succ_fun : α → C(Skeleton X (n+1), ℝ)`.

**How (~20 lines).**

1. `Quotient.lift (pou_ext a) (factoring)` gives a function on the
   cell-attachment quotient `CellAttached`.
2. Compose with the inverse of `cell_attached_to_sknp1_homeomorphic` to obtain
   `pou_succ_raw a : Skeleton X (n+1) → ℝ`.
3. **Continuity:** `pou_ext a` is continuous on each summand (`pou_n.toFun a`
   and `cb_pou γ a`), hence on the disjoint sum. `Quotient.lift` preserves
   continuity. Composition with the continuous inverse of a homeomorphism
   preserves continuity.
4. Package as `⟨pou_succ_raw a, ...⟩ : C(Skeleton X (n+1), ℝ)`.

---

## Step 4 — Prove nonnegativity and sum equals one

**Target goal.**

```
∀ a (x : Skeleton X (n+1)), 0 ≤ pou_succ_fun a x
∀ x : Skeleton X (n+1), ∑ᶠ a, pou_succ_fun a x = 1
```

**How (~20 lines).** For any `x`, use `skn_sum_cnp1_to_sknp1_surj` to obtain a
preimage `x'` in the disjoint sum. Then `pou_succ_fun a x = pou_ext a x'`.

- **Nonneg:** if `Sum.inl`, use `pou_n.nonneg`; if `Sum.inr ⟨γ, y⟩`, use
  `h_nonneg γ`.
- **Sum = 1:** if `Sum.inl`, use `pou_n.sum_eq_one`; if `Sum.inr ⟨γ, y⟩`, use
  `h_sum γ`.

---

## Step 5 — Prove subordination and restriction property (i)

**Target goal.**

```
∀ a, tsupport (pou_succ_fun a) ⊆ Subtype.val ⁻¹' (s a)

∀ a (x : Skeleton X n),
  pou_succ_fun a ⟨x.1, skeleton_mono ... x.2⟩ = pou_n.toFun a x
```

**How (~20 lines).**

- **Subordination:** lift to disjoint sum. If `Sum.inl z`, then
  `z ∈ tsupport (pou_n.toFun a)` gives `z.1 ∈ s a` by `pou_n.subordinate`.
  If `Sum.inr ⟨γ, y⟩`, then `y ∈ tsupport (cb_pou γ a)` gives
  `characteristic_cn (n+1) γ y ∈ s a` by `h_sub γ`.
- **Restriction (i):** for `x : Skeleton X n`, the inclusion into
  `Skeleton X (n+1)` has preimage `Sum.inl x`. So
  `pou_succ_fun a (incl x) = pou_ext a (Sum.inl x) = pou_n.toFun a x`.

---

## Step 6 — Prove zero-extension property (ii)

**Target goal.** For any open `V ⊆ Skeleton X n`, construct an open
`V' ⊆ Skeleton X (n+1)` containing `V` such that whenever
`pou_n.toFun a = 0` on `V`, then `pou_succ_fun a = 0` on `V'`.

**How (~20 lines).**

1. **Preimage of `V'` in the disjoint sum.** Left summand: `V`. Right summand
   for cell `γ`: the collar set
   `W_γ = {x : cb (n+1) | radial_proj x ∈ φ_γ⁻¹(V) ∧ ‖x.1‖ > 1 − ε_γ/2}`.
2. **`W_γ` is open.** On `{‖x.1‖ > 1 − ε_γ/2}`, radial projection is
   continuous, and `φ_γ⁻¹(V)` is open in `cb_boundary`. So `W_γ` is the
   intersection of two open sets.
3. **Saturation.** If `Sum.inl z ∈ V` and boundary point
   `Sum.inr ⟨γ, y⟩ ∼ Sum.inl z`, then `y ∈ ∂D_γ` with `φ_γ(y) = z ∈ V`,
   so `radial_proj(y) = y ∈ φ_γ⁻¹(V)` and `‖y.1‖ = 1 > 1 − ε_γ/2`.
   The converse is analogous.
4. **`V'` is open** in `Skeleton X (n+1)` because it is the image of a
   saturated open set under the quotient map, transported by the homeomorphism.
5. **Zero property.** If `pou_n.toFun a = 0` on `V`, then on `V` itself
   `pou_ext a = 0` (left summand). On `W_γ`, by collar agreement (`h_collar γ`),
   `cb_pou γ a x = pou_n.toFun a ⟨..., proj(x)⟩ = 0` since `proj(x)` maps
   into `V`. So `pou_ext a = 0` on the full preimage, hence
   `pou_succ_fun a = 0` on `V'`.

---

## Step 7 — Prove local finiteness

**Target goal.**

```
LocallyFinite (fun a => Function.support (pou_succ_fun a))
```

**How (~20 lines).** For any `x : Skeleton X (n+1)`, two cases:

- **`x` is in the interior of cell `γ`:** the open cell `e_γ` is a
  neighborhood. On `e_γ`, `pou_succ_fun a = cb_pou γ a`. Since `cb (n+1)` is
  compact, the cell-level POU has only finitely many nonzero members, so
  `{a | support(cb_pou γ a) ∩ e_γ ≠ ∅}` is finite.
- **`x ∈ Skeleton X n`:** by `pou_n.locallyFinite`, there is a neighborhood
  `V` of `x` in `Skeleton X n` with
  `F = {a | support(pou_n.toFun a) ∩ V ≠ ∅}` finite. For `a ∉ F`,
  `pou_n.toFun a = 0` on `V`. Apply Step 6 to get `V'` open in
  `Skeleton X (n+1)` containing `x`, with `pou_succ_fun a = 0` on `V'` for
  all `a ∉ F`. Hence `{a | support(pou_succ_fun a) ∩ V' ≠ ∅} ⊆ F`.

---

## Step 8 — Assemble the result

**Target goal.** Package everything into the existential.

**How (~5 lines).**

```lean
exact ⟨⟨pou_succ_fun, nonneg_proof, sum_proof, lf_proof, sub_proof⟩,
       restriction_proof, zero_extension_proof⟩
```
