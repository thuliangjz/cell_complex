# Detailed Proof Plan: `coeherent` for CWConstructorSkeleton (n+1)

## Goal
Prove that if `CWConstructorSkeleton n` is a `CWComplexClass`, then `CWConstructorSkeleton (n+1)` is also a `CWComplexClass`. The `closure_finite` property is already proved; we need to prove the `coeherent` property.

## Target Statement
```lean
IsCoeherent {closure s | s ∈ sub_cell_complex_sets (CWConstructorSkeleton (n + 1))}
```

## Key Theorem to Use
From `Basic.lean:1167`:
```lean
theorem coeherent_of_closed_crit_and_cover' {X: Type*} [TopologicalSpace X] {B: Set (Set X)}
  (h_close_crit': ∀ s : Set X, (∀ b ∈ B, IsClosed (((↑): b → X) ⁻¹' s)) → IsClosed s)
  (h_cover: ⋃₀ B = Set.univ) : IsCoeherent B
```

So we must prove:
1. **Cover**: `⋃₀ {closure s | s ∈ sub_cell_complex_sets Y_n1} = Set.univ` (where Y_n1 = CWConstructorSkeleton (n+1))
2. **Closed criterion**: For any `B : Set Y_n1`, if `∀ b ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}, IsClosed (((↑): b → Y_n1) ⁻¹' B)`, then `IsClosed B`

---

## Part 1: Cover Condition ✓

**Claim**: `⋃₀ {closure s | s ∈ sub_cell_complex_sets Y_n1} = Set.univ`

**Implemented as**: `sub_cell_complex_closure_cover` in `CellComplex.lean` (works for any `SubCellComplex Y`).

**Proof outline**:
- We have `sub_cell_complex_set_cover Y_n1 : ⋃₀ sub_cell_complex_sets Y_n1 = Set.univ`
- For each cell `s`, we have `s ⊆ closure s`
- Thus `⋃₀ sub_cell_complex_sets Y_n1 ⊆ ⋃₀ {closure s | s ∈ sub_cell_complex_sets Y_n1}`
- So the right-hand side covers `Set.univ`

*This should be straightforward; may already exist as a lemma.*

---

## Part 2: Closed Criterion (Main Work)

**Setup**:
- Let `Y_n := CWConstructorSkeleton n`, `Y_n1 := CWConstructorSkeleton (n+1)`
- `Y_n1` has carrier `CWC.Fsk (n+1)` with subspace topology from `X`
- **Key structural fact**: `Fsk (n+1)` is homeomorphic to `AdjointSpace (Fsk n) (Ff n)` via `Fφ n`
- The adjoint space is the quotient of `(Fsk n) ⊕ Σ_{i : Fι n} (cb (n+1))` with boundary identified

**Quotient map**: The map
```
f : (Fsk n) ⊕ Σ(cb (n+1)) → Fsk (n+1)
```
is the composition of the quotient map `adj_proj` and `Fφ n`. By `Fφ_heomorph`, this is a quotient map (even a homeomorphism when we consider the full adjoint space).

**Strategy**: A set `B ⊆ Y_n1` is closed in `Y_n1` iff its preimage under the quotient map `f` is closed. The preimage decomposes into two parts:
1. The part coming from `Fsk n` (left summand)
2. The part coming from each `(n+1)`-cell (right summand, one copy of `cb (n+1)` per index `i`)

---

### Variable Setup (before Step 2.1)

**Goal context** (from `coeherent_of_closed_crit_and_cover'`):
- `B : Set Y_n1` — the set we need to show is closed
- `hB : ∀ b ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}, IsClosed (((↑): b → Y_n1) ⁻¹' B)`

**Introduce**:
```
Y_n   := CWConstructorSkeleton n
Y_n1  := CWConstructorSkeleton (n + 1)
ih    : CWComplexClass Y_n
g_n1  : Y_n1 → X := (↑)
```

**AdjointSpace parameters** (for `n : ℕ`):
- `A     := {x : Σ (Fι n) (cb (n+1)) | x.2 ∈ cb_boundary}` — the boundary set (CellAttached_boundary)
- `X_adj := CWC.Fsk n`, `Y_adj := Σ (Fι n) (cb (n+1))`
- `f_adj := CWC.Ff n : A → CWC.Fsk n`

**Key maps**:
- `adj_proj A (Ff n) : (Fsk n) ⊕ Σ(Fι n)(cb (n+1)) → AdjointSpace A (Ff n)`
- `left_adj_proj A (Ff n) : Fsk n → AdjointSpace A (Ff n)`
- `right_adj_proj A (Ff n) : Aᶜ → AdjointSpace A (Ff n)` where `Aᶜ = {x | x.2 ∉ cb_boundary}`
- `Fφ n : AdjointSpace A (Ff n) → Fsk (n+1)` — homeomorphism
- `cell_define_map n i : cb (n+1) → X` — characteristic map for (n+1)-cell indexed by `i`

**Identifications**:
- `Y_n1` has carrier `Fsk (n+1)`; topologically `Y_n1 = Fsk (n+1)` as subspace of `X`
- `Fφ_fix n`: `(Fφ n) ∘ left_adj_proj = inclusion Fsk n → Fsk (n+1)`
- `left_adj_right_adj_cover`: `range (left_adj_proj) ∪ range (right_adj_proj) = univ`

**Useful lemmas**: `adj_proj_quotient`, `Fφ_heomorph`, `sigma_boundary_closed n` (for `IsClosed A`), `isClosed_sum_iff`

---

### Step 2.1: Express Closedness via Quotient Preimage

**Lemma to use**: For a quotient map `q : Z → Y_n1`, a set `B ⊆ Y_n1` is closed iff `q ⁻¹' B` is closed in `Z`.

**Construction of the quotient source**:
- `Z = AdjointSpace (Fsk n) (Ff n)` — this is the domain before applying `Fφ n`
- The map `Subtype.val ∘ Fφ n : AdjointSpace → Fsk (n+1)` gives the quotient structure
- Actually: `Fφ n` itself is a homeomorphism `AdjointSpace ≃ₜ Fsk (n+1)`, so the topology on `Fsk (n+1)` is the same as that on `AdjointSpace`
- The topology on `AdjointSpace` is the quotient topology from `(Fsk n) ⊕ Σ(...)` via `adj_proj`

**Therefore**: `B ⊆ Fsk (n+1)` is closed iff `(adj_proj ⁻¹' (Fφ n ⁻¹' B))` is closed in `(Fsk n) ⊕ Σ(...)`.

Since `Fφ n` is a homeomorphism, `Fφ n ⁻¹' B` is just the preimage. Let `B' = (Fφ n)⁻¹' B` as a subset of `AdjointSpace`. Then `B` is closed iff `B'` is closed in `AdjointSpace` iff `adj_proj ⁻¹' B'` is closed in the disjoint union.

**Decomposition of the preimage**:
- `adj_proj ⁻¹' B' = (Sum.inl ⁻¹' (adj_proj ⁻¹' B')) ∪ (Sum.inr ⁻¹' (adj_proj ⁻¹' B'))`
- **Left part** `L := left_adj_proj ⁻¹' B'` — preimage from `Fsk n`
- **Right part** `R := right_adj_proj ⁻¹' (B' restricted to right_adj_proj range)` — preimage from `Σ (Fι n) (cb (n+1))` minus boundary

The disjoint union is closed iff both `L` and `R` are closed (by `isClosed_sum_iff` or similar).

---

### Step 2.2: Left Part — B ∩ Fsk n is Closed in Fsk n

**Claim**: The preimage of `B` under the left inclusion (from `Fsk n` into `Fsk (n+1)`) equals `B ∩ Fsk n` when viewed in `Y_n1`.

**More precisely**:
- `left_adj_proj` embeds `Fsk n` into `AdjointSpace`
- `Fφ n ∘ left_adj_proj` equals the inclusion `Fsk n → Fsk (n+1)` (by `Fφ_fix`: it sends `x` to `⟨x.1, Fsk_chain x.2⟩`, i.e. the same point in the larger skeleton)
- So `(Fφ n ∘ left_adj_proj) ⁻¹' B = B ∩ Fsk n` (as subsets of `Fsk n`)

**What we need**: `B ∩ Fsk n` is closed in `Fsk n` (with its subspace topology from `X`).

**How to get it**: Use the **inductive hypothesis** that `Y_n = CWConstructorSkeleton n` is a `CWComplexClass`, hence has `coeherent`:
- `B_n := {closure t | t ∈ sub_cell_complex_sets Y_n}` is coherent
- The closed criterion says: if for every `b ∈ B_n`, `(↑)⁻¹' (B ∩ Fsk n)` is closed in `b`, then `B ∩ Fsk n` is closed in `Fsk n`

**Observation**: The cells of `Y_n1` that lie entirely in `Fsk n` are exactly the cells of `Y_n`. For such a cell `s`, `closure s` (in `Y_n1`) equals `closure s` (in `Y_n`), because `Fsk n` is closed in `Fsk (n+1)` and `closure(s) ⊆ Fsk n` for cells of dimension ≤ n.

**Our assumption**: For every `b ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}`, `(↑)⁻¹' B` is closed in `b`.

**For cells in Y_n**: When `b = closure s` with `s` a cell in `Y_n`, we have `(↑)⁻¹' B = B ∩ b` closed in `b`. So `B ∩ closure(s)` is closed in `closure(s)` for every cell `s` of `Y_n`.

**By coeherent of Y_n**: The family `{closure t | t ∈ sub_cell_complex_sets Y_n}` satisfies the closed criterion. The set `B ∩ Fsk n` (as a subset of `Y_n`) satisfies: for every `b` in that family, `(↑)⁻¹' (B ∩ Fsk n) = (B ∩ Fsk n) ∩ b = B ∩ b` is closed in `b` (since `b ⊆ Fsk n` and we assume `B ∩ b` closed in `b`). Hence `B ∩ Fsk n` is closed in `Fsk n`. ✓

---

### Step 2.2 — Detailed Decomposed Proof Plan (for Lean)

Each sub-step is designed to be ~10 lines or less.

**Goal**: Prove `IsClosed (Sum.inl ⁻¹' (adj_proj A (CWC.Ff n) ⁻¹' ((CWC.Fφ n) ⁻¹' B)))` in the sum topology on `(CWC.Fsk n) ⊕ Σ (CWC.Fι n) (cb (n+1))`.

**Step 2.2.1 — Relate left preimage to left_adj_proj** (~5 lines)
- **Goal type**: `IsClosed (Sum.inl ⁻¹' (adj_proj A (CWC.Ff n) ⁻¹' ((CWC.Fφ n) ⁻¹' B)))`
- **After step**: `IsClosed ((left_adj_proj A (CWC.Ff n)) ⁻¹' ((CWC.Fφ n) ⁻¹' B))` (same Prop, rewritten)
- Use `left_adj_proj = (adj_proj A (CWC.Ff n)) ∘ Sum.inl`
- Rewrite: `Sum.inl ⁻¹' (adj_proj ⁻¹' ((Fφ n) ⁻¹' B)) = (left_adj_proj A (CWC.Ff n)) ⁻¹' ((CWC.Fφ n) ⁻¹' B)`
- By `Set.preimage_comp`: `(f ∘ g) ⁻¹' S = g ⁻¹' (f ⁻¹' S)`, so this is `(Fφ n ∘ left_adj_proj) ⁻¹' B`

**Step 2.2.2 — Apply Fφ_fix to identify the map** (~8 lines)
- **Goal type**: `IsClosed ((left_adj_proj A (CWC.Ff n)) ⁻¹' ((CWC.Fφ n) ⁻¹' B))`
- **After step**: `IsClosed (incl ⁻¹' B)` where `incl : Y_n → Y_n1` (set type: `Set (CWC.Fsk n)`)
- `CWC.Fφ_fix n`: `(CWC.Fφ n) ∘ (left_adj_proj A (CWC.Ff n)) = fun x => ⟨x.1, (CWC.Fsk_chain n) x.2⟩`
- So the preimage equals `{x : CWC.Fsk n | ⟨x.1, Fsk_chain n x.2⟩ ∈ B}`
- Define `incl : Y_n → Y_n1 := fun y => ⟨y.1, Fsk_incl (Nat.le_succ n) y.2⟩`
- Show the preimage equals `incl ⁻¹' B` as a subset of `CWC.Fsk n`
- Note: `Y_n` and `CWC.Fsk n` are the same underlying type (carrier); `incl` is the inclusion into `Y_n1`

**Step 2.2.3 — Translate to closure-in-Fsk-n** (~10 lines)
- **Goal type**: `IsClosed (incl ⁻¹' B)` (in the topology of `CWC.Fsk n` as the left summand)
- **After step**: New goal `∀ b ∈ {closure t | t ∈ sub_cell_complex_sets Y_n}, IsClosed (((↑) : b → Y_n) ⁻¹' (incl ⁻¹' B))`
- Use `apply closed_crit_of_coeherent ih.coeherent` (or `suffices` with this forall)
- `closed_crit_of_coeherent` has type: `∀ s : Set Y_n, (∀ b ∈ B, IsClosed (((↑) : b → Y_n) ⁻¹' s)) → IsClosed s`
- Here `B` in the lemma = `{closure t | t ∈ sub_cell_complex_sets Y_n}` (the coherent family)
- We need `IsClosed (incl ⁻¹' B)` in `Y_n`; `Y_n` has the same topology as `CWC.Fsk n` (both subspace from X)

**Step 2.2.4 — Relate Y_n cell closures to Y_n1** (~10 lines)
- **Goal type** (as a `have`): For `t ∈ sub_cell_complex_sets Y_n`, show `incl '' t ∈ sub_cell_complex_sets Y_n1` and that `closure (incl '' t)` (in Y_n1) equals `closure t` (in Y_n) as sets
- Type: `t ∈ sub_cell_complex_sets Y_n → incl '' t ∈ sub_cell_complex_sets Y_n1 ∧ closure (incl '' t) = closure t`
- For each `b = closure t` with `t ∈ sub_cell_complex_sets Y_n`, we get `b ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}` (via `incl '' t ∈ sub_cell_complex_sets Y_n1`)
- Prove: `g_n1 '' (incl '' t) = g_n '' t` so `(↑) '' (incl '' t) ∈ instCWConstructorCellComplexClass.sets`

**Step 2.2.5 — Apply hB to get closedness in each b** (~8 lines)
- **Goal type**: `∀ b ∈ {closure t | t ∈ sub_cell_complex_sets Y_n}, IsClosed (((↑) : b → Y_n) ⁻¹' (incl ⁻¹' B))`
- **For each** `b` (with `b = closure t` for some `t`): Goal `IsClosed (((↑) : b → Y_n) ⁻¹' (incl ⁻¹' B))`
- From hB: for `b' = closure (incl '' t) ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}`, we have `IsClosed (((↑) : b' → Y_n1) ⁻¹' B)`
- Show `((↑) : b → Y_n) ⁻¹' (incl ⁻¹' B) = ((↑) : b → Y_n1) ⁻¹' B` (when `b = closure t = closure (incl '' t)`)
- Then `rw [this]` and exact `hB b' hb'`

**Step 2.2.6 — Apply closed_crit_of_coeherent** (~5 lines)
- **Goal type**: `IsClosed (incl ⁻¹' B)` (back to the reduced goal from 2.2.2)
- We have shown the antecedent of `closed_crit_of_coeherent ih.coeherent (incl ⁻¹' B)`
- Apply `closed_crit_of_coeherent ih.coeherent (incl ⁻¹' B)` to get `IsClosed (incl ⁻¹' B)` in `Y_n`
- This equals `IsClosed (incl ⁻¹' B)` in `CWC.Fsk n` (same space, same topology via `Tsk_eq_subspace`)

**Step 2.2.7 — Handle type equality (Tsk = subspace)** (~5 lines)
- **Goal type**: Still `IsClosed (incl ⁻¹' B)` but we must ensure the topology used is the one expected by `isClosed_sum_iff`
- `isClosed_sum_iff` expects: for the left summand, `IsClosed (Sum.inl ⁻¹' S)` where the closedness is in the topology of `CWC.Fsk n`
- After 2.2.1 rewrite, the set equals `incl ⁻¹' B`; after 2.2.6 we have it closed in `Y_n` = `CWC.Fsk n` (with `Tsk n = subspace`)
- Use `Tsk_eq_subspace n` if needed to align `instTopologicalSpaceSubtype` (on the subtype `Fsk n`) with `CWC.Tsk n`

**Suggested lemma to extract** (optional, for clarity):
```lean
lemma left_preimage_eq_incl_preimage (n : ℕ) (B : Set (CWConstructorSkeleton (n+1))) :
  Sum.inl ⁻¹' (adj_proj A (CWC.Ff n) ⁻¹' ((CWC.Fφ n) ⁻¹' B)) =
  (fun y => ⟨y.1, Fsk_incl (Nat.le_succ n) y.2⟩) ⁻¹' B := ...
```

**Lean context reminder** (at line 2529):
- `Y_n`, `Y_n1`, `A`, `B`, `hB` are in scope
- `ih : CWComplexClass (CWConstructorSkeleton n)`
- Goal: `IsClosed (Sum.inl ⁻¹' (adj_proj A (CWC.Ff n) ⁻¹' ((CWC.Fφ n) ⁻¹' B)))`
- Key: The LHS lives in `CWC.Fsk n`; `Sum.inl` embeds `Fsk n` into the disjoint union

---

### Step 2.3: Right Part — Preimage Under Each (n+1)-Cell's Characteristic Map is Closed

**Overall goal**: `IsClosed (Sum.inr ⁻¹' (adj_proj A (CWC.Ff n) ⁻¹' ((CWC.Fφ n) ⁻¹' B)))`  
(LHS lives in `Σ (i : CWC.Fι n), cb (n+1)` with the sigma topology.)

**Claim**: For each `i : Fι n`, the preimage of `B` under the characteristic map of the `(n+1)`-cell indexed by `i` is closed in `cb (n+1)`.

**Setup**:
- The `(n+1)`-cell is `e_i := Set.range (cell_define_map n i)`
- Its closure in `X` (and in `Y_n1`) is `closure e_i`
- The characteristic map `φ_i : cb (n+1) → X` (or `→ closure e_i`) sends the closed ball onto `closure e_i`
- `φ_i` factors through `right_adj_proj` and `Fφ n`

**Our assumption**: For `b = closure e_i` (which is in `{closure s | s ∈ sub_cell_complex_sets Y_n1}`), we have `(↑)⁻¹' B` is closed in `b`, i.e. `B ∩ closure e_i` is closed in `closure e_i` (with subspace topology).

**Key**: The characteristic map `φ_i : cb (n+1) → closure e_i` is continuous and surjective onto `closure e_i`. So:
- `φ_i ⁻¹' (B ∩ closure e_i) = φ_i ⁻¹' B` (since `φ_i` maps into `closure e_i`)
- `B ∩ closure e_i` is closed in `closure e_i` by assumption
- Continuous preimage of closed is closed ⇒ `φ_i ⁻¹' B` is closed in `cb (n+1)` ✓

---

#### Detailed Sub-Steps for Step 2.3 (each ~15 lines)

**Step 2.3.1 — Reduce to sigma topology via `isClosed_sigma_iff`** (~10 lines)

- **Action**: `rw [isClosed_sigma_iff]` and `intro i`.
- **Target type after**: `∀ i : CWC.Fι n, IsClosed ((Sigma.mk i) ⁻¹' (Sum.inr ⁻¹' (adj_proj A (CWC.Ff n) ⁻¹' ((CWC.Fφ n) ⁻¹' B))))`
- **Rationale**: The domain of `Sum.inr` is `Σ (i : CWC.Fι n), cb (n+1)`. In the sigma topology, a set is closed iff its intersection with each fiber (preimage under `Sigma.mk i`) is closed in `cb (n+1)`.

---

**Step 2.3.2 — Rewrite i-th preimage to characteristic-map preimage** (~15 lines)

- **Action**: Show that  
  `(Sigma.mk i) ⁻¹' (Sum.inr ⁻¹' (adj_proj ⁻¹' (Fφ ⁻¹' B))) = (fun x : cb (n+1) => (CWC.Fφ n) (adj_proj A (CWC.Ff n) (Sum.inr ⟨i, x⟩))) ⁻¹' B`.
- **Target type**: After `ext x; simp` (or equivalent), the goal becomes an equality of sets. After `rw [this]`, the goal is  
  `IsClosed ((fun x => (CWC.Fφ n) (adj_proj A (CWC.Ff n) (Sum.inr ⟨i, x⟩))) ⁻¹' B)`.
- **Key lemma**: `pre_characteristic_map n ⟨i, x⟩ = Subtype.val ((CWC.Fφ n) (adj_proj (Sum.inr ⟨i, x⟩)))`, and `(CWC.Fφ n) (adj_proj …)` has type `Fsk (n+1)` so lies in `B : Set Y_n1` when considered as subtype.
- **Note**: The RHS is exactly `φ_i ⁻¹' B` where `φ_i` is the characteristic map into `Fsk (n+1)`.

---

**Step 2.3.3 — Show closure(e_i) ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1} and get hB** (~15 lines)

- **Action**: Prove  
  `closure (Set.range (cell_define_map n i)) ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}`.
- **Target type**: `closure (g_n1 ⁻¹' (Set.range (cell_define_map n i))) ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}`  
  or equivalently: `∃ t, t ∈ sub_cell_complex_sets Y_n1 ∧ closure t = closure (Set.range (cell_define_map n i))`.
- **Steps**:  
  1. `Set.range (cell_define_map n i) ∈ cell_sets` via `cell_define_map_range_in_sets`.  
  2. Define `t := g_n1 ⁻¹' (Set.range (cell_define_map n i))` so that `g_n1 '' t = Set.range (cell_define_map n i)`.  
  3. Then `t ∈ sub_cell_complex_sets Y_n1` (from `sub_cell_complex_sets` def: `(↑) '' t ∈ C.sets`).  
  4. Show `closure t = closure (Set.range (cell_define_map n i))` (as subsets of `Y_n1`/`X`).
- **Then**: `have hB_i := hB (closure t) ⟨t, ht, rfl⟩` to get  
  `IsClosed (((↑) : closure t → Y_n1) ⁻¹' B)`.

---

**Step 2.3.4 — Define φ_i' : cb (n+1) → closure(e_i) and factor φ_i** (~15 lines)

- **Action**: Define `φ_i' : cb (n+1) → closure (Set.range (cell_define_map n i))` by  
  `φ_i' x := ⟨(CWC.Fφ n) (adj_proj A (CWC.Ff n) (Sum.inr ⟨i, x⟩)), proof_that_image_in_closure⟩`.
- **Target type**: `∀ x : cb (n+1), (CWC.Fφ n) (adj_proj A (CWC.Ff n) (Sum.inr ⟨i, x⟩)) ∈ closure (Set.range (cell_define_map n i))`.
- **Use**: `cell_n_in_Fsk_np1`, `cell_define_map`, `pre_characteristic_map`, and that the characteristic map sends `cb` onto the closure of the cell.
- **Show**: `φ_i = (↑) ∘ φ_i'` where `(↑) : closure(e_i) → Y_n1`, so  
  `φ_i ⁻¹' B = φ_i' ⁻¹' (((↑) : closure(e_i) → Y_n1) ⁻¹' B)`.

---

**Step 2.3.5 — Prove continuity of φ_i'** (~12 lines)

- **Target type**: `Continuous φ_i'`.
- **Method**: `φ_i'` is `Subtype.val ∘ (CWC.Fφ n) ∘ adj_proj ∘ Sum.inr ∘ (fun x => ⟨i, x⟩)`. Each factor is continuous: `continuous_subtype_mk`, `(CWC.Fφ_heomorph n).continuous`, `adj_proj` (quotient), `continuous_inr`, `continuous_id`.
- **Alternative**: Use `Continuous.subtype_mk` on the composition into `Fsk (n+1)` with proof that the image lies in `closure (Set.range (cell_define_map n i))`.

---

**Step 2.3.6 — Apply IsClosed.preimage** (~8 lines)

- **Action**: `rw [preimage_comp]` or the equality from 2.3.4, then `exact IsClosed.preimage φ_i'_continuous hB_closed`.
- **Target type**: `IsClosed (φ_i' ⁻¹' (((↑) : closure (Set.range (cell_define_map n i)) → Y_n1) ⁻¹' B))`.
- **From 2.3.3**: `hB_closed : IsClosed (((↑) : closure t → Y_n1) ⁻¹' B)`, and `closure t = closure (Set.range (cell_define_map n i))` so the types match after suitable `convert` or `congr`.
- **Conclusion**: `φ_i ⁻¹' B` is closed in `cb (n+1)`, which is the desired closedness for the i-th summand.

---

**Step 2.3.7 — Handle closure equality (if closure t ≠ closure e_i as types)** (~10 lines, if needed)

- **Issue**: `closure t` (closure in `Y_n1`) vs `closure (Set.range (cell_define_map n i))` (in `X`) may differ as types.
- **Target type**: Align so that `((↑) : closure (Set.range (cell_define_map n i)) → Y_n1) ⁻¹' B` is identified with the set from `hB` (possibly via `closure t` where `t = g_n1 ⁻¹' (Set.range (cell_define_map n i))`).
- **Key**: In `Y_n1`, closure of the cell as a subset of `Y_n1` equals the closure in `X` intersected with `Y_n1`. Since the cell lies in `Fsk (n+1)`, the closures coincide. Use `closure_eq_closure` or similar if available, or prove the equality explicitly.

---

**Summary for Step 2.3**

| Sub-step | Target type / result |
|----------|----------------------|
| 2.3.1 | `∀ i, IsClosed ((Sigma.mk i) ⁻¹' (Sum.inr ⁻¹' …))` |
| 2.3.2 | Preimage equals `(fun x => (CWC.Fφ n) (adj_proj (Sum.inr ⟨i, x⟩))) ⁻¹' B` |
| 2.3.3 | `closure(e_i) ∈ {closure s \| …}` and `hB` gives closedness in `closure(e_i)` |
| 2.3.4 | `φ_i = (↑) ∘ φ_i'` and preimage factorization |
| 2.3.5 | `Continuous φ_i'` |
| 2.3.6 | `IsClosed.preimage` completes the proof |
| 2.3.7 | Resolve type/closure equalities if needed |

**Note**: The `right_adj_proj` part of the quotient corresponds exactly to these characteristic maps (one for each `i`). The preimage we need is the union over `i` of `φ_i ⁻¹' B`, and each is closed. The sigma topology requires closedness in each fiber, which is what we prove. ✓

---

### Step 2.4: Gluing the Two Parts

**Summary**:
1. `B` is closed in `Y_n1` iff its preimage under the quotient map (from `(Fsk n) ⊕ Σ(...)` through `adj_proj` and `Fφ n`) is closed.
2. That preimage splits into:
   - **Left**: `B ∩ Fsk n`, which is closed in `Fsk n` by the inductive hypothesis (coeherent of `Y_n`) and the assumption on `B`.
   - **Right**: For each `i`, `φ_i ⁻¹' B` is closed in `cb (n+1)` by the assumption on `B` and continuity of `φ_i`.
3. By the `isClosed_sum_iff` characterization, the full preimage is closed.
4. Therefore `B` is closed in `Y_n1`. ✓

---

## Part 3: Technical Checklist for the Lean Implementation

### Definitions and Facts to Use
- `Fφ n : AdjointSpace (Fsk n) (Ff n) → Fsk (n+1)` is a homeomorphism (`Fφ_heomorph`)
- `Fφ_fix`: `(Fφ n) ∘ left_adj_proj = inclusion of Fsk n into Fsk (n+1)`
- `left_adj_proj`, `right_adj_proj` decompose the adjoint space
- `cell_define_map n i` and `pre_characteristic_map n` for characteristic maps of `(n+1)`-cells
- `sub_cell_complex_sets Y_n1` and its relation to `cell_sets` of the ambient `instCWConstructorCellComplexClass`
- `closed_in_cwc_iff` for the topology on `Fsk n` as subspace of `X`

### Lemmas That May Be Needed
- Relate `closure s` for `s ∈ sub_cell_complex_sets Y_n1` to cell closures in `X`
- For cells of dimension ≤ n: closure in `Y_n1` = closure in `Y_n` (both equal closure in `X`)
- `isClosed_sum_iff` for the disjoint union
- Quotient topology: closed iff preimage closed (for `adj_proj` and/or `Fφ n`)

### Potential Subtleties
1. **Type equality**: `Y_n1` is `CWConstructorSkeleton (n+1)` which is a `Subtype`; `Fsk (n+1)` is also a subtype of `X`. The coercion `(↑) : Y_n1 → X` and the inclusion `Fsk (n+1) → X` need to be carefully aligned.
2. **Closure in which space**: Closures of cells in `sub_cell_complex_sets Y_n1` are taken in the topology of `Y_n1` (subspace of `X`). For cells in `Fsk n`, this equals closure in `X` (and in `Y_n`) because `Fsk n` is closed.
3. **Coeherent on Y_n**: The inductive hypothesis gives `ih : CWComplexClass (CWConstructorSkeleton n)`. So `ih.coeherent` is `IsCoeherent {closure s | s ∈ sub_cell_complex_sets Y_n}`. We apply `closed_crit_of_coeherent` in the direction: if preimages are closed for all `b`, then the set is closed.
4. **Cover**: The cover `⋃₀ {closure s | s ∈ sub_cell_complex_sets Y_n1} = Set.univ` may need a small proof; it likely follows from `sub_cell_complex_set_cover` and `s ⊆ closure s`.

---

## Summary of Proof Structure

```
coeherent proof for Y_n1:
  apply coeherent_of_closed_crit_and_cover' _ cover
  intro B hB
  -- hB : ∀ b ∈ {closure s | s ∈ sub_cell_complex_sets Y_n1}, IsClosed ((↑)⁻¹' B)

  -- Step 1: B is closed iff its preimage under the quotient map is closed
  rw [closed_iff_preimage_closed_under_quotient]  -- or similar

  -- Step 2: Preimage = left part ∪ right part
  rw [preimage_decomposition]

  -- Step 3: Left part closed (use ih.coeherent)
  apply And.intro
  · exact left_part_closed n ih B hB

  -- Step 4: Right part closed (direct from hB)
  · exact right_part_closed n B hB
```

---

## References

- `Basic.lean:1167`: `coeherent_of_closed_crit_and_cover'`
- `Basic.lean:1145-1148`: `IsCoeherent` structure (`open_crit`, `cover`)
- `Basic.lean:1177`: `closed_crit_of_coeherent`
- `CellComplex.lean:707`: `aux_closed_in_subspace_of_sub_complex_coeherent`
- `CellComplex.lean:787`: `aux_closed_of_sub_complex_coeherent` (uses ambient X's coherent; not directly applicable here)
- `Construction.lean:494`: `Fφ`, `Fφ_fix`, `Fφ_heomorph`
- `Construction.lean:744`: `pre_characteristic_map`, `cell_define_map`
- `Construction.lean:772`: `Fsk n` as image of `left_adj_proj` under `Fφ n`
