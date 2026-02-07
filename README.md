# Cell Complex (Lean)

This project formalizes core definitions and theorems about CW cell complexes in Lean, following the standard topology development in Mathlib. The code focuses on characteristic maps, cell closures, skeletons, and CW-complex properties such as local finiteness, compactness criteria, and connectivity.

## Project Structure

- `STCC/Basic.lean`  
  Elementary constructions on balls, closed balls, and spheres; inner/boundary maps; separation functions on convex sets; extension from sphere to closed ball; and coherence/adjunction primitives.
- `STCC/CellComplex.lean`  
  The main definition of a cell complex (`CellComplexClass`), characteristic maps, skeletons, subcomplexes, and CW-complex (`CWComplexClass`).
- `STCC/TopologicalProperties.lean`  
  Connectivity and compactness results for skeletons and CW complexes, plus finite subcomplex and local compactness criteria.
- `STCC/Construction.lean`  
  Constructions of skeletons and attaching spaces, quotient-map facts, and inductive CW construction theorems.

## Important Definitions

### Basic geometric sets (`STCC/Basic.lean`)
- `b n` — open unit ball in `EuclideanSpace ℝ (Fin n)`.
- `cb n` — closed unit ball.
- `sph n` — unit sphere.
- `cb_inner` / `cb_boundary` — inner and boundary subsets of `cb n` via `b_to_cb` and `sph_to_cb`.
- `cb_inner_map` / `cb_boundary_map` — restriction of a map on `cb n` to its inner or boundary part.
- `sep_fun` — a separation function on convex sets that is 0 on assigned point and 1 on boundary. This is used in proving Hausdorff property.
- `cb_extension` — extension of a function on the sphere to the closed ball.
- `IsCoeherent` — a family `B : Set (Set X)` is coeherent if it covers `X` and a set is open in `X` iff all its preimages in each `b ∈ B` are open in `b` (subspace criterion).
- `AdjointSpace` — A mechanism for gluing 2 space X and Y with a subset A of Y and a map f: A → X.

### Cell complexes (`STCC/CellComplex.lean`)
- `CellComplexClass X` — a cell complex on a Hausdorff space `X`, consisting of:
  - a set of cells `sets`,
  - dimension function `dim_map`,
  - characteristic maps `characteristic_map`,
  - axioms: nonempty cells, pairwise disjoint cells, covering, and boundary image in lower-dimensional cells.
- `CWComplexClass X` — a Cell Complex is CW Complex if each cell closure is covered by finitely many cells (`closure_finite`) and the family of cell closures is coeherent.
- `SubCellComplex X` — a subset `carrier ⊆ X` such that each cell is either contained in it or disjoint from it, and if a cell is contained, so is its closure.
- `Skeleton X n` — the subcomplex whose carrier is the union of all cells with `dim_map ≤ n`, i.e. `⋃ s, ⋃ (C.dim_map s ≤ n), s`.
- `FiniteCellComplex` — the finiteness predicate: `C.sets` is finite (i.e. there are finitely many cells).

### Attachments and quotient constructions (`STCC/Construction.lean`)
- `CellAttached` — adjunction space used to attach `n`-cells to a subspace.
- `CellOfDim n` and `characteristic_cn` — cells of fixed dimension and their characteristic maps.

## Selected Theorems (by file)

### `STCC/Basic.lean`
- `b_closure_eq_cb` — closure of an open ball is the closed ball.
- `cb_contractible`, `cb_path_connected` — closed balls are contractible and path connected.
- `cb_inner_open`, `cb_boundary_eq_inner_compl` — inner/boundary decomposition of `cb n`.

### `STCC/CellComplex.lean`
- `cell_compact` — closures of cells are compact (Hausdorff assumption used).
- `characteristic_map_range` — characteristic map image equals cell closure.
- `cell_closure_connected`, `cell_closure_path_connected` — closures of cells are (path) connected.
- `cell_boundary_cover` — boundary of a cell lies in lower-dimensional cells.
- `cell_open_in_closure`, `cell_boundary_closed` — openness of cells in their closure, closedness of boundaries.
- `skeleton0_discrete` — the `0`-skeleton has discrete topology.
- `boundary_covered_by_finite_cells` — boundary of a cell covered by finitely many lower-dimensional cells.

### `STCC/TopologicalProperties.lean`
- `connected_1_skeleton_of_connected` — 1-skeleton is preconnected under connectedness assumptions.
- `path_connected_of_connected_skeleton` — connected skeleton implies path connectedness of `X`.
- `compact_iff_closed_and_subset_finite_sub_complex` — compactness criterion via finite subcomplex.
- `compact_space_iff_finite` — CW complex is compact iff it is finite.
- `cw_locally_finite_iff_locally_compact` — local finiteness vs. weak local compactness.

### `STCC/Construction.lean`
- `quotient_sigma_cb_map` — characteristic maps form a quotient map from a sigma-type of cells.
- `skn_sum_cnp1_to_sknp1` and `cell_attached_to_sknp1` — attaching `(n+1)`-cells to build the `(n+1)`-skeleton.
- `instCWConstructorCWComplexClass` — CW construction yields a CW complex.

## How to Read the Development

1. Start in `STCC/Basic.lean` for the ball/sphere machinery used in characteristic maps.
2. Move to `STCC/CellComplex.lean` to see the axioms of a cell complex and derived properties.
3. Use `STCC/TopologicalProperties.lean` for global properties (connectedness, compactness).
4. Check `STCC/Construction.lean` for quotient and attachment constructions of skeletons.

## Building

This is a standard Lake project. From the repository root:

```
lake build
```

If you are new to Lean, you can open `STCC.lean` in the editor to browse the imports.
