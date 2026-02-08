# Cell Complex (Lean)

This project formalizes core definitions and theorems about CW cell complexes in Lean, following the standard topology development in Mathlib. The original theory comes from Introduction to Topological Manifolds by John M. Lee. The contents on cell complexes are transcripted in docs/textboox_transcripted.md

## Textbook correspondences 

Mappings from `docs/textbook_transcripted.md` to Lean theorems in `STCC/`:

- Proposition 5.2.1 (coherent topologies) → `continuous_of_coherent`, `quotient_of_choherent` in `STCC/Basic.lean`
- Proposition 5.4 (locally finite implies CW) → `cw_of_locally_finite` in `STCC/CellComplex.lean`
- Proposition 5.5 (top-dimensional cells are open) → `open_cell_of_finite_dim` in `STCC/CellComplex.lean`
- Theorem 5.6 (subcomplexes are closed and CW) → `cw_sub_cell_complex`, `sub_cw_cell_complex_closed` in `STCC/CellComplex.lean`
- Theorem 5.11 (connectedness characterization) → `connected_1_skeleton_of_connected`, `path_connected_of_connected_skeleton` in `STCC/TopologicalProperties.lean`
- Lemma 5.12 (cell closure in finite subcomplex) → `cell_colsure_subset_finite_sub_complex` in `STCC/TopologicalProperties.lean`
- Lemma 5.13 (discrete subsets) → `subset_discrete_iff_cell_inter_finite` in `STCC/TopologicalProperties.lean`
- Theorem 5.14 (compactness characterization) → `compact_iff_closed_and_subset_finite_sub_complex` in `STCC/TopologicalProperties.lean`
- Corollary 5.15 (compact iff finite) → `compact_space_iff_finite` in `STCC/TopologicalProperties.lean`
- Proposition 5.16 (locally compact iff locally finite) → `cw_locally_finite_iff_locally_compact` in `STCC/TopologicalProperties.lean`
- Lemma 5.17 (quotient map from disjoint union of cells) → `quotient_sigma_cb_map` in `STCC/Construction.lean`
- Proposition 5.18 (skeleton via attaching n-cells) → `cell_attached_to_sknp1_homeomorphic` (and helpers like `skn_sum_cnp1_to_sknp1`) in `STCC/Construction.lean`
- Theorem 5.20 (CW Construction Theorem) → `instCWConstructorSkeletonCW0` and related constructors in `STCC/Construction.lean`

## Project Structure

- `STCC/Basic.lean`  
  Elementary constructions on balls, closed balls, and spheres; inner/boundary maps; separation functions on convex sets; extension from sphere to closed ball; and coherence/adjunction primitives.
- `STCC/CellComplex.lean`  
  The main definition of a cell complex (`CellComplexClass`), characteristic maps, skeletons, subcomplexes, and CW-complex (`CWComplexClass`).
- `STCC/TopologicalProperties.lean`  
  Connectivity and compactness results for skeletons and CW complexes, plus finite subcomplex and local compactness criteria.
- `STCC/Construction.lean`  
  Constructions of skeletons and attaching spaces, quotient-map facts, and inductive CW construction theorems.

## Building

This is a standard Lake project. From the repository root:

```
lake build
```

If you are new to Lean, you can open `STCC.lean` in the editor to browse the imports.
