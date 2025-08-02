import Mathlib.Topology.Basic
--import Mathlib.Topology.Instances.Real.Defs
import Mathlib.Topology.Constructions
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Basic
import MyProject.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open BigOperators
open Topology
/-
    a cell complex is really about X and its cell decomposition
    note that although each e ∈ sets are homeomorphic to some open ball, it is not necessarily open in X
    use [] for topological space as we do not use it explicit here
-/
namespace Chp5

/-
    in text the T2Space is assumed
    but the definition does not require T2Space
    it is only required for compactness of closure of cells
-/
class CellComplexClass (X: Type*) [TopologicalSpace X] [T2Space X] where
    sets: Set (Set X)
    nonempty: ∀ A ∈ sets, A.Nonempty
    disjoint: sets.Pairwise Disjoint
    cover: ⋃₀ sets = Set.univ
    dim_map: sets → ℕ
    hom: ∀ s: sets, b (dim_map s) ≃ₜ s.1
    characteristic_map:
        (s : sets) → cb (dim_map s) → X
    characteristic_map_continuous: ∀ s: sets, Continuous (characteristic_map s)
    characteristic_map_inner_range: ∀ s:sets, Set.range (cb_inner_map (characteristic_map s)) = s
    characteristic_map_inner_embd:
        ∀ s:sets, IsEmbedding (cb_inner_map (characteristic_map s))
    characteristic_map_boundary: ∀ s: sets,
        Set.range (cb_boundary_map (characteristic_map s)) ⊆
        ⋃ p:sets, ⋃ _:(dim_map p < dim_map s), p.val

namespace CellComplexClass
-- This is the place we need X to be Hausdorff
-- to use the theorem where a compact subset must be closed
-- for general topological space this need not to be true
theorem cell_compact {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] : ∀ s ∈ C.sets, IsCompact (closure s) := by
    intro s hs
    set f := C.characteristic_map ⟨s, hs⟩
    have range_compact: IsCompact (Set.range f) := by
        apply isCompact_range (C.characteristic_map_continuous _)
    apply IsCompact.of_isClosed_subset range_compact isClosed_closure
    -- to prove closure s ⊆ Set.range f
    -- we first prove s ⊆ Set.range f
    -- then we prove Set.range f is closed
    have s_in_range : s ⊆ Set.range f := by
        have : s ⊆ Set.range (cb_inner_map f) := by rw[C.characteristic_map_inner_range ⟨s, hs⟩]
        have : Set.range (cb_inner_map f) ⊆ Set.range f := by
            rintro x ⟨u, rfl⟩
            use ⟨u.1, b_in_cb u.2⟩
            rfl
        tauto
    have range_closed: IsClosed (Set.range f) := by exact IsCompact.isClosed range_compact
    exact (IsClosed.closure_subset_iff range_closed).mpr s_in_range

theorem characteristic_map_range {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] : ∀ s : C.sets, Set.range (C.characteristic_map s) = closure s := by
    intro s
    let n := C.dim_map s
    set f := C.characteristic_map s with f_def
    let inner := @cb_inner n
    have f_closed : IsClosedMap f := by
        apply Continuous.isClosedMap (C.characteristic_map_continuous s)
    have inner_map_rw : cb_inner_map f = f ∘ b_to_cb := by
        ext x
        simp[cb_inner_map, f, b_to_cb]
    have inner_map_range : f '' inner = s := by
        set h := C.characteristic_map_inner_range s
        rw [inner_map_rw, Set.range_comp] at h
        exact h
    have img_subset : f '' (closure inner) ⊆ closure s := by
        rw [←inner_map_range]
        refine image_closure_subset_closure_image ?_
        apply C.characteristic_map_continuous
    have img_include: closure s ⊆ f '' (closure inner) := by
        rw [←inner_map_range]
        apply IsClosedMap.closure_image_subset f_closed inner
    rw [←Set.image_univ, ←cb_inner_closure]
    ext x
    tauto

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]
theorem cell_closure_connected : ∀ s ∈ C.sets, IsConnected (closure s) := by
    intro s hs
    rw [←characteristic_map_range ⟨s, hs⟩]
    let f := C.characteristic_map ⟨s, hs⟩
    rw [←Set.image_univ]
    apply IsConnected.image
    case H => exact isConnected_univ
    case hf => exact continuous_iff_continuousOn_univ.mp (characteristic_map_continuous ⟨s, hs⟩)
theorem cell_closure_path_connected: ∀ s ∈ C.sets, IsPathConnected (closure s) := by
    intro s hs
    rw [←characteristic_map_range ⟨s, hs⟩]
    let f := C.characteristic_map ⟨s, hs⟩
    rw [←Set.image_univ]
    apply IsPathConnected.image
    case hF =>
        rw [←pathConnectedSpace_iff_univ]
        exact cb_path_connected
    case hf => exact characteristic_map_continuous ⟨s, hs⟩
theorem same_cell_of_mem {x: X} {e1 e2: Set X} (he1: e1 ∈ C.sets) (he2: e2 ∈ C.sets) (x_in_e1: x ∈ e1) (x_in_e2: x ∈ e2) : e1 = e2 := by
    by_contra! h
    have : Disjoint e1 e2 := C.disjoint he1 he2 h
    rw [Set.disjoint_iff_inter_eq_empty] at this
    have x_mem_inter: x ∈ e1 ∩ e2 := ⟨x_in_e1, x_in_e2⟩
    rw [this] at x_mem_inter
    exact x_mem_inter
end

theorem characteristic_map_inner_image {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] : ∀ s : C.sets, (C.characteristic_map s) '' cb_inner = s := by
    intro s
    set f := C.characteristic_map s
    rw [←inner_map_range]
    apply C.characteristic_map_inner_range

theorem characteristic_map_cell_preimage {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] : ∀ s : C.sets, (C.characteristic_map s) ⁻¹' s = cb_inner := by
    intro s
    set f := C.characteristic_map s
    have right_incl : ∀y,  y ∈ cb_inner →  f y ∈ s.val := by
        intro y hy
        have : f '' cb_inner ⊆ s := by
            apply subset_of_eq
            rw [←inner_map_range, C.characteristic_map_inner_range s]
        apply this
        use y
    have left_incl: ∀y, f y ∈ s.val → y ∈ cb_inner := by
        intro y hy
        rcases mem_cb_inner_or_boundary y with y_inner | y_boundary
        . exact y_inner
        let hy' := (C.characteristic_map_boundary s) (mem_boundary_map_range_of_mem_boundary f y_boundary)
        rcases hy' with ⟨_, ⟨p, rfl⟩, hhp⟩
        simp at hhp
        have : p ≠ s := by by_contra h; rw [h] at hhp; linarith
        have p_inter_s_empty : p.val ∩ s = ∅ := by
            apply Disjoint.inter_eq
            apply C.disjoint p.prop s.prop
            contrapose! this
            exact SetCoe.ext this
        have p_inter_s_non_empty: p.val ∩ s ≠ ∅ := by
            apply Set.nonempty_iff_ne_empty'.mp ?_
            use f y
            tauto
        contradiction
    ext y
    tauto

theorem cell_boundary_cover {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]: ∀ s : C.sets, closure s.val \ s ⊆ ⋃ p:C.sets, ⋃ _:(C.dim_map p < C.dim_map s), p.val := by
    intro s
    have aux: closure s.val \ s ⊆ Set.range (cb_boundary_map (C.characteristic_map s)) := by
        rw [←C.characteristic_map_range s, ←C.characteristic_map_inner_image s, ←Set.image_univ]
        rw [boundary_map_range, ←cb_boundary_inner_cmpl]
        apply Set.subset_image_diff
    intro x hx
    apply C.characteristic_map_boundary s (aux hx)

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C:CellComplexClass X]
theorem exists_mem_of_cell : ∀ x: X, ∃ e ∈ C.sets, x ∈ e := by
    intro x
    have : x ∈ Set.univ := trivial
    rw [←C.cover] at this
    simp at this
    exact this
end
end CellComplexClass


end Chp5
/-With the CellComplex prefix we will be able to use projection notation like CX.IsFinite-/
--def CellComplex.IsFinite {X: Type*} [TopologicalSpace X] (CX: CellComplex X) : Prop :=
--    ∃ n : ℕ, ∃ f : (Fin n → CX.sets), f.Bijective
namespace Chp5
class CWComplexClass (X: Type*) [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]: Prop where
    closure_finite: ∀ s ∈ C.sets, ∃ ss ⊆ C.sets, ss.Finite ∧ closure s ⊆ ⋃₀ ss
    coeherent: IsCoeherent {closure s | s ∈ C.sets}
instance cw_of_locally_finite {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (hC: LocallyFinite fun s:C.sets ↦ s.val) : CWComplexClass X where
        closure_finite := by
            intro s hs
            have: ∀ x:X, ∃ V:Set X, x ∈ V ∧ IsOpen V ∧ ∃ ss ⊆ C.sets, ss.Finite ∧ V ⊆ ⋃₀ ss := by
                intro x
                rcases hC x with ⟨V₀, hV₀, hFinite⟩
                rw [mem_nhds_iff] at hV₀
                rcases hV₀ with ⟨V, h_v_in_v₀, h_v_open, h_x_in_v⟩
                use V, h_x_in_v, h_v_open
                set t := {i:C.sets | (i.val ∩ V₀).Nonempty}
                set ss := (fun x:C.sets ↦ x.val)'' t
                use ss
                have : ss ⊆ C.sets := by simp[ss]
                have : ss.Finite := by apply Set.Finite.image _ hFinite
                have : V ⊆ ⋃₀ ss := by
                    intro x hx
                    show ∃ u ∈ ss, x ∈ u    -- use show to convert goal with rfl
                    have : ∃ u ∈ C.sets, x ∈ u := by
                        show x ∈ ⋃₀ C.sets
                        rw [C.cover]
                        trivial
                    rcases this with ⟨u, hu₁, hu₂⟩
                    use u
                    have : u ∈ ss := by
                        simp[ss, t, Set.inter_nonempty]
                        tauto
                    tauto
                tauto
            choose fv h_x_in_v h_v_open fss h_ss_all_cell h_ss_finite h_v_in_ss_union using this
            have fv_cover: ∀ t: Set X, t ⊆ ⋃ i, fv i:= by
                intro t
                intro x xt
                rw [Set.mem_iUnion]
                use x, h_x_in_v x
            have : IsCompact (closure s) := by apply C.cell_compact s hs
            rw [isCompact_iff_finite_subcover] at this
            specialize this fv h_v_open (fv_cover _)
            rcases this with ⟨t, ht⟩
            set ss := ⋃₀ (fss '' t)
            have ss_all_cell : ss ⊆ C.sets := by
                apply Set.sUnion_subset
                rintro _ ⟨x, hx, rfl⟩
                apply h_ss_all_cell
            have ss_finite : ss.Finite := by
                apply Set.Finite.sUnion (Set.toFinite (fss '' t))
                rintro _ ⟨x, hx, rfl⟩
                apply h_ss_finite
            have ss_union_contain_closure : (closure s) ⊆ ⋃₀ ss := by
                intro x hx
                simp[ss]
                specialize ht hx
                simp at ht
                rcases ht with ⟨i, hi, h_x_in_fv_i⟩
                specialize h_v_in_ss_union i h_x_in_fv_i
                simp at h_v_in_ss_union
                rcases h_v_in_ss_union with ⟨t₁, h_t₁, h_x_in_t₁⟩
                use t₁, (by use i)
            use ss
        coeherent := by
            have cover: ⋃₀ {closure s | s ∈ C.sets} = Set.univ := by
                have : ∀ x, ∃ s ∈ C.sets, x ∈ s := by
                    simp [←Set.mem_sUnion, C.cover]
                rw [Set.sUnion_eq_univ_iff]
                intro x
                rcases this x with ⟨s, hs, hxs⟩
                use (closure s)
                constructor
                . use s
                have : s ⊆ closure s := by apply subset_closure
                tauto
            refine coeherent_of_closed_crit_and_cover ?_ cover
            intro A
            constructor
            . intro hs b hb
              rw[←compl_compl (Subtype.val ⁻¹' A), isClosed_compl_iff]
              rw[←compl_compl A, isClosed_compl_iff] at hs
              simpa using isOpen_induced hs
            intro h
            rw [←compl_compl A, isClosed_compl_iff, isOpen_iff_forall_mem_open]
            -- note here that {s | s ∈ C.sets} is locally finite also means {closure s | s ∈ C.sets} is locally finite
            have : LocallyFinite fun s:C.sets ↦ closure s.val := by apply LocallyFinite.closure hC
            intro x hx
            rcases this x with ⟨W₀, hW₀, hFinite⟩
            rw [mem_nhds_iff] at hW₀
            rcases hW₀ with ⟨W, h_W_in_W₀, h_W_open, h_x_in_W⟩
            set t := {i:C.sets | (closure i.val ∩ W₀).Nonempty}
            set ss := (fun x:C.sets ↦ closure x.val)'' t
            have ss_finite : ss.Finite := by apply Set.Finite.image _ hFinite
            have W_sub_A_eq: W \ A = W \ (⋃ s ∈ ss, A ∩ s) := by
                calc
                    W \ A = W \ (A ∩ ⋃₀ ss) := by
                        have ss_cover_W : W ⊆ ⋃₀ ss := by
                            intro x hx
                            show ∃ u ∈ ss, x ∈ u
                            have : ∃ u ∈ C.sets, x ∈ u := by
                                show x ∈ ⋃₀ C.sets
                                rw [C.cover]
                                trivial
                            rcases this with ⟨u, hu, hxu⟩
                            use closure u
                            have : x ∈ closure u := subset_closure hxu
                            have : closure u ∈ ss := by
                                simp [ss, t]
                                use u
                                simp [hu]
                                have : x ∈ W₀ := h_W_in_W₀ hx
                                tauto
                            tauto
                        have aux {S₁ S₂ : Set X} (h : S₁ ⊆ S₂) (S₃: Set X) : S₁ \ S₃ = S₁ \ (S₃ ∩ S₂) := by
                            ext x
                            simp
                            tauto
                        apply aux ss_cover_W
                    _     = W \ (⋃ s ∈ ss, A ∩ s) := by ext x; simp
            have substractor_closed: IsClosed (⋃ s ∈ ss, A ∩ s) := by
                have : ⋃ s ∈ ss, A ∩ s = ⋃ s:ss, A ∩ s.val := Set.biUnion_eq_iUnion ss fun x h ↦ A ∩ x
                rw [this]
                have : ∀ s0 : ss, IsClosed (A ∩ s0.val) := by
                    intro s0
                    have : s0.val ∈ {x | ∃ s ∈ C.sets, closure s = x} := by
                        simp
                        rcases s0.prop with ⟨s1, hs1, hs1_closure⟩
                        use s1.val, s1.prop
                    specialize h s0.val this
                    -- we need a lemma here
                    have aux {C1 D: Set X} (hC1: IsClosed C1) (h: IsClosed (((↑): C1 → X) ⁻¹' D)) : IsClosed (D ∩ C1) := by
                        let f : C1 → X := fun s ↦ s.val
                        have : IsClosedEmbedding f := by
                            exact IsClosed.isClosedEmbedding_subtypeVal hC1
                        have cmap: IsClosedMap f := this.isClosedMap
                        have : D ∩ C1 = f '' (f ⁻¹' D) := by
                            ext x
                            simp
                            constructor
                            . rintro ⟨h1, h2⟩
                              use x, h2
                            rintro ⟨x, ⟨h1, h2, rfl⟩⟩
                            simp [f] at *
                            tauto
                        rw [this]
                        exact cmap (f ⁻¹' D) h
                    have: IsClosed s0.val := by
                        rcases this with ⟨s1, hs1, hs1_closure⟩
                        rw [←hs1_closure]
                        apply isClosed_closure
                    apply aux this h
                have inst_ss_finite: Finite ss := by exact ss_finite
                apply isClosed_iUnion_of_finite this
            have W_sub_A_open: IsOpen (W \ A) := by
                rw [W_sub_A_eq]
                exact IsOpen.sdiff h_W_open substractor_closed
            have W_sub_A_not_in_A : W \ A ⊆ Aᶜ := by
                intro x₀
                simp
            have x_in_W_sub_A : x ∈ W \ A := by tauto
            use (W \ A)
end Chp5

namespace Chp5
namespace CellComplexClass
class FiniteDim (X: Type*) [TopologicalSpace X] [T2Space X] [C:CellComplexClass X] : Prop where
    out: (Set.range C.dim_map).Finite
noncomputable def Dim (X: Type*) [TopologicalSpace X] [T2Space X] [C:CellComplexClass X] [h: FiniteDim X] : ℕ := h.out.toFinset.sup id
theorem le_finite_dim {X: Type*} [TopologicalSpace X] [T2Space X] [C:CellComplexClass X] [FiniteDim X] : ∀ e : C.sets, C.dim_map e ≤ Dim X := by
    intro e
    rw [Dim, ←id_eq (C.dim_map e)]
    apply Finset.le_sup
    rw[Set.Finite.mem_toFinset]
    use e
theorem aux_surjective_of_range_eq {X Y Z: Type*} {f: X → Y} {g: Y → Z} (hg: Function.Injective g) (h: Set.range (g ∘ f) = Set.range g) : Function.Surjective f := by
    intro y
    have : g y ∈ Set.range (g ∘ f) := by rw [h]; use y
    rcases this with ⟨x, hx⟩
    have : f x = y := hg hx
    use x
theorem open_cell_of_finite_dim {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] [FiniteDim X]: ∀ s : C.sets, C.dim_map s = Dim X → IsOpen s.val := by
    intro e₀ he₀
    rw [CW.coeherent.open_crit]
    intro ce hce
    rcases hce with ⟨e, he_in_sets, h₀⟩
    cases eq_or_ne e₀.val e
    case inl he_eq_e₀ =>
        set n := C.dim_map ⟨e, he_in_sets⟩ with n_def
        set f0 := C.characteristic_map ⟨e, he_in_sets⟩ with f0_def
        have : ∀ y : cb n, f0 y ∈ ce := by
            intro y
            rw [←h₀, ←characteristic_map_range ⟨e, he_in_sets⟩, ←f0_def]
            use y
        let f1 : cb n → ce := fun y ↦ ⟨f0 y, this y⟩
        let g : ce → X := Subtype.val
        show IsOpen (g ⁻¹' e₀)
        have gf_eq_char: g ∘ f1 = C.characteristic_map ⟨e, he_in_sets⟩ := by
                ext x
                simp [g, f1, f0]
        have f1_quot: IsQuotientMap f1 := by
            have inj_g: Function.Injective g := Subtype.val_injective
            have embd_g: IsEmbedding g := by exact Topology.IsEmbedding.subtypeVal
            have f1_surj: Function.Surjective f1 := by
                apply aux_surjective_of_range_eq inj_g
                rw [gf_eq_char, characteristic_map_range]
                simp [g, h₀]
            apply  IsQuotientMap.of_surjective_continuous f1_surj
            apply (IsEmbedding.continuous_iff embd_g).mpr
            rw [gf_eq_char]
            apply characteristic_map_continuous
        have : (g ∘ f1) ⁻¹' e = cb_inner := by rw [gf_eq_char]; apply characteristic_map_cell_preimage
        rw [Set.preimage_comp, ←he_eq_e₀] at this
        rw [←f1_quot.isOpen_preimage, this]
        exact cb_inner_open
    case inr he_ne_e₀ =>
        have e₀_inter_e_empty: e₀.val ∩ e = ∅ := by
            apply Disjoint.inter_eq
            apply C.disjoint e₀.prop he_in_sets he_ne_e₀
        have e₀_inter_ce_sub_e_boundary: e₀.val ∩ ce ⊆ ce \ e := by
            intro x hx
            have : x ∈ e ∨ x ∈ ce \ e := by
                cases Classical.em (x ∈ e)
                case inl x_in_e => exact Or.inl x_in_e
                case inr x_nin_e => exact Or.inr (Set.mem_diff_of_mem (Set.mem_of_mem_inter_right hx) x_nin_e)
            rcases this with x_in_e | x_in_ce_diff_e
            case inr => exact x_in_ce_diff_e
            case inl =>
                have e₀_eq_diff_e : e₀.val \ e = e₀ := by
                    calc
                        e₀.val \ e = e₀.val \ (e₀ ∩ e) := Eq.symm Set.diff_self_inter
                        _          = e₀                := by rw [e₀_inter_e_empty]; exact Set.diff_empty
                have : x ∈ e₀.val := Set.mem_of_mem_inter_left hx
                rw [←e₀_eq_diff_e] at this
                contrapose! x_in_e
                apply Set.notMem_of_mem_diff this
        have e₀_inter_ce_cover : e₀.val ∩ ce ⊆ ⋃ p:C.sets, ⋃ _ :(C.dim_map p < C.dim_map ⟨e, he_in_sets⟩), p.val := by
            trans ce \ e
            exact e₀_inter_ce_sub_e_boundary
            rw [←h₀]
            apply cell_boundary_cover ⟨e, he_in_sets⟩
        have : ∀ x : X, x ∈ e₀.val ∩ ce → False := by
            intro x hx
            specialize e₀_inter_ce_cover hx
            rw [Set.mem_iUnion₂] at e₀_inter_ce_cover
            rcases e₀_inter_ce_cover with ⟨p, hp, hxp⟩
            have : p ≠ e₀ := by
                by_contra! h_p_eq_e₀
                rw [h_p_eq_e₀] at hp
                have : C.dim_map ⟨e, he_in_sets⟩ ≤ C.dim_map e₀ := by
                    rw [he₀]
                    apply le_finite_dim
                linarith
            have h_p_e₀_empty: p.val ∩ e₀ = ∅ := by
                apply Disjoint.inter_eq
                apply C.disjoint p.prop e₀.prop
                contrapose! this
                exact SetCoe.ext this
            have x_in_e₀ : x ∈ e₀.val := Set.mem_of_mem_inter_left hx
            have : x ∈ e₀.val ∩ p := Set.mem_inter x_in_e₀ hxp
            rw [Set.inter_comm, h_p_e₀_empty] at this
            tauto
        have : e₀.val ∩ ce = ∅ := Set.subset_eq_empty this rfl
        rw [Set.inter_comm, ←Subtype.preimage_coe_eq_empty] at this
        rw [this]
        exact isOpen_empty
end CellComplexClass

namespace CellComplex
end CellComplex

namespace CellComplexClass
noncomputable section

@[ext]
structure SubCellComplex (X:Type*) [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] where
    carrier: Set X
    cell_incl_or_disjoint: ∀ e ∈ C.sets, e ⊆ carrier ∨ Disjoint e carrier
    cell_closure_incl: ∀ e ∈ C.sets, e ⊆ carrier → (closure e) ⊆ carrier

instance {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] : SetLike (SubCellComplex X) X where
    coe := SubCellComplex.carrier
    coe_injective' _ _ := SubCellComplex.ext

namespace SubCellComplex
theorem subset_of_intersect {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) {s: Set X} (hs: s ∈ C.sets) : s ∩ Y.carrier ≠ ∅ → s ⊆ Y.carrier := by
    intro hs₁
    rcases Y.cell_incl_or_disjoint s hs with h1 | h2
    case inl => exact h1
    case inr => contrapose! hs₁;exact h2.inter_eq
end SubCellComplex

def sub_cell_complex_sets {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) : Set (Set Y) := {s | (↑) '' s ∈ C.sets}

def sub_cell_complex_dim_map {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) : sub_cell_complex_sets Y → ℕ := by
    intro e
    let e' := ((↑): Y → X) '' e.1
    have : e' ∈ C.sets := e.2
    exact C.dim_map ⟨e', this⟩

def sub_cell_complex_set_nonempty {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) : ∀ A ∈ sub_cell_complex_sets Y, A.Nonempty := by
    intro s hs
    have : (((↑): Y → X) '' s).Nonempty := C.nonempty _ hs
    exact Set.image_nonempty.mp this

def sub_cell_complex_set_disjoint {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) : (sub_cell_complex_sets Y).Pairwise Disjoint := by
    intro u₁ hu₁ u₂ hu₂ hu₁u₂
    have : (((↑): Y → X) '' u₁) ≠ (↑) '' u₂ := by
        contrapose! hu₁u₂
        rw [←Set.image_eq_image Subtype.val_injective]
        assumption
    have: Disjoint (((↑): Y → X) '' u₁)  ((↑) '' u₂) := by
        exact C.disjoint hu₁ hu₂ this
    exact Disjoint.of_image this

def sub_cell_complex_set_cover {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) : ⋃₀ sub_cell_complex_sets Y = Set.univ := by
    ext y
    simp
    show ∃ t, ((↑): Y → X) '' t ∈ CellComplexClass.sets ∧ y ∈ t
    have aux_cover: ∀ x : X, ∃ e ∈ C.sets, x ∈ e := by
        intro x
        have : x ∈ Set.univ := by trivial
        rw [←C.cover] at this
        rcases this with ⟨e, he, hxe⟩
        use e
    rcases aux_cover y with ⟨e, he, hey⟩
    use ((↑): Y → X) ⁻¹' e
    have : ((↑): Y → X) '' (((↑):Y → X) ⁻¹' e) = e := by
        let f := ((↑): Y → X)
        show f '' (f ⁻¹' e) = e
        ext x
        constructor
        case mp =>
            intro hx
            rcases hx with ⟨y, hy, rfl⟩
            simpa using hy
        case mpr =>
            intro hx
            simp[f]
            have : e ⊆ Y := by
                rcases Y.cell_incl_or_disjoint e he with incl | disj
                case inl =>
                    exact incl
                case inr =>
                    have : ↑y ∈ Y.carrier := by exact y.prop
                    have : ¬ Disjoint e Y.carrier := by rw [Set.not_disjoint_iff];use y
                    contradiction
            exact ⟨hx, this hx⟩
    rw [this]
    simp
    tauto

def sub_cell_complex_hom {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): ∀ s: sub_cell_complex_sets Y, b (sub_cell_complex_dim_map Y s) ≃ₜ s.1 := by
    intro s
    simp[sub_cell_complex_dim_map]
    have aux: s.1 ≃ₜ ((↑): Y → X) '' s.1 := by
        have: IsEmbedding ((↑): Y → X) := Topology.IsEmbedding.subtypeVal
        have hom1: ((↑): Y → X) '' s.1 ≃ₜ Set.range (((↑): Y → X) ∘ ((↑): s.1 → Y)) := by
            apply Homeomorph.setCongr
            ext x
            simp
        have hom2: s.1 ≃ₜ Set.range (((↑): Y → X) ∘ ((↑): s.1 → Y)) := by
            apply Topology.IsEmbedding.toHomeomorph
            apply Topology.IsEmbedding.comp
            <;> exact Topology.IsEmbedding.subtypeVal
        exact hom2.trans (id hom1.symm)
    let bn := b (C.dim_map ⟨Subtype.val '' s.1, s.prop⟩)
    have: bn ≃ₜ ((↑): Y → X) '' s.1 := by apply C.hom
    exact (aux.trans (id this.symm)).symm

def sub_cell_complex_characteristic_g {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) (s: sub_cell_complex_sets Y): cb (sub_cell_complex_dim_map Y s) → closure (((↑): Y → X) '' s.1) := by
    set s' := ((↑): Y → X) '' s.1
    intro p
    let x := C.characteristic_map ⟨s', s.2⟩ p
    have : x ∈ closure s' := by
        rw [←characteristic_map_range ⟨s', s.2⟩]
        use p
    exact ⟨x, this⟩

theorem sub_cell_complex_characteristic_g_continuous {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] {Y: SubCellComplex X} (s: sub_cell_complex_sets Y) : Continuous (sub_cell_complex_characteristic_g Y s) := by
    have : Continuous (Subtype.val ∘ (sub_cell_complex_characteristic_g Y s)) := by
        simp [sub_cell_complex_characteristic_g]
        apply C.characteristic_map_continuous
    apply continuous_induced_rng.mpr this

def sub_cell_complex_characteristic_h {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) (s: sub_cell_complex_sets Y): closure (((↑): Y → X) '' s.1) → Y := by
    set s' := ((↑): Y → X) '' s.1
    have : s' ⊆ Y := by
        have eq1: s' = (↑) '' s.1 := by rfl
        have eq2: (Y:Set X) = ((↑): Y → X) '' Set.univ := by ext x; simp
        rw [eq1, eq2]
        apply Set.image_mono
        simp
    have : closure s' ⊆ Y := by apply Y.cell_closure_incl _ s.2 this
    intro x
    exact ⟨x.1, this x.2⟩

theorem sub_cell_complex_characteristic_h_continuous {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] {Y: SubCellComplex X} (s: sub_cell_complex_sets Y) : Continuous (sub_cell_complex_characteristic_h Y s) := by
    simp [sub_cell_complex_characteristic_h]
    continuity

def sub_cell_complex_characteristic_map {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): (s: sub_cell_complex_sets Y) → cb (sub_cell_complex_dim_map Y s) → Y := by
    intro s
    exact (sub_cell_complex_characteristic_h Y s) ∘ (sub_cell_complex_characteristic_g Y s)

theorem sub_cell_complex_characteristic_map_continuous {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): ∀ s: sub_cell_complex_sets Y, Continuous (sub_cell_complex_characteristic_map Y s) := by
    intro s
    apply Continuous.comp
    <;> simp[sub_cell_complex_characteristic_g_continuous, sub_cell_complex_characteristic_h_continuous]

theorem aux_sub_cell_complex_characteristic_map_coe {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): ∀ s : sub_cell_complex_sets Y, Subtype.val ∘ (sub_cell_complex_characteristic_map Y s) = C.characteristic_map ⟨Subtype.val '' s.1, s.2⟩ := by
    intro s
    ext x
    simp [sub_cell_complex_characteristic_map, sub_cell_complex_characteristic_g, sub_cell_complex_characteristic_h]

-- note here the dim_map results are definitionally equal, if they are proovably equal, then Eq.mp will be required to 'rw' types
theorem aux_sub_cell_complex_characteristic_map_inner {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): ∀ s : sub_cell_complex_sets Y, Subtype.val ∘ (cb_inner_map (sub_cell_complex_characteristic_map Y s)) = cb_inner_map (C.characteristic_map ⟨Subtype.val '' s.1, s.2⟩) := by
    intro s
    rw [←inner_map_comp, aux_sub_cell_complex_characteristic_map_coe]

theorem sub_cell_complex_characteristic_map_inner_range {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X) : ∀ s: sub_cell_complex_sets Y, Set.range (cb_inner_map (sub_cell_complex_characteristic_map Y s)) = s.1 := by
    intro s
    have : Set.range (Subtype.val ∘ (cb_inner_map (sub_cell_complex_characteristic_map Y s))) = Subtype.val '' s.1 := by
        simp [aux_sub_cell_complex_characteristic_map_inner]
        apply C.characteristic_map_inner_range
    rw [Set.range_comp, Set.image_eq_image (Subtype.val_injective)] at this
    exact this

theorem sub_cell_complex_characteristic_map_inner_embd {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): ∀ s: sub_cell_complex_sets Y, IsEmbedding (cb_inner_map (sub_cell_complex_characteristic_map Y s)) := by
    intro s
    rw [←Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal, aux_sub_cell_complex_characteristic_map_inner]
    apply C.characteristic_map_inner_embd

theorem sub_cell_complex_characteristic_map_boundary {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): ∀ s: sub_cell_complex_sets Y, Set.range (cb_boundary_map (sub_cell_complex_characteristic_map Y s)) ⊆ ⋃ p, ⋃ (_ : sub_cell_complex_dim_map Y p < sub_cell_complex_dim_map Y s), p.1 := by
    intro s
    let g: Y → X := Subtype.val
    have aux_carrier_eq_univ: Y.carrier = g '' Set.univ := by
        ext x
        constructor
        case mp => intro h; use ⟨x, h⟩; simp [g]
        case mpr => rintro ⟨x0, hx0, rfl⟩; exact x0.2
    have : g '' Set.range (cb_boundary_map (sub_cell_complex_characteristic_map Y s)) ⊆ g '' (⋃ p, ⋃ (_ : sub_cell_complex_dim_map Y p < sub_cell_complex_dim_map Y s), p.1) := by
        have sub1: g '' Set.range (cb_boundary_map (sub_cell_complex_characteristic_map Y s)) ⊆ ⋃ p', ⋃ (_ : C.dim_map p' < C.dim_map ⟨g '' s.1, s.2⟩), p'.1 := by
            rw [←Set.range_comp, ←boundary_map_comp, aux_sub_cell_complex_characteristic_map_coe]
            apply C.characteristic_map_boundary
        have sub2: g '' Set.range (cb_boundary_map (sub_cell_complex_characteristic_map Y s)) ⊆ Y.carrier := by
            rw [aux_carrier_eq_univ, Set.image_subset_image_iff (Subtype.val_injective)]
            tauto
        have inter_eq: (⋃ p', ⋃ (_ : C.dim_map p' < C.dim_map ⟨g '' s.1, s.2⟩), p'.1) ∩ Y.carrier = g '' ⋃ p, ⋃ (_ : sub_cell_complex_dim_map Y p < sub_cell_complex_dim_map Y s), p.1 := by
            ext x
            constructor
            case mp =>
                intro hx
                rw [Set.mem_inter_iff] at hx
                rcases hx with ⟨hx1, hx2⟩
                simp at hx1
                rcases hx1 with ⟨p0, ⟨⟨hp0_1, hp0_2⟩, hxp0⟩ ⟩
                simp [g]
                use hx2
                have : p0 ⊆ Y.carrier := by
                    rcases Y.cell_incl_or_disjoint p0 hp0_1 with h_incl | h_disjoint
                    case inl => exact h_incl
                    case inr =>
                        have : x ∈ p0 ∩ Y.carrier := by rw[Set.mem_inter_iff]; exact ⟨hxp0, hx2⟩
                        rw [h_disjoint.inter_eq] at this
                        tauto
                set p1 : Set Y := {y | g y ∈ p0}
                have p1_eq_p0: g '' p1 = p0 := by
                    ext y
                    simp [g, p1]
                    intro hy
                    exact this hy
                use p1
                have res1: ⟨x, hx2⟩ ∈ p1 := by simp[p1, g, hxp0]
                rw [and_comm]
                use res1
                have p1_in_y_sets : p1 ∈ sub_cell_complex_sets Y := by
                    simp [sub_cell_complex_sets]
                    rw [p1_eq_p0]
                    exact hp0_1
                use p1_in_y_sets
                have: sub_cell_complex_dim_map Y ⟨p1, p1_in_y_sets⟩ = CellComplexClass.dim_map ⟨p0, hp0_1⟩ := by
                    simp [sub_cell_complex_dim_map]
                    have : Subtype.val '' p1 ∈ C.sets := by rw[p1_eq_p0]; assumption
                    have: (⟨(Subtype.val '' p1), this⟩: C.sets) = ⟨p0, hp0_1⟩ := by exact SetCoe.ext p1_eq_p0
                    rw [this]
                rw [this, sub_cell_complex_dim_map]
                exact hp0_2
            case mpr =>
                intro hx
                apply Set.mem_inter
                case hb =>
                    show x ∈ Y.carrier
                    rw [aux_carrier_eq_univ]
                    let s := ⋃ p, ⋃ (_ : sub_cell_complex_dim_map Y p < sub_cell_complex_dim_map Y s), p.1
                    have : s ⊆ Set.univ := by intro x hx; trivial
                    exact (Set.image_mono this) hx
                case ha =>
                    simp [g] at hx
                    rcases hx with ⟨hxY, ⟨p, ⟨⟨hp, hpdim⟩, hxp⟩⟩⟩
                    let p' := g '' p
                    have hp' : p' ∈ C.sets := by simpa using hp
                    have hxp' : x ∈ p' := by use ⟨x, hxY⟩
                    simp
                    use p'; rw[and_comm]; use hxp', hp', hpdim
        let h := Set.subset_inter sub1 sub2
        rw [inter_eq] at h
        exact h
    rw [Set.image_subset_image_iff (Subtype.val_injective)] at this
    exact this

instance cell_complex_of_sub_cell_complex {X:Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (Y: SubCellComplex X): CellComplexClass Y where
    sets := sub_cell_complex_sets Y
    nonempty := sub_cell_complex_set_nonempty Y
    disjoint := sub_cell_complex_set_disjoint Y
    cover := sub_cell_complex_set_cover Y
    dim_map := sub_cell_complex_dim_map Y
    hom := sub_cell_complex_hom Y
    characteristic_map := sub_cell_complex_characteristic_map Y
    characteristic_map_continuous := sub_cell_complex_characteristic_map_continuous Y
    characteristic_map_inner_range := sub_cell_complex_characteristic_map_inner_range Y
    characteristic_map_inner_embd := sub_cell_complex_characteristic_map_inner_embd Y
    characteristic_map_boundary := sub_cell_complex_characteristic_map_boundary Y
end

theorem aux_closed_in_subspace_of_sub_complex_coeherent {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] {Y: SubCellComplex X} {s: Set Y} (hs: ∀ ce ∈ {x | ∃ e ∈ sub_cell_complex_sets Y, closure e = x}, IsClosed (((↑): ce → Y) ⁻¹' s)) {e0: Set X} (he0: e0 ∈ C.sets) (h: e0 ⊆ Y.carrier): IsClosed (((↑): closure e0 → X) ⁻¹' (((↑): Y → X) '' s)) := by
    let g : Y → X := (↑);
    let s' := g '' s;
    let φ : closure e0 → X := (↑)
    show IsClosed (φ ⁻¹' s')
    have h' : closure e0 ⊆ Y.carrier := by exact Y.cell_closure_incl e0 he0 h
    let e0' := g ⁻¹' e0
    have aux_e0_e0' : g '' e0' = e0 := by
        ext x
        simp[g, e0']
        exact fun a ↦ h a
    have e0'_in_sets: e0' ∈ sub_cell_complex_sets Y := by
        simp [e0', sub_cell_complex_sets]
        rw [aux_e0_e0']
        exact he0
    let hom_to_fun : closure e0 → closure e0' := by
        rintro  ⟨x, hx⟩
        have : ⟨x, h' hx⟩ ∈ closure e0' := by
            rw [mem_closure_iff]
            intro V hV hyV
            rcases hV with ⟨V', hV', hV'eq⟩
            have x_in_V': x ∈ V' := by
                rw [←hV'eq] at hyV
                simpa using hyV
            rw [mem_closure_iff] at hx
            specialize hx V' hV' x_in_V'
            rcases hx with ⟨t, ht⟩
            let t': Y := ⟨t, h ht.2⟩
            have t'_in_V: t' ∈ V := by rw [←hV'eq]; exact ht.1
            have t'_in_e0' : t' ∈ e0' := ht.2
            use t', t'_in_V
        exact ⟨⟨x, h' hx⟩, this⟩
    -- this homeomorphisim will not be used but kept here as it might be useful
    have ce0_hom_ce0': closure e0 ≃ₜ closure e0' := {
        toFun := hom_to_fun
        invFun := by
            rintro ⟨y, hy⟩
            have : y.1 ∈ closure e0 := by
                rw [mem_closure_iff]
                intro V hV hyV
                let V' := g ⁻¹' V
                have y_in_V' : y ∈ V' := hyV
                have V'_open: IsOpen V' := isOpen_induced hV
                rw [mem_closure_iff] at hy
                specialize hy V' V'_open y_in_V'
                rcases hy with ⟨t', ht'⟩
                have t_in_V: t'.1 ∈ V := ht'.1
                have t_in_e0 : t'.1 ∈ e0 := ht'.2
                use t'.1, t_in_V
            exact ⟨y.1, this⟩
        left_inv := fun x ↦ rfl
        right_inv := fun x ↦ rfl
    }
    set η : closure e0' → Y := (↑) with η_def
    specialize hs (closure e0') (by use e0', e0'_in_sets)
    rw [←η_def] at hs
    have : φ ⁻¹' s' = hom_to_fun ⁻¹' (η ⁻¹' s) := by
        ext x
        constructor
        case mp =>
            intro hx
            rcases hx with ⟨y, hy, hyx⟩
            have : y = η (hom_to_fun x) := by
                exact SetLike.coe_eq_coe.mp hyx
            show η (hom_to_fun x) ∈ s
            rwa [←this]
        case mpr =>
            intro hx
            have : g (η (hom_to_fun x)) = φ x := by rfl
            show φ x ∈ s'
            rw [←this]
            use (η (hom_to_fun x)), hx
    rw [this]
    exact IsClosed.preimage (by continuity) hs

theorem aux_closed_of_sub_complex_coeherent {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] (Y: SubCellComplex X) {s: Set Y} (hs: ∀ b ∈ {x | ∃ s ∈ sub_cell_complex_sets Y, closure s = x}, IsClosed (((↑): b → Y) ⁻¹' s)) : IsClosed (((↑): Y → X) '' s) := by
    let g : Y → X := (↑)
    let s' := g '' s
    apply closed_crit_of_coeherent CW.coeherent
    rintro _ ⟨e0, he0, rfl⟩
    match (Y.cell_incl_or_disjoint e0 he0) with
    | Or.inl h =>
        -- e0 in Y
        apply aux_closed_in_subspace_of_sub_complex_coeherent hs he0 h
    | Or.inr h =>
        rcases CW.closure_finite e0 he0 with ⟨ss, ss_all_sets, ss_finite, ss_cover⟩
        let ss₁ := {e | e ∈ ss ∧ (e ∩ Y.carrier).Nonempty}
        let φ : closure e0 → X := (↑)
        have pre_img_eq: φ ⁻¹' (closure e0 ∩ s') = φ ⁻¹' s' := Subtype.preimage_coe_self_inter (closure e0) s'
        have pre_img_closed: IsClosed (closure e0 ∩ s') := by
            have eq1 : closure e0 ∩ s' = closure e0 ∩ s' ∩ (⋃ e ∈ ss₁, closure e) := by
                ext x
                constructor
                case mpr =>
                    intro hx
                    use hx.1.1
                    exact hx.1.2
                case mp =>
                    intro hx
                    have : x ∈ ⋃ e ∈ ss₁, closure e := by
                        rcases ss_cover hx.1 with ⟨e1, he1, hxe1⟩
                        have : e1 ∈ ss₁ := by
                            use he1
                            have : x ∈ Y.carrier := by
                                rcases hx.2 with ⟨y, hy, rfl⟩
                                exact y.2
                            use x, hxe1
                        simp
                        use e1, this, subset_closure hxe1
                    use hx
            have eq2 : closure e0 ∩ s' ∩ (⋃ e ∈ ss₁, closure e) = closure e0 ∩ (⋃ e ∈ ss₁, s' ∩ closure e) := by
                rw [Set.inter_assoc]
                congr
                exact Set.inter_iUnion₂ s' fun i j ↦ closure i
            rw [eq1, eq2]
            have ss₁_finite: ss₁.Finite := Set.Finite.sep ss_finite fun a ↦ (a ∩ Y.carrier).Nonempty
            have : ∀ e ∈ ss₁, IsClosed (s' ∩ closure e) := by
                intro e he
                let η : closure e → X := (↑)
                have : s' ∩ closure e = η '' (η ⁻¹' s')  := by
                    ext x
                    simp [η]
                    tauto
                rw [this]
                have : IsClosedEmbedding η := IsClosed.isClosedEmbedding_subtypeVal isClosed_closure
                apply (IsClosedEmbedding.isClosed_iff_image_isClosed this).mp
                have e_in_sets : e ∈ C.sets := ss_all_sets he.1
                apply aux_closed_in_subspace_of_sub_complex_coeherent hs e_in_sets
                apply Y.subset_of_intersect e_in_sets
                rw [←Set.nonempty_iff_ne_empty]
                exact he.2
            apply IsClosed.inter isClosed_closure
            refine Set.Finite.isClosed_biUnion ss₁_finite this
        rw [isClosed_induced_iff]
        use closure e0 ∩ s'

instance cw_sub_cell_complex {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] (Y: SubCellComplex X): CWComplexClass Y where
    closure_finite := by
        intro s hs
        let g: Y → X := (↑)
        let s' := g '' s
        have aux_carrier_eq : Y.carrier = g '' Set.univ := by simp [g]; rfl
        have hs'_in_Y : s' ⊆ Y.carrier := by rw [aux_carrier_eq];apply Set.image_subset;apply Set.subset_univ
        have hcs'_in_Y: closure s' ⊆ Y.carrier := by exact Y.cell_closure_incl s' hs hs'_in_Y
        have hs'_in_sets: s' ∈ C.sets := by simpa using hs
        rcases CW.closure_finite s' hs'_in_sets with ⟨ss', hss'_sub_sets, hss'_finite, hss'_incl_closure⟩
        let ss'₁ := {s'₁ | s'₁ ∈ ss' ∧ s'₁ ∩ closure s' ≠ ∅}
        have hss'₁_incl_closure : closure s' ⊆ ⋃₀ ss'₁ := by
            intro x hx
            rcases hss'_incl_closure hx with ⟨s'₁, hs'₁⟩
            have : s'₁ ∈ ss'₁ := by
                use hs'₁.1
                rw [←Set.nonempty_iff_ne_empty]
                use x
                tauto
            use s'₁
            tauto
        have hss'₁_all_in_Y : ∀ s'₁ ∈ ss'₁, s'₁ ⊆ Y.carrier := by
            intro s'₁ hs'₁
            have hs'₂: s'₁ ∩ Y.carrier ≠ ∅ := by
                have hle: s'₁ ∩ closure s' ≤ s'₁ ∩ Y.carrier := by intro x; simp [Set.mem_inter_iff]; tauto
                have hlt: ⊥ < s'₁ ∩ closure s' := by simpa [Set.nonempty_iff_ne_empty] using hs'₁.2
                have : ⊥ < s'₁ ∩ Y.carrier := by exact lt_of_le_of_lt' hle hlt
                exact Ne.symm (ne_of_lt this)
            have hs'₃: s'₁ ∈ C.sets := by exact hss'_sub_sets hs'₁.1
            exact SubCellComplex.subset_of_intersect Y hs'₃ hs'₂
        have hss'₁_coe_eq_self: ∀ s'₁ ∈ ss'₁, g '' (g ⁻¹' s'₁) = s'₁ := by
            intro s'₁ hs'₁
            have : s'₁ ∩ Y.carrier = s'₁ := Eq.symm ((fun {α} {s t} ↦ Set.left_eq_inter.mpr) (hss'₁_all_in_Y s'₁ hs'₁))
            rw [←this]
            ext x
            simp[g]
            tauto
        let ss := (Set.preimage g) '' ss'₁
        use ss
        have ss_in_sets : ss ⊆ sub_cell_complex_sets Y := by
            intro s0 hs0
            rcases hs0 with ⟨s1, hs1, rfl⟩
            simp [sub_cell_complex_sets]
            rw [hss'₁_coe_eq_self s1 hs1]
            apply hss'_sub_sets hs1.1
        have ss_finite: ss.Finite := by
            apply Set.Finite.image
            have : ss'₁ ⊆ ss' := by
                intro s'₁ hs'₁
                exact hs'₁.1
            apply Set.Finite.subset hss'_finite this
        have cs_in_ss_iunion : closure s ⊆ ⋃₀ ss := by
            have aux_cs : closure s ⊆ g ⁻¹' (closure s') := by
                intro x hx
                show g x ∈ closure s'
                rw [mem_closure_iff]
                intro V hV h_gx_in_V
                let V' := g ⁻¹' V
                have hV' : IsOpen V' := isOpen_induced hV
                have h_x_in_V' : x ∈ V' := h_gx_in_V
                have V'_s_inter_nonempty: (V' ∩ s).Nonempty := by
                    rw [mem_closure_iff] at hx
                    exact hx V' hV' h_x_in_V'
                rcases V'_s_inter_nonempty with ⟨y, hyV', hys⟩
                use g y, hyV'
                use y
            have aux_ss: g ⁻¹' (closure s') ⊆ ⋃₀ ss := by
                have : ⋃₀ ss = g ⁻¹' (⋃₀ ss'₁) := by simp[ss]
                rw [this]
                intro y hy
                exact hss'₁_incl_closure hy
            apply subset_trans aux_cs aux_ss
        tauto
    coeherent := by
        apply coeherent_of_closed_crit_and_cover'
        case h_close_crit' =>
            intro s hs
            let g: Y → X := (↑)
            let s' := g '' s
            have coe_closed: @IsClosed X _ s' := by
                apply aux_closed_of_sub_complex_coeherent Y hs
            have : g ⁻¹' s' = s := by ext x; simp [g, s']
            rw [←this]
            exact IsClosed.preimage continuous_subtype_val coe_closed
        case h_cover =>
            ext x
            simp
            have : ∃ s ∈ C.sets, (x:X) ∈ s := by
                have : (x:X) ∈ ⋃₀ C.sets := by rw  [C.cover]; trivial
                exact  this
            rcases this with ⟨s, hs1, hs2⟩
            let s' := ((↑): Y → X) ⁻¹' s
            have s_in_Y : s ⊆ Y := by
                rcases Y.cell_incl_or_disjoint s hs1 with h1 | h2
                case inl => exact h1
                case inr =>
                    rw [Set.disjoint_iff_inter_eq_empty] at h2
                    contrapose! h2
                    use x.val
                    exact ⟨hs2, x.2⟩
            have s'_in_sets: s' ∈ sub_cell_complex_sets Y := by
                have : ((↑): Y → X) '' s' = s := by
                    ext x
                    simp[s']
                    exact fun a ↦ s_in_Y a
                simp [sub_cell_complex_sets, this, hs1]
            have x_in_s' : x ∈  closure s' := subset_closure hs2
            use s', s'_in_sets

theorem sub_cw_cell_complex_closed {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X] (Y: SubCellComplex X) : IsClosed Y.carrier := by
    let g : Y → X := (↑)
    have : Y.carrier = g '' Set.univ := by
        ext x
        simp [g]
        rfl
    rw [this]
    apply aux_closed_of_sub_complex_coeherent Y
    rintro b ⟨e', he', rfl⟩
    simp

def Skeleton (X: Type*) [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] (n : ℕ) : SubCellComplex X where
    carrier := ⋃ s : C.sets, ⋃ _:(C.dim_map s ≤ n), s.val
    cell_incl_or_disjoint := by
        intro e he
        have : C.dim_map ⟨e, he⟩ ≤ n ∨ C.dim_map ⟨e, he⟩ > n := by exact le_or_gt (dim_map ⟨e, he⟩) n
        match le_or_gt (dim_map ⟨e, he⟩) n with
        | Or.inl h =>
            left
            intro x hx
            simp
            use e, ⟨he, h⟩
        | Or.inr h =>
            right
            apply Set.disjoint_iUnion₂_right.mpr
            intro e' he'
            have : e ≠ e' := by
                contrapose! he'
                simpa [he'] using h
            apply C.disjoint he e'.2 this
    cell_closure_incl := by
        intro e he e_in_y
        rw [←characteristic_map_range ⟨e, he⟩]
        intro x hx
        rw [cb_map_range_decomposition _] at hx
        match hx with
        | Or.inl hx_boundary =>
            have : ⋃ s:C.sets, ⋃ _:(C.dim_map s < C.dim_map ⟨e, he⟩), s.1 ⊆ ⋃ s:C.sets, ⋃ _:(C.dim_map s ≤ n), s.1 := by
                have aux : C.dim_map ⟨e, he⟩ ≤ n := by
                    rcases C.nonempty e he with ⟨x0, hx0⟩
                    specialize e_in_y hx0
                    simp at e_in_y
                    rcases e_in_y with ⟨e0, ⟨e0_in_sets, he0⟩, h_x0_in_e0⟩
                    have : e0 = e := by
                        by_contra! h
                        have : Disjoint e0 e := C.disjoint e0_in_sets he h
                        rw [Set.disjoint_left] at this
                        specialize this h_x0_in_e0
                        contradiction
                    have : (⟨e0, e0_in_sets⟩:C.sets) = ⟨e, he⟩ := by exact SetCoe.ext this
                    rw [←this]
                    exact he0
                intro y hy
                simp at hy
                rcases hy with ⟨s0, ⟨hs0_10, hs0_11⟩, hs0_2⟩
                simp
                have : C.dim_map ⟨s0, hs0_10⟩ ≤ n := by linarith
                use s0, ⟨hs0_10, this⟩
            apply this (C.characteristic_map_boundary ⟨e, he⟩ hx_boundary)
        | Or.inr hx_inner =>
            rw [C.characteristic_map_inner_range] at hx_inner
            exact e_in_y hx_inner

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]
theorem boundary_sub_skeleton : ∀ s : C.sets, 1 ≤ C.dim_map s → Set.range (cb_boundary_map (C.characteristic_map s)) ⊆ Skeleton X ((C.dim_map s) - 1) := by
    intro s hs
    trans ⋃ p:C.sets, ⋃ _:(C.dim_map p < C.dim_map s), p.val
    apply C.characteristic_map_boundary
    intro x hx
    simp at hx
    rcases hx with ⟨s1, ⟨s1_in_sets, dim_s1_lt⟩, x_in_s1⟩
    show x ∈ (Skeleton X ((C.dim_map s) - 1)).carrier
    simp [Skeleton]
    have : C.dim_map ⟨s1, s1_in_sets⟩ ≤ C.dim_map s - 1 := (Nat.le_sub_one_iff_lt hs).mpr dim_s1_lt
    use s1, ⟨s1_in_sets, this⟩

theorem sub_skeleton_iff {n : ℕ}: ∀ s : C.sets, s.1 ⊆ Skeleton X n ↔ C.dim_map s ≤ n := by
    intro s
    constructor
    case mp =>
        intro s_in_skeleton
        rcases C.nonempty s.1 s.2 with ⟨x, hx⟩
        let hx_in_skeleton : x ∈ (Skeleton X n).carrier := s_in_skeleton hx
        simp [Skeleton] at hx_in_skeleton
        rcases hx_in_skeleton with ⟨s1, ⟨s1_in_sets, hs1⟩, h_x_in_s1⟩
        have : s.1 = s1 := by
            by_contra! h
            let s_s1_disjoint: Disjoint s.1 s1 := C.disjoint s.2 s1_in_sets h
            rw [Set.disjoint_iff] at s_s1_disjoint
            have : x ∈ s.1 ∩ s1 := Set.mem_inter hx h_x_in_s1
            exact s_s1_disjoint this
        have : s = ⟨s1, s1_in_sets⟩ := SetCoe.ext this
        rw [this]
        exact hs1
    case mpr =>
        intro hs
        show s.1 ⊆ ⋃ r: C.sets, ⋃ _:(C.dim_map r ≤ n), r.val
        exact Set.subset_biUnion_of_mem hs

theorem mem_sub_complex_iff {x : X} {S: SubCellComplex X} : x ∈ S ↔ ∃ e ∈ C.sets, x ∈ e ∧ e ⊆ S := by
    constructor
    case mp =>
        intro hx
        let CS: CellComplexClass S := by infer_instance
        have : ∃ e' ∈ CS.sets, ⟨x, hx⟩ ∈ e' := by
            rw [←Set.mem_sUnion, CellComplexClass.cover]
            trivial
        rcases this with ⟨e', e'_in_sets_of_S, x'_in_e'⟩
        let g : S → X := (↑)
        use g '' e', e'_in_sets_of_S
        have : x ∈ g '' e' := by
            rw [Set.mem_image]
            use ⟨x, hx⟩
        use this
        rintro x1 ⟨x1', hx1', rfl⟩
        exact Subtype.coe_prop x1'
    case mpr =>
        rintro ⟨e, e_in_sets, ⟨x_in_e, e_sub_s⟩⟩
        exact e_sub_s x_in_e

theorem skeleton_mono : ∀ (m n : ℕ), m ≤ n → ((Skeleton X m): Set X) ⊆ (Skeleton X n) := by
    intro m n m_le_n x hx
    have : x ∈ ⋃ s:C.sets, ⋃ _:(C.dim_map s ≤ m), s.val := by exact hx
    rw [Set.mem_iUnion₂] at this
    rcases this with ⟨s0, hs0, hxs0⟩
    show x ∈ ⋃ s:C.sets, ⋃ _:(C.dim_map s ≤ n), s.val
    rw [Set.mem_iUnion₂]
    use s0, (le_trans hs0 m_le_n)
theorem exists_mem_of_skeleton (x: X): ∃ n:ℕ, x ∈ (Skeleton X n) := by
    rcases exists_mem_of_cell x with ⟨e, e_in_sets, x_in_e⟩
    let n := C.dim_map ⟨e, e_in_sets⟩
    use n
    show x ∈ ⋃ s:C.sets, ⋃ _:(C.dim_map s ≤ n), s.val
    simp
    have : C.dim_map ⟨e, e_in_sets⟩ ≤ n := by exact Nat.le_refl (dim_map ⟨e, e_in_sets⟩)
    use e, ⟨e_in_sets, this⟩
theorem skeleton_cover : ⋃ n:ℕ, ((Skeleton X n): Set X) = Set.univ := by
    ext x
    simp
    exact exists_mem_of_skeleton x
theorem skeleton_cover_any_ge_n : ∀ n : ℕ, ⋃ m:ℕ, ⋃ _:(n ≤ m), ((Skeleton X m): Set X) = Set.univ := by
    intro n
    ext x
    simp
    rcases exists_mem_of_skeleton x with ⟨n₀, hn₀⟩
    let m := max n n₀
    use m, Nat.le_max_left n n₀
    exact skeleton_mono n₀ m (Nat.le_max_right n n₀) hn₀
theorem cell_singleton_of_dim0 : ∀ e : C.sets, C.dim_map e = 0 ↔ ∃ x : X, e.val = {x} := by
    rintro ⟨e, e_in_sets⟩
    refine Iff.intro ?mp ?mpr
    case mp =>
        intro d0
        let f := C.characteristic_map ⟨e, e_in_sets⟩
        have : Subsingleton (b (C.dim_map ⟨e, e_in_sets⟩)) := by
            rw [d0]
            exact instSubsingletonElemEuclideanSpaceRealFinOfNatNatB
        have hf: f '' cb_inner = e := by apply C.characteristic_map_inner_image
        have : f '' cb_inner = Set.range (f ∘ b_to_cb) := by rw [cb_inner, Set.range_comp]
        rw [this] at hf
        simp
        rw [←hf]
        let x0 : b (C.dim_map ⟨e, e_in_sets⟩) := default
        use (f ∘ b_to_cb) x0
        ext y
        constructor
        . rintro ⟨x1, hx1, rfl⟩
          apply Set.mem_singleton_of_eq
          congr
          apply Subsingleton.allEq
        rintro hy
        use x0
        exact Eq.symm hy
    case mpr =>
        rintro ⟨x, hx⟩
        simp at hx
        let f := cb_inner_map (C.characteristic_map ⟨e, e_in_sets⟩)
        have f_inj: Function.Injective f := by
            apply IsEmbedding.injective
            exact characteristic_map_inner_embd ⟨e, e_in_sets⟩
        have f_range_singleton : Set.range f = {x} := by
            rw [←hx]
            apply C.characteristic_map_inner_range
        have domain_singleton: ∃ y, b (C.dim_map ⟨e, e_in_sets⟩) = {y} := by
            have : x ∈ Set.range f := by rw [f_range_singleton]; rfl
            rcases this with ⟨y, hy⟩
            use y
            ext y'
            refine Iff.intro ?mp ?mpr
            case mp =>
                intro hy'
                have : f ⟨y', hy'⟩ = f y := by
                    trans x
                    . show f ⟨y', hy'⟩ ∈ ({x}:Set X)
                      rw [←f_range_singleton]
                      apply Set.mem_range_self
                    exact Eq.symm hy
                have : ⟨y', hy'⟩ = y := by exact f_inj this
                apply_fun Subtype.val at this
                exact this
            case mpr =>
                intro hy'
                simp at hy'
                rw [hy']
                exact Subtype.coe_prop y
        rw [b_singleton_iff] at domain_singleton
        exact domain_singleton

theorem skeleton_cell_dim {n : ℕ}: ∀ e : sub_cell_complex_sets (Skeleton X n), sub_cell_complex_dim_map (Skeleton X n) e ≤ n := by
    let g : (Skeleton X n) → X := (↑)
    intro e
    let e' := g '' e
    have e'_in_sets : e' ∈ C.sets := e.2
    have : C.dim_map ⟨e', e'_in_sets⟩ = sub_cell_complex_dim_map (Skeleton X n) e := rfl
    rw [←this]
    have : e' ⊆ (Skeleton X n) := by
        intro x hx
        rcases hx with ⟨y, y_in_e, rfl⟩
        exact y.2
    rw [←sub_skeleton_iff]
    simpa using this

instance {n:ℕ}: FiniteDim (Skeleton X n) := by
    have : (Set.range (sub_cell_complex_dim_map (Skeleton X n))).Finite := by
        have finite_superset: {x:ℕ | x ≤ n}.Finite := by exact Set.finite_le_nat n
        have range_subset: (Set.range (sub_cell_complex_dim_map (Skeleton X n))) ⊆ {x:ℕ | x ≤ n} := by
            rintro m ⟨e, he⟩
            show m ≤ n
            rw [←he]
            apply skeleton_cell_dim
        exact Set.Finite.subset finite_superset range_subset
    exact { out := this }

theorem skeleton_dim {n : ℕ}: Dim (Skeleton X n) ≤ n := by
    simp [Dim]
    intro b e' e'_in_sets hb
    let g : (Skeleton X n) → X := (↑)
    let e := g '' e'
    have e_in_sets : e ∈ C.sets := e'_in_sets
    have : C.dim_map ⟨e, e_in_sets⟩ = dim_map ⟨e', e'_in_sets⟩ := rfl
    rw [←hb, ←this]
    have : e ⊆ (Skeleton X n) := by
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact y.2
    rw [←sub_skeleton_iff]
    simpa using this

theorem skeleton0_discrete [CWComplexClass X]: DiscreteTopology (Skeleton X 0) := by
    have singleton_in_sets: ∀ x : (Skeleton X 0), {x} ∈ sub_cell_complex_sets (Skeleton X 0) := by
        have aux: ∀ x ∈ (Skeleton X 0), {x} ∈ C.sets := by
            have : ∀ x ∈ (Skeleton X 0), ∃ e : C.sets, x ∈ e.1 ∧ (C.dim_map e = 0) := by
                intro x hx
                have: x ∈ ⋃ s:C.sets, ⋃ _:(C.dim_map s ≤ 0), s.val := hx
                rw [Set.mem_iUnion₂] at this
                rcases this with ⟨e, ⟨dim_e, x_in_e⟩⟩
                use e, x_in_e, Nat.eq_zero_of_le_zero dim_e
            intro x hx
            rcases this x hx with ⟨e, x_in_e, dim_e_0⟩
            rw [cell_singleton_of_dim0] at dim_e_0
            rcases dim_e_0 with ⟨x₀, hx₀⟩
            rw [hx₀] at x_in_e
            have : e.val = {x} := by
                ext y
                rw [hx₀]
                simp
                exact Iff.symm (Eq.congr_right x_in_e)
            rw [←this]
            exact e.2
        intro x
        rw [sub_cell_complex_sets]
        simp
        exact aux x.val x.prop
    have singleton_open: ∀ x : (Skeleton X 0), IsOpen {x} := by
        intro x
        let x_in_sets := singleton_in_sets x
        apply open_cell_of_finite_dim ⟨{x}, x_in_sets⟩
        have dim_skeleton_0 : Dim (Skeleton X 0) = 0 := by
            apply Nat.eq_zero_of_le_zero
            exact skeleton_dim
        have dim_singleton : dim_map ⟨{x}, x_in_sets⟩ = 0 := by
            rw [cell_singleton_of_dim0]
            use x
        linarith
    rw [←singletons_open_iff_discrete]
    exact singleton_open
theorem closed_of_cell_empty_or_full_intersection [CWComplexClass X] (s: Set X) (hs: ∀ e ∈ C.sets, closure e ∩ s = ∅ ∨ closure e ∩ s = closure e) : IsClosed s := by
    apply closed_crit_of_coeherent CWComplexClass.coeherent
    rintro b ⟨e, e_in_sets, rfl⟩
    let g : closure e → X := (↑)
    show IsClosed (g ⁻¹' s)
    have ce_eq_range : closure e = Set.range g := Eq.symm Subtype.range_coe
    rw [←Set.preimage_inter_range, Subtype.range_coe]
    match hs e e_in_sets with
    | Or.inl ce_not_in_s =>
        rw [Set.inter_comm, ce_not_in_s]
        simp
    | Or.inr ce_in_s =>
        rw [Set.inter_comm, ce_in_s]
        simp[ce_eq_range]
theorem open_closed_of_cell_empty_or_full_intersection [CWComplexClass X] (s: Set X) (hs: ∀ e ∈ C.sets, closure e ∩ s = ∅ ∨ closure e ∩ s = closure e) : IsOpen s ∧ IsClosed s := by
    rw [and_comm]
    use closed_of_cell_empty_or_full_intersection s hs
    have : IsClosed sᶜ := by
        apply closed_of_cell_empty_or_full_intersection
        intro e e_in_sets
        match hs e e_in_sets with
        | Or.inl ce_not_in_s =>
            right
            rw [Set.inter_eq_left]
            apply Disjoint.subset_compl_right
            rwa [Set.disjoint_iff_inter_eq_empty]
        | Or.inr ce_in_s =>
            left
            rwa [←Set.disjoint_iff_inter_eq_empty,Set.disjoint_compl_right_iff_subset, ←Set.inter_eq_left]
    rwa [←isClosed_compl_iff]
theorem boundary_nonempty : ∀ s : sets, 1 ≤ dim_map s → (Set.range (cb_boundary_map (C.characteristic_map s))).Nonempty := by
    intro s hs
    rw [boundary_map_range, cb_boundary, ←Set.range_comp, Set.range_nonempty_iff_nonempty]
    apply Set.Nonempty.to_subtype
    exact sph_nonempty hs
theorem boundary_covered_by_finite_cells [CW: CWComplexClass X] : ∀ e₀:C.sets, ∃ ss ⊆ C.sets, ss.Finite ∧ (closure e₀.1) \ e₀.1 ⊆ ⋃₀ ss ∧ ∀ e₁:C.sets, e₁.1 ∈ ss → C.dim_map e₁ < C.dim_map e₀ := by
    intro e₀
    rcases CW.closure_finite e₀.1 e₀.2 with ⟨ss₁, ss₁_subset_sets, ss₁_finite, ss₁_cover_ce₀⟩
    let ss₂' := {e:C.sets | C.dim_map e < C.dim_map e₀}
    let ss₂ := Subtype.val '' ss₂'
    let ss := ss₁ ∩ ss₂
    have all_cell: ss ⊆ C.sets := by
        intro e he
        rcases he.2 with ⟨e' ,he', rfl⟩
        exact e'.2
    have ss_finite: ss.Finite := by
        exact Set.Finite.inter_of_left ss₁_finite _
    have boundary_covered: closure e₀ \ e₀ ⊆ ⋃₀ ss := by
        intro x hx
        rcases Set.mem_sUnion.mp (ss₁_cover_ce₀ (hx.1)) with ⟨s₁, s₁_in_ss₁, x_in_s₁⟩
        have : closure e₀ \ e₀ ⊆ ⋃₀ ss₂ := by rw [Set.sUnion_image Subtype.val ss₂'];apply cell_boundary_cover
        rcases Set.mem_sUnion.mp (this hx) with ⟨s₂, s₂_in_ss₂, x_in_s₂⟩
        have s₁_eq_s₂ : s₁ = s₂ := by
            have s₁_in_sets : s₁ ∈ C.sets := ss₁_subset_sets s₁_in_ss₁
            have s₂_in_sets : s₂ ∈ C.sets := by
                rcases s₂_in_ss₂ with ⟨s₂', hs₂, rfl⟩
                exact s₂'.2
            apply same_cell_of_mem s₁_in_sets s₂_in_sets x_in_s₁ x_in_s₂
        rw [←s₁_eq_s₂] at s₂_in_ss₂
        rw [Set.mem_sUnion]
        use s₁, ⟨s₁_in_ss₁, s₂_in_ss₂⟩
    have dim_lt: ∀ e:C.sets, e.1 ∈ ss → C.dim_map e < C.dim_map e₀ := by
        intro e he
        show e ∈ ss₂'
        suffices e.1 ∈ ss₂ by
            rcases this with ⟨e', e'_in_ss₂', heq⟩
            have : e' = e := SetCoe.ext heq
            rwa [←this]
        exact he.2
    use ss
end

-- finite cell complex
def FiniteCellComplex (X: Type*) [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] : Prop := C.sets.Finite

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X]
def dim0_cell_subcomplex (e : C.sets) (he: C.dim_map e = 0) : SubCellComplex X where
    carrier := e.1
    cell_incl_or_disjoint := by
        intro e' he'
        match eq_or_ne e' e with
        | Or.inl eq => left; rw [eq]
        | Or.inr ne => right; apply C.disjoint he' e.2 ne
    cell_closure_incl := by
        intro e' he' e'_in_e
        rw [cell_singleton_of_dim0] at he
        rcases he with ⟨x, hx⟩
        rw [hx, Set.subset_singleton_iff_eq] at e'_in_e
        match e'_in_e with
        | Or.inl e'_empty =>
            rw [e'_empty]
            simp
        | Or.inr e'_singleton =>
            rw [e'_singleton]
            simp [hx]
theorem dim0_cell_subcomplex_finite (e: C.sets) (he: C.dim_map e = 0) : FiniteCellComplex (dim0_cell_subcomplex e he) := by
    have : (sub_cell_complex_sets (dim0_cell_subcomplex e he)).Finite := by
        have : (sub_cell_complex_sets (dim0_cell_subcomplex e he)) = {Set.univ} := by
            ext e'
            let g : (dim0_cell_subcomplex e he) → X := (↑)
            have range_eq_e: g '' (Set.univ) = e.1 := by
                simp
                rw [Subtype.range_coe]
                rfl
            refine Iff.intro ?mp ?mpr
            case mp =>
                intro he'
                show e' = Set.univ
                suffices g '' e' = g '' (Set.univ) by
                    rw [Set.image_eq_image (Subtype.val_injective)] at this
                    exact this
                rw [range_eq_e]
                have e'_image_nonempty : (g '' e') ≠ ∅ := by
                    rw [←Set.nonempty_iff_ne_empty]
                    apply nonempty
                    exact he'
                have e'_image_sub_e : (g '' e') ⊆ e := by
                    rw [←range_eq_e]
                    exact Set.image_mono fun ⦃a⦄ a ↦ trivial
                rw [cell_singleton_of_dim0] at he
                rcases he with ⟨x, hx⟩
                rw [hx, Set.subset_singleton_iff_eq] at e'_image_sub_e
                rw [hx]
                tauto
            case mpr =>
                intro he'
                simp at he'
                rw [he']
                show g '' (Set.univ) ∈ C.sets
                rw [range_eq_e]
                exact e.2
        rw [this]
        apply Set.finite_singleton
    exact this

theorem finite_sub_cell_complex_iff (sc: SubCellComplex X) : (FiniteCellComplex sc) ↔ ({e:Set X| e ∈ C.sets ∧ e ⊆ sc}.Finite) := by
    let g : sc → X := (↑)
    let s1 := {e: Set X | e ∈ C.sets ∧ e ⊆ sc}
    have : s1 =  (Set.image g) '' (sub_cell_complex_sets sc) := by
        ext e
        refine Iff.intro ?mp ?mpr
        case mp =>
            intro he
            let e' := g ⁻¹' e
            use e'
            have : g '' e' = e := by
                calc
                    g '' e' = (sc:Set X) ∩ e:= Subtype.image_preimage_coe sc e
                    _ = e := Set.inter_eq_self_of_subset_right he.2
            constructor
            . show g '' e' ∈ C.sets
              rw [this]
              exact he.1
            exact this
        case mpr =>
            intro he
            simp at he
            rcases he with ⟨e', he', rfl⟩
            constructor
            . exact he'
            apply Subtype.coe_image_subset
    refine Iff.intro ?mp ?mpr
    case mp =>
        simp only [s1, this]
        intro h
        apply Set.Finite.image
        exact h
    case mpr =>
        simp only [s1, this]
        intro h
        apply Set.Finite.of_finite_image h
        apply Set.injOn_of_injective
        rw [Set.image_injective]
        exact Subtype.val_injective


theorem cell_colsure_subset_finite_sub_complex [CW: CWComplexClass X] : ∀ e ∈ C.sets, ∃ SC: (SubCellComplex X), FiniteCellComplex SC ∧ closure e ⊆ SC := by
    intro e he
    -- see "induction tactic that doesn't destroy the input from context" on Zulip chat, this usage is interesting
    -- the cases tactic can also be used in this fashion
    induction' dim_eq: (C.dim_map ⟨e, he⟩) using Nat.strong_induction_on with n₀ ihn generalizing e he
    choose f_to_subcomplex hf_finite hf_cover using ihn
    rcases boundary_covered_by_finite_cells ⟨e, he⟩ with ⟨ss, ss_sub_sets, ss_finite, ss_cover_boundary, ss_dim_lt⟩
    --let fss: ss → SubCellComplex X := by
    --    intro e
    --    let m := C.dim_map ⟨e.1, ss_sub_sets e.2⟩
    --    have m_le_n₀: m < n₀ := by
    --        rw [←dim_eq]
    --        apply ss_dim_lt _ e.2
    --    exact f_to_subcomplex m m_le_n₀ e.1 (ss_sub_sets e.2) rfl
    let fss : ss → SubCellComplex X := fun e ↦ f_to_subcomplex (C.dim_map ⟨e.1, ss_sub_sets e.2⟩) (by rw [←dim_eq]; apply ss_dim_lt _ e.2) e.1 (ss_sub_sets e.2) rfl
    let SC_carrier : Set X:= (⋃ s:ss, ((fss s):Set X)) ∪ e
    have SC_carrier_cell_incl_or_disjoint : ∀ e₁ ∈ C.sets, e₁ ⊆ SC_carrier ∨ Disjoint e₁ SC_carrier := by
        intro e₁ he₁
        match eq_or_ne (e₁ ∩ SC_carrier) ∅ with
        | Or.inl inter_eq_empty =>
            right
            rwa [Set.disjoint_iff_inter_eq_empty]
        | Or.inr inter_ne_empty =>
            left
            rw [←Set.nonempty_iff_ne_empty] at inter_ne_empty
            rcases inter_ne_empty with ⟨x, hx⟩
            match hx.2 with
            | Or.inl mem_iunion =>
                rw [Set.mem_iUnion] at mem_iunion
                rcases mem_iunion with ⟨i ,hi⟩
                suffices sub_fss_i : e₁ ⊆ (fss i) by
                    have : ((fss i):Set X) ⊆ (⋃ s, (fss s):Set X) := Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
                    tauto
                apply (fss i).subset_of_intersect he₁
                rw [←Set.nonempty_iff_ne_empty]
                use x, hx.1, hi
            | Or.inr mem_e =>
                rw [same_cell_of_mem he₁ he hx.1 mem_e]
                exact Set.subset_union_right
    have aux_sub_some_fss {e₀: Set X} (e₀_in_sets: e₀ ∈ C.sets) (e₀_sub_SC: e₀ ⊆ SC_carrier) (e₀_ne_e: e₀ ≠ e) : ∃ s:ss, e₀ ⊆ (fss s) := by
        by_contra! not_subset
        have e₀_e_disjoint : Disjoint e₀ e := C.disjoint e₀_in_sets he e₀_ne_e
        have e₀_iufss_disjoint: Disjoint e₀ (⋃s:ss, fss s) := by
            rw [Set.disjoint_iUnion_right]
            intro s
            rcases (fss s).cell_incl_or_disjoint e₀ e₀_in_sets with h_incl | h_disj
            . exact False.elim ((not_subset s) h_incl)
            exact h_disj
        have e₀_disjoint_sc: Disjoint e₀ SC_carrier := Disjoint.union_right e₀_iufss_disjoint e₀_e_disjoint
        have e₀_empty : e₀ = ∅ := by
            rw [←Set.subset_empty_iff]
            exact e₀_disjoint_sc (fun _ a ↦ a) e₀_sub_SC
        have e₀_nonempty: e₀ ≠ ∅ := by
            rw [←Set.nonempty_iff_ne_empty]
            apply C.nonempty _ e₀_in_sets
        contradiction
    have ce_sub_SC : (closure e) ⊆ SC_carrier := by
        intro x hx
        rw [←Set.inter_union_diff (closure e) e, Set.inter_eq_right.mpr subset_closure] at hx
        match hx with
        | Or.inl x_in_e =>
            apply Set.subset_union_right x_in_e
        | Or.inr x_in_e_boundary =>
            simp at ss_cover_boundary
            suffices ⋃₀ ss ⊆ SC_carrier by
                exact this (ss_cover_boundary x_in_e_boundary)
            intro x' hx'
            simp at hx'
            left
            simp
            rcases hx' with ⟨i, i_in_ss, hi⟩
            use i, i_in_ss
            apply hf_cover
            apply subset_closure hi
    have SC_carrier_cell_closure_incl : ∀ e₁ ∈ C.sets, e₁ ⊆ SC_carrier → (closure e₁) ⊆ SC_carrier := by
        intro e₁ e₁_in_sets e₁_sub_carrier
        match eq_or_ne e₁ e with
        | Or.inl heq =>
            rw [heq]
            exact ce_sub_SC
        | Or.inr hne =>
            suffices ∃ s : ss, e₁ ⊆ fss s by
                rcases this with ⟨s, hs⟩
                have ce₁_subset: (closure e₁) ⊆ fss s := (fss s).cell_closure_incl e₁ e₁_in_sets hs
                have fss_s_subset: ((fss s):Set X) ⊆ SC_carrier := by
                    intro x hx
                    left
                    exact Set.mem_iUnion_of_mem s hx
                exact fun ⦃a⦄ a_1 ↦ fss_s_subset (ce₁_subset a_1)
            exact aux_sub_some_fss e₁_in_sets e₁_sub_carrier hne
    have SC_finite : {e₀:Set X | e₀ ∈ C.sets ∧ e₀ ⊆ SC_carrier}.Finite := by
        let SE := {e₀:Set X | e₀ ∈ C.sets ∧ e₀ ⊆ SC_carrier}
        let E: ss → Set (Set X) := fun s ↦ {e₀: Set X | e₀ ∈ C.sets ∧ e₀ ⊆ (fss s)}
        show SE.Finite
        have SE_decomp : SE = (⋃ s:ss, E s) ∪ {e} := by
            ext e₀
            refine Iff.intro ?mp ?mpr
            case mp =>
                rintro ⟨e₀_in_sets, e₀_sub_SC⟩
                match eq_or_ne e₀ e with
                | Or.inl e₀_eq_e => right; exact e₀_eq_e
                | Or.inr e₀_ne_e =>
                    rcases aux_sub_some_fss e₀_in_sets e₀_sub_SC e₀_ne_e with ⟨s₀, e₀_sub_fss_s₀⟩
                    left
                    simp [E]
                    use e₀_in_sets, s₀, s₀.2
            case mpr =>
                intro he₀
                match he₀ with
                | Or.inr mem_singleton =>
                    rw [mem_singleton]
                    use he
                    exact Set.subset_union_right
                | Or.inl mem_iunion =>
                    simp [E] at mem_iunion
                    use mem_iunion.1
                    rcases mem_iunion.2 with ⟨s₀, s₀_in_ss, hs₀⟩
                    trans ((fss ⟨s₀, s₀_in_ss⟩):Set X)
                    . exact hs₀
                    trans (⋃ s:ss, ((fss s):Set X))
                    . exact Set.subset_iUnion_of_subset ⟨s₀, s₀_in_ss⟩ fun ⦃a⦄ a ↦ a
                    exact Set.subset_union_left
        rw [SE_decomp]
        apply Set.Finite.union
        case ht => exact Set.finite_singleton e
        case hs =>
            have : Finite ss := ss_finite
            apply Set.finite_iUnion
            intro s₀
            rw [←finite_sub_cell_complex_iff]
            apply hf_finite
    let SC: SubCellComplex X := {
        carrier := SC_carrier
        cell_closure_incl := SC_carrier_cell_closure_incl
        cell_incl_or_disjoint:= SC_carrier_cell_incl_or_disjoint
    }
    use SC
    constructor
    . rw [finite_sub_cell_complex_iff]
      exact SC_finite
    exact ce_sub_SC
theorem subset_discrete_iff_cell_inter_finite [CW: CWComplexClass X] {S: Set X} : (IsClosed S ∧ (DiscreteTopology S)) ↔ ∀ e ∈ C.sets, (S ∩ e).Finite := by
    refine Iff.intro ?mp ?mpr
    case mp =>
        intro hS e e_in_sets
        suffices (S ∩ (closure e)).Finite by
            apply Set.Finite.subset this
            exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) subset_closure
        refine IsCompact.finite ?hcompact ?hdiscrete
        case hcompact => exact IsCompact.of_isClosed_subset (cell_compact e e_in_sets) (IsClosed.inter hS.1 isClosed_closure) Set.inter_subset_right
        case hdiscrete => exact DiscreteTopology.of_subset hS.2 Set.inter_subset_left
    case mpr =>
        intro hS
        have aux_closed: ∀ S₀: Set X, (∀ e ∈ C.sets, (S₀ ∩ e).Finite) → IsClosed S₀ := by
            intro S₀ hS₀
            apply closed_crit_of_coeherent CW.coeherent
            rintro _ ⟨e, e_in_sets, rfl⟩
            let g : (closure e) → X := (↑)
            show IsClosed (g ⁻¹' S₀)
            suffices hfinite: (S₀ ∩ closure e).Finite by
                have : g ⁻¹' S₀ = g ⁻¹' (S₀ ∩ closure e) := by
                    rw [Subtype.preimage_coe_eq_preimage_coe_iff]
                    ext x
                    simp
                    exact fun a a_1 ↦ a
                rw [this]
                exact IsClosed.preimage_val (Set.Finite.isClosed hfinite)
            rcases CW.closure_finite e e_in_sets with ⟨ss, ss_sub_sets, ss_finite, ss_cover⟩
            suffices (S₀ ∩ ⋃₀ ss).Finite by
                apply Set.Finite.subset this
                exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) ss_cover
            have : S₀ ∩ ⋃₀ ss = ⋃ s ∈ ss, S₀ ∩ s := by
                ext x
                simp
            rw [this]
            exact Set.Finite.biUnion' ss_finite fun i hi ↦ hS₀ i (ss_sub_sets hi)
        have SClosed: IsClosed S := aux_closed S hS
        have SDiscrete: DiscreteTopology S := by
            rw [discreteTopology_iff_forall_isClosed]
            intro s
            let g : S → X := (↑)
            suffices s_in_x_closed : IsClosed (g '' s) by
                have : s = g ⁻¹' (g '' s) := Eq.symm Set.preimage_val_image_val_eq_self
                rw [this]
                exact IsClosed.preimage_val s_in_x_closed
            apply aux_closed
            intro e e_in_sets
            apply Set.Finite.subset (hS e e_in_sets)
            rintro x ⟨⟨b, b_in_s, rfl⟩, x_in_e⟩
            exact ⟨b.2, x_in_e⟩
        tauto
end

end CellComplexClass
end Chp5
