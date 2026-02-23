import STCC.TopologicalProperties
import STCC.Construction
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.PartitionOfUnity
namespace Chp5

section helper
universe u
lemma paracompact_of_exist_partition_of_unity {X: Type u} [TopologicalSpace X] (hX: ∀ (α: Type u) (s: α → Set X), (∀ a, IsOpen (s a)) → (⋃ a, s a = Set.univ) → ∃ p:(PartitionOfUnity α X), p.IsSubordinate s): ParacompactSpace X := by
  constructor
  intro α s hs_open hs_cover
  obtain ⟨p, hp⟩ := hX α s hs_open hs_cover
  refine ⟨α, fun a => Function.support (p a), ?openness, ?covering, ?locally_finite, ?refinement⟩
  case openness =>
    intro b
    exact isOpen_ne.preimage (map_continuous (p b))
  case covering =>
    rw [Set.iUnion_eq_univ_iff]
    intro x
    obtain ⟨a, ha⟩ := p.exists_pos (Set.mem_univ x)
    exact ⟨a, ne_of_gt ha⟩
  case locally_finite =>
    exact p.locallyFinite
  case refinement =>
    intro b
    exact ⟨b, subset_closure.trans (hp b)⟩
end helper

noncomputable def cb_radial_proj {n : ℕ} (x : cb (n + 1)) : @cb_boundary (n + 1) :=
  ⟨sph_to_cb ⟨pre_proj_to_sph (Nat.le_add_left 1 n) x.1,
    pre_proj_to_sph_in_sph (Nat.le_add_left 1 n) x.1⟩,
   ⟨⟨pre_proj_to_sph (Nat.le_add_left 1 n) x.1,
     pre_proj_to_sph_in_sph (Nat.le_add_left 1 n) x.1⟩, rfl⟩⟩

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X]
open CellComplexClass
open Classical

structure CompatibleSkeletonPOU (α : Type*) (s : α → Set X) (n : ℕ) where
  toFun : α → C(Skeleton X n, ℝ)
  nonneg : ∀ a (x : Skeleton X n), 0 ≤ toFun a x
  sum_eq_one : ∀ x : Skeleton X n, ∑ᶠ a, toFun a x = 1
  locallyFinite : LocallyFinite (fun a => Function.support (toFun a))
  subordinate : ∀ a, tsupport (toFun a) ⊆ (Subtype.val ⁻¹' (s a))

noncomputable def skeleton_pou_zero
    (s : α → Set X) (_hs_open : ∀ a, IsOpen (s a)) (hs_cover : ⋃ a, s a = Set.univ) :
    CompatibleSkeletonPOU α s 0 := by
  haveI : DiscreteTopology (Skeleton X 0) := skeleton0_discrete
  -- For each point in the 0-skeleton, choose a covering index
  have h_mem : ∀ x : Skeleton X 0, ∃ a : α, (x : X) ∈ s a := by
    intro x
    have : (x : X) ∈ ⋃ a, s a := hs_cover ▸ Set.mem_univ _
    exact Set.mem_iUnion.mp this
  let idx : Skeleton X 0 → α := fun x => (h_mem x).choose
  have h_idx : ∀ x, (x : X) ∈ s (idx x) := fun x => (h_mem x).choose_spec
  refine ⟨fun a => ⟨fun x => if idx x = a then 1 else 0, continuous_of_discreteTopology⟩,
    ?_, ?_, ?_, ?_⟩
  · -- nonneg
    intro a x
    simp only [ContinuousMap.coe_mk]
    split_ifs <;> norm_num
  · -- sum_eq_one
    intro x
    simp only [ContinuousMap.coe_mk]
    convert finsum_eq_single _ (idx x) (fun b hb => ?_) using 1
    · simp
    · simp [Ne.symm hb]
  · -- locallyFinite
    intro x
    refine ⟨{x}, (isOpen_discrete _).mem_nhds rfl, ?_⟩
    apply Set.Finite.subset (Set.finite_singleton (idx x))
    intro a ha
    simp only [Set.mem_singleton_iff]
    obtain ⟨y, hy_supp, hy_mem⟩ := ha
    rw [Set.mem_singleton_iff] at hy_mem
    subst hy_mem
    rw [Function.mem_support] at hy_supp
    simp only [ContinuousMap.coe_mk] at hy_supp
    by_contra h
    exact hy_supp (if_neg (Ne.symm h))
  · -- subordinate
    intro a
    apply subset_trans (closure_minimal (fun x hx => ?_) (isClosed_discrete _))
      (le_refl _)
    rw [Function.mem_support] at hx
    simp only [ContinuousMap.coe_mk] at hx
    simp only [Set.mem_preimage]
    have h_eq : idx x = a := by
      by_contra h
      exact hx (if_neg h)
    rw [← h_eq]
    exact h_idx x

omit CW in theorem exists_cb_pou_on_cell
    {α : Type*} (s : α → Set X) (hs_open : ∀ a, IsOpen (s a)) (hs_cover : ⋃ a, s a = Set.univ)
    (n : ℕ) (γ : CellOfDim (n + 1)) (pou_n : CompatibleSkeletonPOU α s n) :
    ∃ cb_pou : α → C(cb (n + 1), ℝ),
      (∀ a x, 0 ≤ cb_pou a x) ∧
      (∀ x, ∑ᶠ a, cb_pou a x = 1) ∧
      (∀ a, tsupport (cb_pou a) ⊆ (characteristic_cn (n + 1) γ) ⁻¹' (s a)) ∧
      (∀ a x (hx : x ∈ cb_boundary),
        cb_pou a x =
          pou_n.toFun a
            ⟨characteristic_cn (n + 1) γ x, char_cnp1_boundary_in_skn n γ x hx⟩) ∧
      (∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        ∀ a (x : cb (n + 1)), (1 - ε / 2 : ℝ) < ‖x.1‖ →
          cb_pou a x = pou_n.toFun a
            ⟨characteristic_cn (n + 1) γ (cb_radial_proj x).1,
             char_cnp1_boundary_in_skn n γ (cb_radial_proj x).1
               (cb_radial_proj x).2⟩) := by
  let boundary_pullback : α → cb_boundary → ℝ := fun a z =>
    pou_n.toFun a
      ⟨characteristic_cn (n + 1) γ z.1, char_cnp1_boundary_in_skn n γ z.1 z.2⟩
  have h_boundary_pullback_cont : ∀ a, Continuous (boundary_pullback a) := by
    intro a
    change Continuous (fun z : cb_boundary =>
      pou_n.toFun a
        ⟨characteristic_cn (n + 1) γ z.1, char_cnp1_boundary_in_skn n γ z.1 z.2⟩)
    refine (pou_n.toFun a).continuous.comp ?_
    refine Continuous.subtype_mk ?_ (fun z : cb_boundary => char_cnp1_boundary_in_skn n γ z.1 z.2)
    change Continuous (fun z : cb_boundary => characteristic_cn (n + 1) γ z.1)
    have h_char : Continuous (characteristic_cn (n + 1) γ) := by
      rcases γ with ⟨e, he⟩
      change Continuous (fun x : cb (n + 1) =>
        C.characteristic_map e ((congrArg (fun p ↦ (cb p : Type)) he).mpr x))
      refine Continuous.comp (C.characteristic_map_continuous e) ?_
      exact @Eq.rec ℕ (C.dim_map e)
        (fun m hm => Continuous ((congrArg (fun p ↦ (cb p : Type)) hm).mpr))
        continuous_id (n + 1) he
    exact h_char.comp continuous_subtype_val
  have h_cb_preimage_cover_open :
      (∀ a, IsOpen ((characteristic_cn (n + 1) γ) ⁻¹' (s a))) ∧
      (⋃ a, (characteristic_cn (n + 1) γ) ⁻¹' (s a) = Set.univ) := by
    have h_char_cont : Continuous (characteristic_cn (n + 1) γ) := by
      rcases γ with ⟨e, he⟩
      change Continuous (fun x : cb (n + 1) =>
        C.characteristic_map e ((congrArg (fun p ↦ (cb p : Type)) he).mpr x))
      refine Continuous.comp (C.characteristic_map_continuous e) ?_
      exact @Eq.rec ℕ (C.dim_map e)
        (fun m hm => Continuous ((congrArg (fun p ↦ (cb p : Type)) hm).mpr))
        continuous_id (n + 1) he
    refine ⟨?_, ?_⟩
    · intro a
      exact (hs_open a).preimage h_char_cont
    · rw [Set.iUnion_eq_univ_iff]
      intro x
      have hx : characteristic_cn (n + 1) γ x ∈ ⋃ a, s a := by
        simp [hs_cover]
      simpa [Set.mem_iUnion, Set.mem_preimage] using hx
  have h_exists_eta_on_cb :
      ∃ η : PartitionOfUnity α (cb (n + 1)),
        η.IsSubordinate (fun a => (characteristic_cn (n + 1) γ) ⁻¹' (s a)) := by
    rcases h_cb_preimage_cover_open with ⟨hopen, hcover⟩
    have hcover_subset : (Set.univ : Set (cb (n + 1))) ⊆
        ⋃ a, (characteristic_cn (n + 1) γ) ⁻¹' (s a) := by
      simp [hcover]
    simpa using
      (PartitionOfUnity.exists_isSubordinate
        (X := cb (n + 1)) (s := Set.univ)
        isClosed_univ
        (fun a => (characteristic_cn (n + 1) γ) ⁻¹' (s a))
        hopen hcover_subset)
  have h_exists_finite_active_boundary :
      ∃ t : Finset α, ∀ a, a ∉ t → boundary_pullback a = 0 := by
    classical
    let boundary_to_skeleton : cb_boundary → Skeleton X n := fun z =>
      ⟨characteristic_cn (n + 1) γ z.1, char_cnp1_boundary_in_skn n γ z.1 z.2⟩
    have h_boundary_to_skeleton_cont : Continuous boundary_to_skeleton := by
      refine Continuous.subtype_mk ?_ (fun z : cb_boundary => char_cnp1_boundary_in_skn n γ z.1 z.2)
      change Continuous (fun z : cb_boundary => characteristic_cn (n + 1) γ z.1)
      have h_char : Continuous (characteristic_cn (n + 1) γ) := by
        rcases γ with ⟨e, he⟩
        change Continuous (fun x : cb (n + 1) =>
          C.characteristic_map e ((congrArg (fun p ↦ (cb p : Type)) he).mpr x))
        refine Continuous.comp (C.characteristic_map_continuous e) ?_
        exact @Eq.rec ℕ (C.dim_map e)
          (fun m hm => Continuous ((congrArg (fun p ↦ (cb p : Type)) hm).mpr))
          continuous_id (n + 1) he
      exact h_char.comp continuous_subtype_val
    have h_cb_boundary_compact : IsCompact (@cb_boundary (n + 1)) := by
      exact (isCompact_univ.of_isClosed_subset cb_boundary_closed (by intro x hx; trivial))
    let K : Set (Skeleton X n) := Set.range boundary_to_skeleton
    have hK_compact : IsCompact K := by
      letI : CompactSpace cb_boundary := isCompact_iff_compactSpace.mp h_cb_boundary_compact
      exact isCompact_range h_boundary_to_skeleton_cont
    have h_finite :
        {a | (Function.support (pou_n.toFun a) ∩ K).Nonempty}.Finite := by
      simpa [K] using pou_n.locallyFinite.finite_nonempty_inter_compact hK_compact
    refine ⟨h_finite.toFinset, ?_⟩
    intro a ha
    funext z
    by_contra hz
    have hz_support :
        ⟨characteristic_cn (n + 1) γ z.1, char_cnp1_boundary_in_skn n γ z.1 z.2⟩
          ∈ Function.support (pou_n.toFun a) := by
      rw [Function.mem_support]
      simpa [boundary_pullback] using hz
    have ha_mem :
        a ∈ {a | (Function.support (pou_n.toFun a) ∩ K).Nonempty} := by
      exact ⟨_, hz_support, ⟨z, rfl⟩⟩
    have ha_in_t : a ∈ h_finite.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ha_mem
    exact ha ha_in_t

  let collar_of (A : Set (@cb_boundary (n + 1))) (ε : ℝ) : Set (cb (n + 1)) :=
    {x |
      cb_radial_proj x ∈ A ∧
      (1 - ε : ℝ) < ‖x.1‖ ∧ ‖x.1‖ ≤ 1}
  let boundary_collar (ε : ℝ) : Set (cb (n + 1)) :=
    {x | (1 - ε : ℝ) < ‖x.1‖}
  let inner_core (ε : ℝ) : Set (cb (n + 1)) :=
    {x | ‖x.1‖ ≤ (1 - ε : ℝ)}
  have h_exists_uniform_epsilon :
      ∀ t : Finset α, (∀ a, a ∉ t → boundary_pullback a = 0) →
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
          ∀ a, closure (collar_of (tsupport (boundary_pullback a)) ε) ⊆
            (characteristic_cn (n + 1) γ) ⁻¹' (s a) := by
    intro t ht
    have h_boundary_pullback_subordinate: ∀ a, (↑) '' tsupport (boundary_pullback a) ⊆ ((characteristic_cn (n + 1) γ) ⁻¹' (s a)) := by
      intro a
      let g : cb_boundary → Skeleton X n := fun z =>
        ⟨characteristic_cn (n + 1) γ z.1, char_cnp1_boundary_in_skn n γ z.1 z.2⟩
      have hg_cont : Continuous g := by
        refine Continuous.subtype_mk ?_
          (fun z : cb_boundary => char_cnp1_boundary_in_skn n γ z.1 z.2)
        change Continuous (fun z : cb_boundary => characteristic_cn (n + 1) γ z.1)
        have h_char_cont : Continuous (characteristic_cn (n + 1) γ) := by
          rcases γ with ⟨e, he⟩
          change Continuous (fun x : cb (n + 1) =>
            C.characteristic_map e ((congrArg (fun p ↦ (cb p : Type)) he).mpr x))
          exact Continuous.comp (C.characteristic_map_continuous e)
            (@Eq.rec ℕ (C.dim_map e)
              (fun m hm => Continuous ((congrArg (fun p ↦ (cb p : Type)) hm).mpr))
              continuous_id (n + 1) he)
        exact h_char_cont.comp continuous_subtype_val
      have h_support : Function.support (boundary_pullback a) ⊆
          g ⁻¹' (Function.support (pou_n.toFun a)) := by
        intro z hz; exact hz
      have h_tsupport_sub : tsupport (boundary_pullback a) ⊆
          g ⁻¹' (tsupport (pou_n.toFun a)) :=
        (closure_mono h_support).trans (hg_cont.closure_preimage_subset _)
      rintro y ⟨z, hz_mem, rfl⟩
      exact pou_n.subordinate a (h_tsupport_sub hz_mem)
    have h_boundary_pullback_thicken_subset: ∀ a, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        closure (collar_of (tsupport (boundary_pullback a)) ε) ⊆
          (characteristic_cn (n + 1) γ) ⁻¹' (s a) := by
      intro a
      have hK_compact : IsCompact ((Subtype.val : cb_boundary → cb (n + 1)) ''
          tsupport (boundary_pullback a)) := by
        have h_bd_compact : IsCompact (@cb_boundary (n + 1)) :=
          isCompact_univ.of_isClosed_subset cb_boundary_closed fun x _ => trivial
        haveI : CompactSpace (cb_boundary : Set (cb (n + 1))) :=
          isCompact_iff_compactSpace.mp h_bd_compact
        exact (isClosed_tsupport (boundary_pullback a)).isCompact.image continuous_subtype_val
      have hU_open : IsOpen ((characteristic_cn (n + 1) γ) ⁻¹' (s a)) :=
        h_cb_preimage_cover_open.1 a
      obtain ⟨δ, hδ_pos, hδ_thick⟩ :=
        hK_compact.exists_thickening_subset_open hU_open (h_boundary_pullback_subordinate a)
      refine ⟨min (δ / 2) (1 / 2), by positivity,
        by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)], ?_⟩
      -- Chain: closure (collar) ⊆ cthickening (δ/2) K ⊆ thickening δ K ⊆ U
      have h_collar_sub_cthick : collar_of (tsupport (boundary_pullback a)) (min (δ / 2) (1 / 2)) ⊆
          Metric.cthickening (δ / 2) ((Subtype.val : cb_boundary → cb (n + 1)) ''
            tsupport (boundary_pullback a)) := by
        intro x hx
        obtain ⟨hx_proj, hx_low, hx_high⟩ := hx
        apply Metric.thickening_subset_cthickening
        have hx_norm_pos : 0 < ‖x.1‖ := by linarith [min_le_right (δ / 2) (1 / 2 : ℝ)]
        have hx_ne : x.1 ≠ 0 := norm_pos_iff.mp hx_norm_pos
        have h_proj_val : ((↑(cb_radial_proj x) : cb (n + 1)) : EuclideanSpace ℝ (Fin (n + 1))) =
            (1 / ‖x.1‖) • x.1 := by
          show (sph_to_cb ⟨pre_proj_to_sph (Nat.le_add_left 1 n) x.1,
            pre_proj_to_sph_in_sph (Nat.le_add_left 1 n) x.1⟩).1 = (1 / ‖x.1‖) • x.1
          simp [sph_to_cb, pre_proj_to_sph, hx_ne]
        have h_dist_eq : dist x (↑(cb_radial_proj x) : cb (n + 1)) = 1 - ‖x.1‖ := by
          rw [Subtype.dist_eq, dist_eq_norm, h_proj_val,
            show x.1 - (1 / ‖x.1‖) • x.1 = (1 - 1 / ‖x.1‖) • x.1 from by
              rw [sub_smul, one_smul],
            norm_smul, Real.norm_eq_abs,
            abs_of_nonpos (sub_nonpos.mpr ((le_div_iff₀ hx_norm_pos).mpr (by linarith)))]
          field_simp; ring
        rw [Metric.mem_thickening_iff]
        exact ⟨↑(cb_radial_proj x), ⟨cb_radial_proj x, hx_proj, rfl⟩,
          by rw [h_dist_eq]; linarith [min_le_left (δ / 2) (1 / 2 : ℝ)]⟩
      exact (closure_minimal h_collar_sub_cthick Metric.isClosed_cthickening).trans
        ((Metric.cthickening_subset_thickening' hδ_pos (half_lt_self hδ_pos) _).trans hδ_thick)
    choose f_a_ε hε₁ hε₂ hε₃ using h_boundary_pullback_thicken_subset
    -- For a ∉ t, boundary_pullback vanishes so tsupport is empty
    have h_outside_t : ∀ a, a ∉ t → tsupport (boundary_pullback a) = ∅ := by
      intro a ha
      change closure (Function.support (boundary_pullback a)) = ∅
      rw [Function.support_eq_empty_iff.mpr (ht a ha), closure_empty]
    by_cases ht_ne : t.Nonempty
    · -- t nonempty: take ε = inf' of f_a_ε over t
      obtain ⟨a₀, ha₀⟩ := ht_ne
      refine ⟨t.inf' ⟨a₀, ha₀⟩ f_a_ε,
        (Finset.lt_inf'_iff ⟨a₀, ha₀⟩).mpr fun a _ => hε₁ a,
        lt_of_le_of_lt (Finset.inf'_le f_a_ε ha₀) (hε₂ a₀), fun a => ?_⟩
      by_cases ha : a ∈ t
      · -- a ∈ t: closure_mono (smaller ε → thinner collar → smaller closure)
        refine (closure_mono ?_).trans (hε₃ a)
        intro x ⟨hx_proj, hx_low, hx_high⟩
        exact ⟨hx_proj, by linarith [Finset.inf'_le f_a_ε ha], hx_high⟩
      · -- a ∉ t: collar is empty (tsupport is empty)
        suffices h : collar_of (tsupport (boundary_pullback a)) (t.inf' ⟨a₀, ha₀⟩ f_a_ε) = ∅ by
          rw [h, closure_empty]; exact Set.empty_subset _
        ext x; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx_proj, _, _⟩; simp [h_outside_t a ha] at hx_proj
    · -- t empty: all boundary_pullbacks vanish, any ε works
      rw [Finset.not_nonempty_iff_eq_empty] at ht_ne
      refine ⟨1 / 2, by norm_num, by norm_num, fun a => ?_⟩
      suffices h : collar_of (tsupport (boundary_pullback a)) (1 / 2 : ℝ) = ∅ by
        rw [h, closure_empty]; exact Set.empty_subset _
      ext x; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx_proj, _, _⟩; simp [h_outside_t a (by simp [ht_ne])] at hx_proj
  have h_exists_sigma :
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ σ : C(cb (n + 1), ℝ),
          (∀ x, 0 ≤ σ x ∧ σ x ≤ 1) ∧
          (∀ x, x ∈ inner_core ε → σ x = 1) ∧
          (∀ x, x ∈ boundary_collar (ε / 2) → σ x = 0) := by
    intro ε hε0 hε1
    let s0 : Set (cb (n + 1)) := {x | (1 - ε / 2 : ℝ) ≤ ‖x.1‖}
    let s1 : Set (cb (n + 1)) := inner_core ε
    have hs0 : IsClosed s0 := by
      refine isClosed_le continuous_const ?_
      exact (continuous_norm.comp continuous_subtype_val)
    have hs1 : IsClosed s1 := by
      change IsClosed {x : cb (n + 1) | ‖x.1‖ ≤ (1 - ε : ℝ)}
      refine isClosed_le ?_ continuous_const
      exact (continuous_norm.comp continuous_subtype_val)
    have hs01 : Disjoint s0 s1 := by
      rw [Set.disjoint_iff]
      intro x hx
      have hx0 : (1 - ε / 2 : ℝ) ≤ ‖x.1‖ := hx.1
      have hx1 : ‖x.1‖ ≤ (1 - ε : ℝ) := by
        simpa [s1, inner_core] using hx.2
      have hlt : (1 - ε : ℝ) < (1 - ε / 2 : ℝ) := by linarith
      linarith
    obtain ⟨σ, hσ0, hσ1, hσIcc⟩ := exists_continuous_zero_one_of_isClosed hs0 hs1 hs01
    refine ⟨σ, ?_, ?_, ?_⟩
    · intro x
      have hxIcc : σ x ∈ Set.Icc (0 : ℝ) 1 := hσIcc x
      exact ⟨hxIcc.1, hxIcc.2⟩
    · intro x hx
      simpa [s1, inner_core] using hσ1 hx
    · intro x hx
      have hx0 : x ∈ s0 := by
        change (1 - ε / 2 : ℝ) ≤ ‖x.1‖
        exact le_of_lt hx
      simpa [s0] using hσ0 hx0
  -- the original text here does not consider the case for x == 0, however we need only extension to be equal to the value on boundary
  have h_exists_boundary_extension :
      ∃ phi : α → C(cb (n + 1), ℝ),
        ∀ a x (hx : x ∈ cb_boundary), phi a x = boundary_pullback a ⟨x, hx⟩ := by
    refine ⟨fun a => ⟨cb_extension (Nat.le_add_left 1 n) (boundary_pullback a),
      cb_extension_continuous (Nat.le_add_left 1 n) (h_boundary_pullback_cont a)⟩, ?_⟩
    intro a x hx
    exact cb_extension_eq_on_boundary (Nat.le_add_left 1 n) (boundary_pullback a) x hx

  obtain ⟨η, hη_sub⟩ := h_exists_eta_on_cb
  obtain ⟨t, ht_zero⟩ := h_exists_finite_active_boundary
  obtain ⟨ε, hε_pos, hε_lt_one, hε_sub⟩ := h_exists_uniform_epsilon t ht_zero
  obtain ⟨σ, hσ_range, hσ_inner, hσ_boundary⟩ := h_exists_sigma ε hε_pos hε_lt_one
  -- Radial pullback: for x ≠ 0, project x to boundary via x/‖x‖ and evaluate boundary_pullback.
  -- At x = 0, assign 0 (this value is irrelevant since σ(0) = 1 kills the phi term).
  let phi : α → cb (n + 1) → ℝ := fun a x =>
    if x.1 = 0 then 0
    else boundary_pullback a (cb_radial_proj x)
  let cb_pou_candidate : α → cb (n + 1) → ℝ := fun a x =>
    σ x * η a x + (1 - σ x) * phi a x
  have cb_pou_candidate_nonneg : ∀ a x, 0 ≤ cb_pou_candidate a x := by
    intro a x
    have hσ0 : 0 ≤ σ x := (hσ_range x).1
    have hσ1 : σ x ≤ 1 := (hσ_range x).2
    have hη0 : 0 ≤ η a x := η.nonneg a x
    have hphi0 : 0 ≤ phi a x := by
      show 0 ≤ phi a x
      simp only [phi]
      split_ifs with h
      · exact le_refl 0
      · exact pou_n.nonneg a _
    have hmul1 : 0 ≤ σ x * η a x := mul_nonneg hσ0 hη0
    have hmul2 : 0 ≤ (1 - σ x) * phi a x := mul_nonneg (sub_nonneg.mpr hσ1) hphi0
    simpa [cb_pou_candidate] using add_nonneg hmul1 hmul2

  -- phi a x = 0 whenever a ∉ t (boundary pullback vanishes outside finite active set)
  have h_phi_zero_outside : ∀ a, a ∉ t → ∀ x, phi a x = 0 := by
    intro a ha x
    simp only [phi]
    split_ifs with h
    · rfl
    · exact congr_fun (ht_zero a ha) _

  -- Support of fun a => phi a x is contained in t (finite)
  have h_phi_support_finite : ∀ x, (Function.support (fun a => phi a x)).Finite := by
    intro x
    exact (t.finite_toSet).subset fun a ha => by
      rw [Function.mem_support] at ha
      exact Finset.mem_coe.mpr (by_contra fun h => ha (h_phi_zero_outside a h x))

  -- Support of fun a => η a x is finite (from η.locallyFinite)
  have h_eta_support_finite : ∀ x, (Function.support (fun a => η a x)).Finite := by
    intro x
    exact η.locallyFinite.point_finite x

  have cb_pou_candidate_sum_eq_one : ∀ x, ∑ᶠ a, cb_pou_candidate a x = 1 := by
    intro x
    -- Finite support of the two summand families
    have h1_fin : (Function.support (fun a => σ x * η a x)).Finite :=
      (h_eta_support_finite x).subset fun a ha => by
        rw [Function.mem_support] at ha ⊢; exact right_ne_zero_of_mul ha
    have h2_fin : (Function.support (fun a => (1 - σ x) * phi a x)).Finite :=
      (h_phi_support_finite x).subset fun a ha => by
        rw [Function.mem_support] at ha ⊢; exact right_ne_zero_of_mul ha
    -- Distribute the finsum
    have h_split : ∑ᶠ a, cb_pou_candidate a x =
        (∑ᶠ a, σ x * η a x) + (∑ᶠ a, (1 - σ x) * phi a x) := by
      have h_eq : ∀ a, cb_pou_candidate a x = σ x * η a x + (1 - σ x) * phi a x :=
        fun _ => rfl
      simp_rw [h_eq]
      exact finsum_add_distrib h1_fin h2_fin
    -- Factor out constants
    rw [h_split,
      (mul_finsum' _ _ (h_eta_support_finite x)).symm,
      (mul_finsum' _ _ (h_phi_support_finite x)).symm,
      η.sum_eq_one (Set.mem_univ x), mul_one]
    -- Goal: σ x + (1 - σ x) * ∑ᶠ a, phi a x = 1
    by_cases hx : x.1 = 0
    · -- x = 0: σ x = 1 since 0 ∈ inner_core ε
      have hx_inner : x ∈ inner_core ε := by
        simp only [inner_core, Set.mem_setOf_eq]
        rw [hx, norm_zero]
        linarith
      rw [hσ_inner x hx_inner]; ring
    · -- x ≠ 0: ∑ᶠ a, phi a x = 1 by radial pullback from pou_n
      suffices h_phi_sum : ∑ᶠ a, phi a x = 1 by rw [h_phi_sum]; ring
      -- The projected boundary point and corresponding skeleton point
      let z : @cb_boundary (n + 1) := cb_radial_proj x
      let sk : Skeleton X n :=
        ⟨characteristic_cn (n + 1) γ z.1, char_cnp1_boundary_in_skn n γ z.1 z.2⟩
      -- phi a x = pou_n.toFun a sk for all a (by unfolding definitions)
      have h_eq : ∀ a, phi a x = pou_n.toFun a sk := by
        intro a
        show (if x.1 = 0 then (0 : ℝ) else boundary_pullback a z) = pou_n.toFun a sk
        rw [if_neg hx]
      simp_rw [h_eq]
      exact pou_n.sum_eq_one sk

  have cb_pou_candidate_subordinate :
      ∀ a, tsupport (cb_pou_candidate a) ⊆ (characteristic_cn (n + 1) γ) ⁻¹' (s a) := by
    intro a
    have h_sub_sigma_eta :
        tsupport (fun x => σ x * η a x) ⊆ (characteristic_cn (n + 1) γ) ⁻¹' (s a) := by
      exact
        (tsupport_mul_subset_right
          (f := fun x : cb (n + 1) => σ x)
          (g := fun x : cb (n + 1) => η a x)).trans (hη_sub a)
    have h_sub_1_sub_sigma_phi:
        tsupport (fun x => (1 - σ x) * phi a x) ⊆ (characteristic_cn (n + 1) γ) ⁻¹' (s a) := by
      refine (closure_mono ?_).trans (hε_sub a)
      intro x hx
      have h1 : (1 : ℝ) - σ x ≠ 0 := left_ne_zero_of_mul hx
      have h2 : phi a x ≠ 0 := right_ne_zero_of_mul hx
      have hx_not_inner : x ∉ inner_core ε :=
        fun h => h1 (by rw [hσ_inner x h]; ring)
      have hx_norm_gt : (1 - ε : ℝ) < ‖x.1‖ := not_le.mp hx_not_inner
      have hx_ne_zero : x.1 ≠ 0 := fun h => h2 (if_pos h)
      have h_bp_ne_zero : boundary_pullback a (cb_radial_proj x) ≠ 0 :=
        fun h => h2 ((if_neg hx_ne_zero).trans h)
      exact ⟨subset_closure h_bp_ne_zero, hx_norm_gt,
        by have := x.property; change x.1 ∈ Metric.closedBall 0 1 at this
           rwa [Metric.mem_closedBall', dist_zero] at this⟩
    exact (tsupport_add (fun x => σ x * η a x) (fun x => (1 - σ x) * phi a x)).trans
      (Set.union_subset h_sub_sigma_eta h_sub_1_sub_sigma_phi)

  have cb_pou_candidate_boundary : ∀ a x (hx : x ∈ cb_boundary),
      cb_pou_candidate a x =
        pou_n.toFun a ⟨characteristic_cn (n + 1) γ x, char_cnp1_boundary_in_skn n γ x hx⟩ := by
    intro a x hx
    obtain ⟨y, hy⟩ := hx
    have hx_norm : ‖x.1‖ = 1 := by
      have : x.1 = y.1 := congr_arg Subtype.val (hy.symm)
      rw [this, ← dist_zero, ← Metric.mem_sphere']
      exact y.property
    have hσ_zero : σ x = 0 :=
      hσ_boundary x (show (1 - ε / 2 : ℝ) < ‖x.1‖ by rw [hx_norm]; linarith)
    have hx_ne : x.1 ≠ 0 := fun h => by simp [h] at hx_norm
    show σ x * η a x + (1 - σ x) * phi a x = _
    rw [hσ_zero, zero_mul, zero_add, sub_zero, one_mul]
    show (if x.1 = 0 then (0 : ℝ) else boundary_pullback a (cb_radial_proj x)) = _
    rw [if_neg hx_ne]
    have h_radial_eq : (cb_radial_proj x).1 = x := by
      apply Subtype.ext
      change pre_proj_to_sph (Nat.le_add_left 1 n) x.1 = x.1
      simp [pre_proj_to_sph, hx_ne, hx_norm]
    exact congr_arg (boundary_pullback a)
      (show cb_radial_proj x = ⟨x, ⟨y, hy⟩⟩ from Subtype.ext h_radial_eq)

  have cb_pou_candidate_cont : ∀ a, Continuous (cb_pou_candidate a) := by
    intro a
    have h_term1 : Continuous (fun x => σ x * η a x) :=
      σ.continuous.mul (η a).continuous
    suffices h_term2 : Continuous (fun x => (1 - σ x) * phi a x) from
      h_term1.add h_term2
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_ne : x.1 = (0 : EuclideanSpace ℝ (Fin (n + 1)))
    · -- At origin: locally zero since σ = 1 on inner_core ε
      have hU_open : IsOpen {y : cb (n + 1) | ‖y.1‖ < 1 - ε} :=
        isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
      have hx_in_U : x ∈ {y : cb (n + 1) | ‖y.1‖ < 1 - ε} := by
        show ‖x.1‖ < 1 - ε; rw [hx_ne, norm_zero]; linarith
      refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hU_open.mem_nhds hx_in_U] with y hy
      rw [hσ_inner y (le_of_lt hy), sub_self, zero_mul]
    · -- Away from origin: phi a equals bp a ∘ rp near x, which is continuous
      -- ContinuousAt of to_sph at nonzero points
      let to_sph : EuclideanSpace ℝ (Fin (n + 1)) → sph (n + 1) :=
        fun v => ⟨pre_proj_to_sph (Nat.le_add_left 1 n) v,
          pre_proj_to_sph_in_sph (Nat.le_add_left 1 n) v⟩
      have h_to_sph_cat : ContinuousAt to_sph x.1 := by
        show (nhds x.1).map to_sph ≤ nhds (to_sph x.1)
        have : (nhds x.1).map (Subtype.val ∘ to_sph) ≤ nhds (to_sph x.1).1 :=
          pre_proj_to_sph_cont_at_nonzero (Nat.le_add_left 1 n) x.1 hx_ne
        rwa [← Filter.map_map, Filter.map_le_iff_le_comap, ← nhds_subtype] at this
      -- sph → cb_boundary is continuous
      let sph_to_bd : sph (n + 1) → @cb_boundary (n + 1) :=
        fun s => ⟨sph_to_cb s, ⟨s, rfl⟩⟩
      have h_sph_to_bd_cont : Continuous sph_to_bd :=
        (continuous_subtype_val.subtype_mk (fun x => sph_in_cb x.prop)).subtype_mk _
      -- bp a ∘ rp = (bp a ∘ sph_to_bd) ∘ to_sph ∘ Subtype.val
      have h_bp_rp_cat : ContinuousAt
          (fun y : cb (n + 1) => boundary_pullback a (cb_radial_proj y)) x :=
        ((h_boundary_pullback_cont a).comp h_sph_to_bd_cont).continuousAt.comp
          (h_to_sph_cat.comp continuous_subtype_val.continuousAt)
      -- (1 - σ) * (bp a ∘ rp) is ContinuousAt
      have h_rhs_cat : ContinuousAt
          (fun y => (1 - σ y) * boundary_pullback a (cb_radial_proj y)) x :=
        (continuous_const.sub σ.continuous).continuousAt.mul h_bp_rp_cat
      -- The actual function equals the above near x (since phi a = bp a ∘ rp when y.1 ≠ 0)
      refine h_rhs_cat.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_ne.preimage continuous_subtype_val).mem_nhds hx_ne] with y hy
      congr 1; exact if_neg hy

  have cb_pou_candidate_collar : ∃ ε' : ℝ, 0 < ε' ∧ ε' < 1 ∧
      ∀ a (x : cb (n + 1)), (1 - ε' / 2 : ℝ) < ‖x.1‖ →
        cb_pou_candidate a x = pou_n.toFun a
          ⟨characteristic_cn (n + 1) γ (cb_radial_proj x).1,
           char_cnp1_boundary_in_skn n γ (cb_radial_proj x).1
             (cb_radial_proj x).2⟩ := by
    refine ⟨ε, hε_pos, hε_lt_one, fun a x hx_collar => ?_⟩
    have hx_ne : x.1 ≠ 0 := by
      intro h; simp [h] at hx_collar; linarith
    have hσ_zero : σ x = 0 := hσ_boundary x hx_collar
    show σ x * η a x + (1 - σ x) * phi a x = _
    rw [hσ_zero, zero_mul, zero_add, sub_zero, one_mul]
    show (if x.1 = 0 then (0 : ℝ) else boundary_pullback a (cb_radial_proj x)) = _
    rw [if_neg hx_ne]

  exact ⟨fun a => ⟨cb_pou_candidate a, cb_pou_candidate_cont a⟩,
    cb_pou_candidate_nonneg,
    cb_pou_candidate_sum_eq_one,
    cb_pou_candidate_subordinate,
    cb_pou_candidate_boundary,
    cb_pou_candidate_collar⟩

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
            (∀ y ∈ V', pou_succ.toFun a y = 0))) := by
  sorry

instance instCWComplexParacompactSpace : ParacompactSpace X := by
  apply paracompact_of_exist_partition_of_unity
  intro α s hs_open hs_cover
  sorry


end

end Chp5
