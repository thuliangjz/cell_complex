import MyProject.TopologicalProperties

open BigOperators

namespace Chp5

section
variable {X: Type*} [TopologicalSpace X] [T2Space X] [C: CellComplexClass X] [CW: CWComplexClass X]
theorem quotient_sigma_cb_map : Topology.IsQuotientMap (fun (⟨e, d⟩: (_:C.sets) × cb (C.dim_map _)) ↦ C.characteristic_map e d) := by
  let B := {closure s | s ∈ C.sets}
  let φ := fun (⟨e, d⟩: (_:C.sets) × cb (C.dim_map _)) ↦ C.characteristic_map e d
  let γ : ((e:C.sets) × cb (C.dim_map e)) → ((b:B) × (b.1)) := by
    rintro ⟨e, d⟩
    use ⟨closure e.1, ⟨e.1, And.intro e.2 rfl⟩⟩
    simp
    use C.characteristic_map e d
    rw [←C.characteristic_map_range e]
    exact Set.mem_range_self d
  let η := CoeherentSigmaMap B
  have : φ = η ∘ γ := by
    ext x
    simp [φ, γ, η, CoeherentSigmaMap]
  sorry
end

end Chp5
