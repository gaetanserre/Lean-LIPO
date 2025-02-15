import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set

namespace IsCompact

variable {α : Type} [TopologicalSpace α] {Ω : Set α} (h : IsCompact Ω)

include h

lemma nullMeasurable [MeasureSpace α] [OpensMeasurableSpace α] [T2Space α] :
    NullMeasurableSet Ω :=
  h.measurableSet.nullMeasurableSet

lemma exists_argmax {β : Type} [TopologicalSpace β] [LinearOrder β] [ClosedIciTopology β]
    {f : Ω → β} (hf : Continuous f) (hne : Ω.Nonempty) : ∃ x, ∀ y, f y ≤ f x := by
  have univ_compact : IsCompact (univ : Set Ω) := by
    rwa [Subtype.isCompact_iff, Subtype.coe_image_univ Ω]
  have univ_ne : (univ : Set Ω).Nonempty := by
    use ⟨hne.some, hne.some_mem⟩
    trivial
  obtain ⟨x, _, hx⟩ := univ_compact.exists_isMaxOn univ_ne hf.continuousOn
  use x
  exact fun _ ↦ hx (trivial)

lemma exists_argmin {β : Type} [TopologicalSpace β] [LinearOrder β] [ClosedIicTopology β]
    {f : Ω → β} (hf : Continuous f) (hne : Ω.Nonempty) : ∃ x, ∀ y, f x ≤ f y := by
  have univ_compact : IsCompact (univ : Set Ω) := by
    rwa [Subtype.isCompact_iff, Subtype.coe_image_univ Ω]
  have univ_ne : (univ : Set Ω).Nonempty := by
    use ⟨hne.some, hne.some_mem⟩
    trivial
  obtain ⟨x, _, hx⟩ := univ_compact.exists_isMinOn univ_ne hf.continuousOn
  use x
  exact fun _ ↦ hx (trivial)

end IsCompact
