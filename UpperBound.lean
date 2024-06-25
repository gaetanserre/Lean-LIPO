/-
  Created in 2024 by Gaëtan Serré
-/

/-
  Formalization of the proof on the upper bound of the probability for LIPO to reject a candidate.
-/

import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open Metric Finset MeasureTheory ENNReal Set

/- The dimension of the space. -/
variable {d : ℕ} (hd : 0 < d)

/-- Utility lemma: the the bigger the radius of a ball, the bigger its volume. -/
lemma volume_mono (x₁ x₂ : EuclideanSpace ℝ (Fin d))
    (r₁ r₂ : ℝ) (h : r₁ ≤ r₂) : volume (ball x₁ r₁) ≤ volume (ball x₂ r₂) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  repeat rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  have h1 : ENNReal.ofReal (√Real.pi ^ d / ((d : ℝ) / 2 + 1).Gamma) ≠ 0 := by
    suffices 0 < √Real.pi ^ d / ((d : ℝ) / 2 + 1).Gamma by
      exact (ne_of_lt (ofReal_pos.mpr this)).symm
    have sqrt_pi_pos : 0 < √Real.pi ^ d := pow_pos (Real.sqrt_pos_of_pos (Real.pi_pos)) d
    have arg_pos : 0 < (d : ℝ) / 2 + 1 := by
      have : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
      linarith
    exact div_pos sqrt_pi_pos (Real.Gamma_pos_of_pos arg_pos)
  rw [mul_le_mul_right h1 (ofReal_ne_top)]
  exact pow_le_pow_left' (ofReal_le_ofReal h) d

/--
  `Finset` is a finite set of elements.
  The image of a nonempty `Finset` by a function is also nonempty.
-/
lemma image_nonempty {α β : Type*} [DecidableEq β] {f : α → β} {A : Finset α}
    (ha : A.Nonempty) : (A.image f).Nonempty :=
  (Finset.image_nonempty).mpr ha

/-- Definition of the argmax. -/
def argmax {α β : Type*} [LE β] (f : α → β) := {y | ∀ x, f x ≤ f y}
/-- Definition of the argmin. -/
def argmin {α β : Type*} [LE β] (f : α → β) := {y | ∀ x, f y ≤ f x}

/-- Definition of the diameter of a set. -/
noncomputable def diam {α β : Type*} [LE β] [HSub β β β] {f : α → β}
    (neamax : (argmax f).Nonempty) (neamin : (argmin f).Nonempty) :=
  f neamax.some - f neamin.some

/- The search space. -/
variable {X : Set (EuclideanSpace ℝ (Fin d))}

/- To create the instance `MeasureSpace X` -/
attribute [local instance] Measure.Subtype.measureSpace

/-
  We assume that `X` can be approximated by a measurable set, up to a null measure set
  (true for a compact subset of ℝᵈ).
-/
variable (null_measurable : NullMeasurableSet X)

/--
  The substraction operator for the subtype `X`. It uses the operator from the encompassing type.
  -/
noncomputable instance : HSub X X (EuclideanSpace ℝ (Fin d)) where
  hSub := fun x y ↦ x.1 - y.1

/-
  Let `f` the function to be optimized.
  We suppose that is has an argmax and an argmin w.r.t. to its domain
  (true if `X` compact and `f` continuous).
-/
variable (f : X → ℝ) (neamax : (argmax f).Nonempty) (neamin : (argmin f).Nonempty)

/-- Wether the candidate `x` is being rejected. -/
def is_rejected {A : Finset X} (hA : A.Nonempty) (κ : ℝ) (x : X) :=
  (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
    < (A.image f).max' (image_nonempty hA)
/--
  The set containing all points that are rejected, given a nonempty `Finset`
  of potential maximizers
-/
def rejected {A : Finset X} (hA : A.Nonempty) (κ : ℝ) :=
  {x | is_rejected f hA κ x}

/--
  A candidate `x` is rejected iff it belongs to a ball determined
  by the best maximizer found so far and a potential maximizer.
-/
theorem reject_iff_ball {A : Finset X} (hA : A.Nonempty) {κ : ℝ} (hκ : 0 < κ) (x : X) :
    is_rejected f hA κ x
    ↔ ∃ x₁ ∈ A, x ∈ ball x₁ (((A.image f).max' (image_nonempty hA) - f x₁) / κ) := by
  let f' := (A.image f).max' (image_nonempty hA)
  rw [show (A.image f).max' (image_nonempty hA) = f' by rfl]
  let f'' := (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
  unfold is_rejected
  rw [show (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA) = f'' by rfl]
  constructor
  · intro h
    have : ∃ x₁ ∈ A, f x₁ + κ * ‖x - x₁‖ = f'' := mem_image.mp (min'_mem _ (image_nonempty hA))
    rcases this with ⟨x₁, hx₁, hfx₁⟩
    use x₁
    refine ⟨hx₁, ?_⟩
    rw [←hfx₁] at h
    have norm_ineq : ‖x - x₁‖ < (f' - f x₁) / κ :=
      (lt_div_iff' hκ).mpr (lt_tsub_iff_left.mpr h)
    exact norm_ineq
  rintro ⟨x₁, hx₁, h⟩
  have reject : f x₁ + κ * ‖x - x₁‖ < f' :=
    lt_tsub_iff_left.mp ((lt_div_iff' hκ).mp (mem_ball_iff_norm.mp h))
  have min_le : f'' ≤ f x₁ + κ * ‖x - x₁‖ := min'_le _ _ (mem_image_of_mem _ hx₁)
  exact lt_of_le_of_lt min_le reject

/-- The set of rejected candidates is equal to the union indexed by `A` of balls.-/
theorem reject_iff_ball_set {A : Finset X} (hA : A.Nonempty) {κ : ℝ} (hκ : 0 < κ) :
    rejected f hA κ = ⋃ xᵢ ∈ A, ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁ball⟩ := (reject_iff_ball f hA hκ x).mp hx
    exact Set.mem_biUnion hx₁ hx₁ball
  intro hx
  suffices is_rejected f hA κ x by exact this
  rw [reject_iff_ball f hA hκ x]
  simpa using hx

/-- The diameter is bigger than any distance within `A`. -/
lemma diam_le {A : Finset X} (hA : A.Nonempty) :
    ∀ ⦃x⦄, x ∈ A → (A.image f).max' (image_nonempty hA) - f x ≤ diam neamax neamin := by
  intro x _
  have image_le_max : (A.image f).max' (image_nonempty hA) ≤ f (neamax.some) := by
    have : ∃ x₁ ∈ A, f x₁ = (A.image f).max' (image_nonempty hA) := mem_image.mp (max'_mem _ (image_nonempty hA))
    rcases this with ⟨x₁, _, hfx₁⟩
    rw [← hfx₁]
    exact (Nonempty.some_mem neamax) x₁
  exact tsub_le_tsub image_le_max ((Nonempty.some_mem neamin) x)

/-- The uniform measure on `X`. -/
noncomputable def μ : Measure X := (volume X)⁻¹ • volume

/--
  Utility lemma. It shows that the volume restricted on `X` of a ball is less or equal
  than the volume on the entire space of the same ball.
-/
lemma le_coe_volume (r : ℝ) (x : X) : volume (ball x r) ≤ volume (ball x.1 r) := by
  rw [show volume (ball x r) = volume.comap Subtype.val (ball x r) by rfl]
  rw [Measure.comap_apply₀ Subtype.val volume Subtype.val_injective]
  swap; exact fun s a ↦ Measure.MeasurableSet.nullMeasurableSet_subtype_coe null_measurable a
  swap; exact MeasurableSet.nullMeasurableSet measurableSet_ball
  suffices Subtype.val '' (ball x r) ⊆ ball x.1 r by
    exact OuterMeasureClass.measure_mono volume this
  intro y hy
  obtain ⟨x', h1x', h2x'⟩ := (Set.mem_image Subtype.val {y | ‖y.1 - x.1‖ < r} y).mp hy
  rw [mem_setOf_eq] at h1x'
  rwa [h2x'] at h1x'

/-- The measure over the entire space of a ball of radius `diam`. -/
noncomputable def measure_ball_diam (κ : ℝ) :=
  (volume X)⁻¹
  * (ENNReal.ofReal (diam neamax neamin / κ) ^ d
  * ENNReal.ofReal (√Real.pi ^ d / ((d : ℝ) / 2 + 1).Gamma))

/--
  **Main theorem**: the measure of the rejected candidates is less or equal than
  the volume of `|A|` ball of radius `diam`.
-/
theorem measure_reject_le {A : Finset X} (hA : A.Nonempty) {κ : ℝ} (hκ : 0 < κ) :
    μ (rejected f hA κ) ≤ A.card * measure_ball_diam f neamax neamin κ := by
  /- We rewrite the set of rejected candidates as a union of balls. -/
  rw [reject_iff_ball_set f hA hκ]
  /-
    We show that μ ∪(x ∈ A) ball(x, (A.img f).max - f (x))
    ≤ ∑ (x ∈ A) (volume X)⁻¹ * volume (ball((x : ℝᵈ), diam))
  -/
  have μ_le : μ (⋃ xᵢ ∈ A, ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ))
      ≤ ∑ xᵢ ∈ A, (volume X)⁻¹ * volume (ball xᵢ.1 (diam neamax neamin / κ)) := by
    have union_le_sum : μ (⋃ xᵢ ∈ A, ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ))
        ≤ ∑ xᵢ ∈ A, μ (ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ)) :=
      measure_biUnion_finset_le A (fun i =>
          ball i (((Finset.image f A).max' (_root_.image_nonempty hA) - f i) / κ))
    have sum_le_sum : ∑ xᵢ ∈ A, μ (ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ))
      ≤ ∑ xᵢ ∈ A, (volume X)⁻¹ * volume (ball xᵢ.1 (diam neamax neamin / κ)) := by
      have μ_le : ∀ x ∈ A, μ (ball x (((A.image f).max' (image_nonempty hA) - f x) / κ))
          ≤ (volume X)⁻¹ * volume (ball x.1 (diam neamax neamin / κ)) := by
        intro x hx
        have volume_le : volume (ball x (((A.image f).max' (image_nonempty hA) - f x) / κ))
            ≤ volume (ball x.1 (diam neamax neamin / κ)) := by
          have volume_comap_le := le_coe_volume
            null_measurable (((A.image f).max' (image_nonempty hA) - f x) / κ) x
          have volume_ball_le := volume_mono hd x x _ _
            ((div_le_div_right hκ).mpr (diam_le f neamax neamin hA hx))
          exact Preorder.le_trans _ _ _ volume_comap_le volume_ball_le
        unfold μ
        rw [Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul_left' volume_le _
      exact GCongr.sum_le_sum μ_le
    exact Preorder.le_trans _ _ _ union_le_sum sum_le_sum
  /-
    We show that ∑ (x ∈ A) (volume X)⁻¹ * volume (ball(x, diam))
    = A.card * (volume X)⁻¹ * volume_ball_diam
  -/
  have sum_μ : ∑ xᵢ ∈ A, (volume X)⁻¹ * volume (ball xᵢ.1 (diam neamax neamin / κ))
      = A.card * measure_ball_diam f neamax neamin κ := by
    have volume_ball : ∀ x ∈ A, (volume X)⁻¹
      * volume (ball x.1 (diam neamax neamin / κ)) = measure_ball_diam f neamax neamin κ := by
      intro x _
      have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
      rw [EuclideanSpace.volume_ball, Fintype.card_fin]
      rfl
    rw [sum_congr rfl volume_ball, ← nsmul_eq_mul]
    exact sum_const (measure_ball_diam f neamax neamin κ)
  rwa [sum_μ] at μ_le
