import Mathlib

open Metric Pointwise Finset MeasureTheory ENNReal

variable {d : ℕ} (hd : 0 < d) [Nonempty (Fin d)]

lemma image_nonempty {f : EuclideanSpace ℝ (Fin d) → ℝ} {A : Finset (EuclideanSpace ℝ (Fin d))}
    (ha : A.Nonempty) : (A.image f).Nonempty :=
  (Finset.image_nonempty).mpr ha

theorem reject_iff_ball (f : EuclideanSpace ℝ (Fin d) → ℝ) {A : Finset (EuclideanSpace ℝ (Fin d))}
    (hA : A.Nonempty) {κ : ℝ} (hκ : 0 < κ) (x : EuclideanSpace ℝ (Fin d)) :
    (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
      < (A.image f).max' (image_nonempty hA)
    ↔ ∃ x₁ ∈ A, x ∈ ball x₁ (((A.image f).max' (image_nonempty hA) - f x₁) / κ) := by
  let f' := (A.image f).max' (image_nonempty hA)
  rw [show (A.image f).max' (image_nonempty hA) = f' by rfl]
  let f'' := (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
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
    exact mem_ball_iff_norm.mpr norm_ineq
  rintro ⟨x₁, hx₁, h⟩
  have reject : f x₁ + κ * ‖x - x₁‖ < f' :=
    lt_tsub_iff_left.mp ((lt_div_iff' hκ).mp (mem_ball_iff_norm.mp h))
  have min_le : f'' ≤ f x₁ + κ * ‖x - x₁‖ := min'_le _ _ (mem_image_of_mem _ hx₁)
  exact lt_of_le_of_lt min_le reject

theorem reject_iff_ball_set (f : EuclideanSpace ℝ (Fin d) → ℝ) (A : Finset (EuclideanSpace ℝ (Fin d))) (hA : A.Nonempty) (κ : ℝ) (hκ : 0 < κ) :
    {x | (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
      < (A.image f).max' (image_nonempty hA)}
    = {x | ∃ x₁ ∈ A, x ∈ ball x₁ (((A.image f).max' (image_nonempty hA) - f x₁) / κ)} := by
  ext x
  exact reject_iff_ball f hA hκ x

lemma volume_mono (x₁ x₂ : EuclideanSpace ℝ (Fin d))
    (r₁ r₂ : ℝ) (h : r₁ ≤ r₂) : volume (ball x₁ r₁) ≤ volume (ball x₂ r₂) := by
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

def argmax {α β : Type*} [LE β] (f : α → β) := {y | ∀ x, f x ≤ f y }
def argmin {α β : Type*} [LE β] (f : α → β) := {y | ∀ x, f y ≤ f x }

example (f : EuclideanSpace ℝ (Fin d) → ℝ)
    {A : Finset (EuclideanSpace ℝ (Fin d))} (hA : A.Nonempty) :
    ∀ x ∈ A, ∀ x' ∈ argmax f, ∀ x'' ∈ argmin f,
    (A.image f).max' (image_nonempty hA) - f x
    ≤ f x' - f x'' := by
  intro x _ x' hx' x'' hx''
  have image_le_max : (A.image f).max' (image_nonempty hA) ≤ f x' := by
    have : ∃ x₁ ∈ A, f x₁ = (A.image f).max' (image_nonempty hA) := mem_image.mp (max'_mem _ (image_nonempty hA))
    rcases this with ⟨x₁, _, hfx₁⟩
    rw [← hfx₁]
    exact hx' x₁
  exact tsub_le_tsub image_le_max (hx'' x)

#minimize_imports
