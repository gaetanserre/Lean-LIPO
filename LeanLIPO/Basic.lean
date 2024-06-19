import Mathlib

open Metric Pointwise Finset MeasureTheory ENNReal Set

variable {d : ℕ} (hd : 0 < d) [Nonempty (Fin d)]

lemma image_nonempty {f : EuclideanSpace ℝ (Fin d) → ℝ} {A : Finset (EuclideanSpace ℝ (Fin d))}
    (ha : A.Nonempty) : (A.image f).Nonempty :=
  (Finset.image_nonempty).mpr ha

def argmax {α β : Type*} [LE β] (f : α → β) := {y | ∀ x, f x ≤ f y}
def argmin {α β : Type*} [LE β] (f : α → β) := {y | ∀ x, f y ≤ f x}
noncomputable def diame {α β : Type*} [LE β] [HSub β β β] {f : α → β}
    (nemax : (argmax f).Nonempty) (nemin : (argmin f).Nonempty) :=
  f nemax.some - f nemin.some

variable (f : EuclideanSpace ℝ (Fin d) → ℝ)
(nemax : (argmax f).Nonempty) (nemin : (argmin f).Nonempty)

lemma unique_argmax : ∀ x y, x ∈ argmax f → y ∈ argmax f → f x = f y := by
  intro x y hx hy
  specialize hy x
  specialize hx y
  linarith

lemma unique_argmin : ∀ x y, x ∈ argmin f → y ∈ argmin f → f x = f y := by
  intro x y hx hy
  specialize hy x
  specialize hx y
  linarith

theorem reject_iff_ball {A : Finset (EuclideanSpace ℝ (Fin d))}
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

/- theorem reject_iff_ball_set {A : Finset (EuclideanSpace ℝ (Fin d))}
    (hA : A.Nonempty) {κ : ℝ} (hκ : 0 < κ) :
    {x | (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
      < (A.image f).max' (image_nonempty hA)}
    = {x | ∃ x₁ ∈ A, x ∈ ball x₁ (((A.image f).max' (image_nonempty hA) - f x₁) / κ)} := by
  ext x
  exact reject_iff_ball f hA hκ x -/

theorem reject_iff_ball_set {A : Finset (EuclideanSpace ℝ (Fin d))}
    (hA : A.Nonempty) {κ : ℝ} (hκ : 0 < κ) :
    {x | (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
      < (A.image f).max' (image_nonempty hA)}
    = ⋃ xᵢ ∈ A, ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁ball⟩ := (reject_iff_ball f hA hκ x).mp hx
    exact Set.mem_biUnion hx₁ hx₁ball
  intro hx
  suffices (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
    < (A.image f).max' (image_nonempty hA) by exact this
  rw [reject_iff_ball f hA hκ x]
  simpa using hx

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

lemma diam_le {A : Finset (EuclideanSpace ℝ (Fin d))} (hA : A.Nonempty) :
    ∀ x ∈ A, (A.image f).max' (image_nonempty hA) - f x ≤ diame nemax nemin := by
  intro x _
  have image_le_max : (A.image f).max' (image_nonempty hA) ≤ f (nemax.some) := by
    have : ∃ x₁ ∈ A, f x₁ = (A.image f).max' (image_nonempty hA) := mem_image.mp (max'_mem _ (image_nonempty hA))
    rcases this with ⟨x₁, _, hfx₁⟩
    rw [← hfx₁]
    exact (Nonempty.some_mem nemax) x₁
  exact tsub_le_tsub image_le_max ((Nonempty.some_mem nemin) x)

noncomputable def μ : Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume (univ : Set (EuclideanSpace ℝ (Fin d))))⁻¹ • volume

noncomputable def volume_ball_diam :=
    ENNReal.ofReal (diame nemax nemin) ^ d
    * ENNReal.ofReal (√Real.pi ^ d / ((d : ℝ) / 2 + 1).Gamma)

example {A : Finset (EuclideanSpace ℝ (Fin d))}
    (hA : A.Nonempty) (κ : ℝ) (hκ : 0 < κ) :
    μ {x | (A.image (fun y ↦ f y + κ * ‖x - y‖)).min' (image_nonempty hA)
      < (A.image f).max' (image_nonempty hA)}
    ≤ A.card * volume_ball_diam f nemax nemin := by
  rw [reject_iff_ball_set f hA hκ]

  have : μ (⋃ xᵢ ∈ A, ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ))
      ≤ ∑ xᵢ ∈ A, μ (ball xᵢ (((A.image f).max' (image_nonempty hA) - f xᵢ) / κ)) :=
    measure_biUnion_finset_le A
      (fun i ↦ ball i (((Finset.image f A).max' (image_nonempty hA) - f i) / κ))

  sorry
