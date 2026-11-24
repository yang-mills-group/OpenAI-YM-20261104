import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskRegion
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite
import YM.Comparison.Density.Render.Goods

/-! The support of each masked atom is charged to its own lifted walks.
The rank-two correction also carries its four original clover leaves. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Wilson Finset
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {h : ℕ}

private theorem visits_size (x : Cover) (w : Walk) : (visits x w).length=w.length+1 := by
  induction w generalizing x <;>simp [visits, *]

theorem slot_size (v : Slot) : v.stencil.card≤v.length+2 := by
  apply (Finset.card_union_le _ _).trans
  have walk := List.toFinset_card_le (visits (0:Cover) v.walk)
  have face := List.toFinset_card_le (visits v.offset (square v.plaq.val.1 v.plaq.val.2))
  rw [visits_size] at walk face
  exact (Nat.add_le_add walk face).trans (by dsimp [Slot.length,square];omega)

theorem footprint_size (a : Atom G h) (x : Site n) :
    (a.footprint x).card ≤ 1+a.length+2*h := by
  apply card_image_le.trans
  apply (Finset.card_insert_le ..).trans
  apply (Nat.add_le_add_right Finset.card_biUnion_le 1).trans
  have card : (∑ j,(a.leg j).stencil.card) ≤ ∑ j,((a.leg j).length+2) :=
    sum_le_sum fun j _=>slot_size (a.leg j)
  apply (Nat.add_le_add_right card 1).trans_eq
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Atom.length]
  change (∑ j,(a.leg j).length)+h*2+1=1+(∑ j,(a.leg j).length)+2*h
  ring

theorem masked_atom_salary (a : Atom G h) (x : Site n) (X : Support n) {extra : ℕ}
    (scope : X.card≤(a.footprint x).card+extra) {σ : ℝ} (hs : 0<σ) :
    a.magnitude*2^h*X.card ≤ a.budget σ*(2^h*(1+2*h+extra+σ⁻¹)) := by
  have supp : (X.card:ℝ)≤1+a.length+2*h+extra := by
    exact_mod_cast scope.trans (Nat.add_le_add_right (footprint_size a x) extra)
  have ep : 1≤Real.exp (σ*a.length) := Real.one_le_exp (mul_nonneg hs.le (Nat.cast_nonneg _))
  have z : σ*(a.length:ℝ)≤Real.exp (σ*a.length) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have length : (a.length:ℝ) ≤ Real.exp (σ*a.length)*σ⁻¹ := by
    rw [←div_eq_mul_inv,le_div_iff₀ hs]
    simpa only [mul_comm] using z
  have positive : 0≤1+2*(h:ℝ)+extra := by positivity
  have cover : (X.card:ℝ) ≤ Real.exp (σ*a.length)*(1+2*h+extra+σ⁻¹) := by
    apply supp.trans
    rw [mul_add]
    linarith [mul_le_mul_of_nonneg_right ep positive]
  have base : 0≤a.magnitude*2^h := mul_nonneg (sum_nonneg fun _ _=>abs_nonneg _) (by positivity)
  exact (mul_le_mul_of_nonneg_left cover base).trans_eq (by unfold Atom.budget;ring)

end YM.Integration.OriginalMarkedRunAction
