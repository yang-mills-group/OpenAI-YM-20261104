import YM.Integration.WilsonCenteredCaptureBridge

/-! Collect the proper hard responses of one compensated centered cell,
at their original addresses and against the complete original cover. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCompulsoryCollection
open Finset Lattice RG Wilson Marker QuadraticLocal Ac Corona Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {P : Rep G n}
variable (D : Lamps X ι G P.p o R) (A : Gallery X μ o P R)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) {α δ κ : ℝ} (width : 0 ≤ α)
    (regular : D.Paid w P.p.B α δ) (hard : A.K.Paid w P.p.B α κ)

def joint (a b : V) (x : X) (U : Config G n) (l : ι) (i : ℕ) : ℂ :=
  (D.frame l x U).part (R.fire a)*(A.K.hard x i U).part (R.fire b) +
    (A.K.hard x i U).part (R.fire a)*(D.frame l x U).part (R.fire b)

include hw width regular hard in
theorem original (a b : V) (x : X) (U : Config G n) :
    (D.log x U).part (R.fire a)*(A.gas x U).part (R.fire b) +
    (A.gas x U).part (R.fire a)*(D.log x U).part (R.fire b) =
      ∑' F : Finset ℕ, if P.activities.admissible P.p U F then
        ∑ i ∈ F, (∑' l, joint D A a b x U l i) *
          ∏ j ∈ F.erase i, (P.activities.K j U : ℂ)
        else 0 := by
  have fd := regular.sums width hw x U
  have part (c : V) : Summable (fun l => (D.frame l x U).part (R.fire c)) :=
    ((Poly.get (R.fire c)).hasSum fd.hasSum).summable
  rw [WilsonCenteredCompulsoryOwners.grouped A w hw width hard a b]
  apply tsum_congr
  intro F
  split_ifs
  · apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun c : ℂ => c*_)
    rw [Lamps.log, Poly.share fd, Poly.share fd, ←tsum_mul_right, ←tsum_mul_left,
      ←Summable.tsum_add ((part a).mul_right _) ((part b).mul_left _)]
    rfl
  · rfl

include hw width regular hard in
theorem collected (a b : V) (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z)
    (x : X) (U : Config G n) :
    SumBudget (fun z : ι × ℕ => w a*w b*‖joint D A a b x U z.1 z.2‖ *
        Real.exp (α * coverNumber P.p.B (D.ground z.1 ∪ Z ∪ (P.activities.forced z.2).support)))
      (2*Real.exp (α * coverNumber P.p.B Z)*(δ*κ)) := by
  let ab := WilsonCenteredCaptureBridge.original D A.K w hw width regular hard a b Z za zb x U
  let ba := WilsonCenteredCaptureBridge.original D A.K w hw width regular hard b a Z zb za x U
  refine budget_loosen (budget_mono (budget_plus ab ba) (fun z => by positivity [hw a,hw b])
    (fun z => ?_)) (by ring_nf; exact le_rfl)
  have h := norm_add_le
    ((D.frame z.1 x U).part (R.fire a)*(A.K.hard x z.2 U).part (R.fire b))
    ((A.K.hard x z.2 U).part (R.fire a)*(D.frame z.1 x U).part (R.fire b))
  simp only [norm_mul] at h
  calc
    _ ≤ (w a*w b*((‖(D.frame z.1 x U).part (R.fire a)‖*
          ‖(A.K.hard x z.2 U).part (R.fire b)‖) +
          ‖(A.K.hard x z.2 U).part (R.fire a)‖*‖(D.frame z.1 x U).part (R.fire b)‖))*_ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (mul_nonneg (hw _).le (hw _).le))
        (Real.exp_pos _).le
    _ = _ := by ring

include hw width regular hard in
theorem divided (a b : V) (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z)
    (x : X) (U : Config G n) (hk : 0 < κ) :
    SumBudget (fun z : ι × ℕ => κ⁻¹ * (w a*w b*‖joint D A a b x U z.1 z.2‖ *
        Real.exp (α * coverNumber P.p.B (D.ground z.1 ∪ Z ∪ (P.activities.forced z.2).support))))
      (2*Real.exp (α * coverNumber P.p.B Z)*δ) := by
  convert budget_scale (inv_pos.mpr hk).le
    (collected D A w hw width regular hard a b Z za zb x U) using 1
  field_simp

end YM.Integration.WilsonCenteredCompulsoryCollection
