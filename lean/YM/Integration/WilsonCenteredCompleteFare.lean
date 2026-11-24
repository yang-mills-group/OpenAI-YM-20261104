import YM.Integration.WilsonCenteredCompleteGallery

/-! The whole original capture uses a single forced divisor. Its estimate
depends on the number of occupied marks, with no factor in the ambient census. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCompleteFare
open Finset RG Wilson Lattice Marker Push.Local
open WilsonCenteredMaskPieces WilsonCenteredCompleteGallery
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] {R : Census V}

theorem forced (p : BudgetPoint) {t : R.Mode} (w : V→ℝ) (hw : ∀i,0<w i)
    {κ v b B W : ℝ} (div : 0<κ) (small : κ≤1) (room : hitWidth p*v≤1)
    (positive : 0≤b) (cab : b≤B) (cost : (Poly.toll w t)⁻¹≤W) {r : ℕ} (load : t.val.card ≤ r) :
    (WilsonCenteredMixedSetFiling.price b w t κ+(hitWidth p*v)*WilsonCenteredMixedSetFiling.price b w t κ)/κ
      ≤2*(B*W)*r*Real.exp r :=by
  let T:ℝ:=t.val.card
  have T0 : 0≤T := Nat.cast_nonneg _
  have capped : T≤r :=Nat.cast_le.mpr load
  have δ0 : 0≤Real.exp (T*κ)-1 :=sub_nonneg.mpr (Real.one_le_exp (mul_nonneg T0 div.le))
  have slot0 :=(inv_pos.mpr (Poly.worth hw t)).le
  have pos : 0≤WilsonCenteredMixedSetFiling.price b w t κ :=mul_nonneg positive (mul_nonneg slot0 δ0)
  have rare := WilsonCenteredOccupiedHardSets.divided T0 div.le small
  have event : Real.exp (T*κ)-1≤((r:ℝ)*κ)*Real.exp r :=
    rare.trans (mul_le_mul (mul_le_mul_of_nonneg_right capped div.le) (Real.exp_le_exp.mpr capped) (Real.exp_pos _).le
      (mul_nonneg (Nat.cast_nonneg _) div.le))
  have numerator : WilsonCenteredMixedSetFiling.price b w t κ ≤ (B*W)*(((r:ℝ)*κ)*Real.exp r) :=by
    unfold WilsonCenteredMixedSetFiling.price
    rw [←mul_assoc]
    exact mul_le_mul (mul_le_mul cab cost slot0 (positive.trans cab)) event δ0
      (mul_nonneg (positive.trans cab) (slot0.trans cost))
  apply (div_le_iff₀ div).mpr
  calc
    _ ≤ 2*WilsonCenteredMixedSetFiling.price b w t κ :=by linarith [mul_le_of_le_one_left pos room]
    _ ≤ 2*((B*W)*(((r:ℝ)*κ)*Real.exp r)) := by linarith
    _ = _ :=by ring

theorem original (p : BudgetPoint) (s : R.Mode) (w : V→ℝ) (hw : ∀i,0<w i)
    (rows : R.Mode→ℝ) {r : ℕ} (load : s.val.card ≤ r) {D B W bare κ v : ℝ}
    (div : 0<κ) (small : κ≤1) (room : hitWidth p*v≤1) (D0 : 0≤D) (B0 : 0≤B) (W0 : 0≤W)
    (pure : bare≤D) (soft : ∀t:R.Mode,t.val⊆s.val→0≤rows t∧rows t≤B)
    (source : ∀t:R.Mode,t.val⊆s.val→(Poly.toll w t)⁻¹≤W) :
    invoice p s w v κ bare rows≤(2:ℝ)^r*(D+2*(B*W)*r*Real.exp r) :=by
  let h:ℝ:=2*(B*W)*r*Real.exp r
  have h0 : 0≤h :=by positivity
  have item (z) (mem : z∈splits s) : (if z.2=R.quiet then bare else
      (WilsonCenteredMixedSetFiling.price (rows z.1) w z.2 κ+(hitWidth p*v)*WilsonCenteredMixedSetFiling.price (rows z.1) w z.2 κ)/κ)≤D+h :=by
    by_cases vacant : z.2=R.quiet
    · rw [if_pos vacant]
      exact pure.trans (le_add_of_nonneg_right h0)
    rw [if_neg vacant]
    have both:=valid mem
    have fine : z.1.val⊆s.val :=both.2 ▸ subset_union_left
    have hard : z.2.val⊆s.val :=both.2 ▸ subset_union_right
    exact (forced p w hw div small room (soft _ fine).1 (soft _ fine).2 (source _ hard)
      ((card_le_card hard).trans load)).trans (le_add_of_nonneg_left D0)
  unfold invoice
  apply (sum_le_sum item).trans
  rw [sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (add_nonneg D0 h0)
  exact_mod_cast (size s).trans (Nat.pow_le_pow_right (by decide : 0<2) load)

end YM.Integration.WilsonCenteredCompleteFare
