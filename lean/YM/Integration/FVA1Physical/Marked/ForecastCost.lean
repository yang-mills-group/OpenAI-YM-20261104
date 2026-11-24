import YM.Integration.FVA1Physical.Marked.ShortWallet
import YM.Integration.FVA1Physical.Marked.ColorSummable

/-! Absolute field-independent price of every marked coefficient of the
purchased smooth forecast. The nilpotent exponential uses its actual finite
order, so it only incurs a polynomial price in the untruncated physical fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Extra.Trajectories LocalComparison RG3.Script.Picnic Push.AbsoluteSums Overlay RG3.Forms
open Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset Rooms Comparison.RG02.Order
open scoped BigOperators Classical
variable {G : Gauge} {I Z : Type} [Fintype I] [DecidableEq I] {B : Census I} {n : Side}
  {P : Rep G n} {o : I→Site n} {T : Taste Z o P B} {w : I→ℝ} {κ a b : ℝ}

theorem finite_pass_price (hw : ∀ i,0<w i) (p : Poly B) {M : ℝ} (hm : Poly.price w p≤M) :
    Poly.price w p.pass ≤ repeats (Fintype.card I+1) M := by
  apply (Poly.batch hw ..).trans
  apply Finset.sum_le_sum
  intro k _
  rw [Poly.adapted]
  have hc : ‖((k.factorial:ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1≤k.factorial from Nat.factorial_pos k))
  exact (mul_le_of_le_one_left (Poly.nonnegative hw _) hc).trans
    ((Poly.powers hw _ k).trans (pow_le_pow_left₀ (Poly.nonnegative hw _) hm _))

theorem log_value_price (W : FullBudget P.p T w κ a b) (t : Z) (V : Config G n) :
    Poly.price w ((T.leaf t).log V) ≤ (Fintype.card I:ℝ)*a*3 := by
  let A := T.leaf t
  let z (i : ℕ) := Poly.toll w (T.menu.rays i)*P.p.mass (T.menu.branch i) (W.white i)
  let c (i : ℕ) := Poly.toll w (T.tag i)*P.p.mass (T.site i) (W.gold i)
  have zn i : 0≤z i := mul_nonneg (Poly.worth W.radii _).le ((W.white_nonnegative i).trans (P.p.loMass _ _ (W.white_nonnegative i)))
  have cn i : 0≤c i := mul_nonneg (Poly.worth W.radii _).le ((W.gold_nonnegative i).trans (P.p.loMass _ _ (W.gold_nonnegative i)))
  choose regular caption rb cb bill using W.regularTotal
  have un j : 0≤w j*W.unitBound j := mul_nonneg (W.radii _).le (W.unit_nonnegative _)
  have budZ := Overlay.per_system (P:=T.menu.rays) (c:=a) zn (W.active t).articles.proper
    (fun j=>budget_loosen (rb j) (by linarith only [bill j,un j,budget_nonneg (cb j)]))
  have budC := Overlay.per_system (P:=T.tag) (c:=a) cn (W.active t).captions.card
    (fun j=>budget_loosen (cb j) (by linarith only [bill j,un j,budget_nonneg (rb j)]))
  have u (j : I) : w j*‖T.menu.global t j‖≤a := (mul_le_mul_of_nonneg_left (W.unit t j) (W.radii _).le).trans
    (by linarith only [bill j,budget_nonneg (rb j),budget_nonneg (cb j)])
  have z0 i : Poly.price w (A.contents.ray i V)≤z i := by
    rw [Bands.ray,Poly.solo]
    apply mul_le_mul_of_nonneg_left _ (Poly.worth W.radii _).le
    apply le_trans _ (P.p.loMass _ _ (W.white_nonnegative i))
    obtain ⟨j,hj⟩ := (W.active t).articles.proper i
    by_cases hy : Healthy P.p.threshold (T.menu.branch i) V
    · change ‖masked P.p.threshold (T.menu.branch i) (T.menu.regular t i) V‖ ≤ _
      rw [masked_eq _ _ _ _ hy]
      exact grain_value ((W.regular i).controls t j hj) hy
    change ‖masked P.p.threshold (T.menu.branch i) (T.menu.regular t i) V‖ ≤ _
    rw [masked_ne _ _ _ _ hy,norm_zero]
    exact W.white_nonnegative i
  have c0 i : Poly.price w (Poly.send (T.tag i) (T.score t i))≤c i := by
    rw [Poly.solo]
    exact mul_le_mul_of_nonneg_left ((W.caption t i).trans (P.p.loMass _ _ (W.gold_nonnegative i))) (Poly.worth W.radii _).le
  have gu : Poly.price w (∑ j : I,Poly.send (B.fire j) (T.menu.global t j)) ≤ (Fintype.card I:ℝ)*a := by
    apply (Poly.batch W.radii ..).trans
    simp_rw [Poly.solo,Poly.solo_toll]
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s:=Finset.univ) (fun j _=>u j)
  have gz := ((Poly.budgeted W.radii budZ.2.1 z0).2).trans budZ.2.2
  have gc := ((Poly.budgeted W.radii budC.2.1 c0).2).trans budC.2.2
  apply (Poly.addition W.radii ..).trans
  apply (add_le_add ((Poly.addition W.radii ..).trans (add_le_add gu gz)) gc).trans_eq
  ring

variable {D h : ℕ} {ξ : I→ℕ} {wallet : Rooms.Wallet Z o P B ξ D h}

omit [Fintype I] in
/-- The scalar is chosen before the test and field. The only scale/geometry
input in this retained part is the admitted change of tag rents. -/
theorem render_value_price (hw : ∀ i,0<w i) {ray : Parabola.Ray B} {address : I→Support n} {width β allowance : ℝ}
    (shell : wallet.Usable address ray width β allowance) (pos : 0<width)
    {L : ℝ} (rent : ∀ s : Senses B,Poly.toll w s.val ≤ L*ray s.val) (hL : 0≤L)
    (t : Z) (cut : ℕ) (g : ℝ) (V : Config G n) :
    Poly.price w (wallet.render cut g t V) ≤ L*∑ s : Senses B,valueInvoice G ξ D h s g := by
  apply (Poly.batch hw ..).trans
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _=>?_
  rw [Poly.solo]
  let A := Stanza.son (wallet.prediction t) h
  let zone := Tale.court P.p.B (o (Sonnet.root s))
  let val := valueInvoice G ξ D h s g
  let read := A.wake s (A.short (wallet.activation t) cut) o g
  have vn : 0≤val := Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>mul_nonneg (abs_nonneg _) (Vase.ticketC_pos ..)
  have msk : |masked P.p.threshold zone read V|≤val := by
    by_cases hy:Healthy P.p.threshold zone V
    · rw [masked_eq _ _ _ _ hy]; exact wake_bound A s _ (shell.optics t) pos g V
    rw [masked_ne _ _ _ _ hy,abs_zero]; exact vn
  have rate : Poly.toll w s.val*|wallet.weight t s|≤L := by
    calc
      _ ≤ (L*ray s.val)*|wallet.weight t s| := mul_le_mul_of_nonneg_right (rent s) (abs_nonneg _)
      _ = L*(ray s.val*|wallet.weight t s|) := mul_assoc ..
      _ ≤ L*1 := mul_le_mul_of_nonneg_left (shell.starts t s) hL
      _ = L := mul_one _
  change Poly.toll w s.val * ‖((wallet.weight t s * masked P.p.threshold zone read V : ℝ):ℂ)‖ ≤ L*val
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,←mul_assoc]
  exact mul_le_mul rate msk (abs_nonneg _) hL

end YM.Integration.FVA1Physical.Marked
