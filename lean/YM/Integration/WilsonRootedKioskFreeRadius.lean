import YM.Integration.WilsonRootedKioskSlipCharge

/-! Keep both charged taps and the full older marked shift. Its absent quiet
mode, like the newly filed slips, pays one factor of the free radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskFreeRadius
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected Push.AbsoluteSums QuadraticLocal
open WilsonRootedKioskOccupiedSlip WilsonRootedKioskSlipCharge
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V T I J:Type}[DecidableEq V]{p:BudgetPoint}{o:V → Site n}{R:Census V}
variable {w:V → ℝ}{k a c d s e:ℝ}{B:ℕ}

def occupied (f:Poly R):Poly R:=fun l=>if l=R.quiet then 0 else f.part l

theorem price (f:Poly R)(hw:∀v,0<w v)(hk:1 ≤ k):
    Poly.price (fun i=>w i/k) (occupied f)  ≤  k⁻¹*Poly.price w f:=by
  unfold Poly.price;rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change Poly.toll _ j*‖if j=R.quiet then 0 else f.part j‖  ≤  _
  by_cases zero:j=R.quiet
  · rw [if_pos zero,norm_zero,mul_zero]
    exact mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hk)) (mul_nonneg ((Poly.worth hw _).le) (norm_nonneg _))
  · rw [if_neg zero,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (toll hw hk zero) (norm_nonneg _)

theorem moved (M:Canopy.ShiftRows T J G p o R)(hw:∀v,0<w v)(hk:1 ≤ k)(initial:M.Budget w B a c):
    M.Budget (fun i=>w i/k) B a (k⁻¹*c):=by
  obtain ⟨f,hf,hit⟩:=initial.earned
  refine ⟨fun i=>occupied (f i),?_,fun x=>?_⟩
  · intro i t u j
    by_cases zero:j=R.quiet
    · subst j
      change ‖(M.soap t i u).part R.quiet‖  ≤  (if R.quiet=R.quiet then (0:ℂ) else (f i).part R.quiet).re ∧ _
      rw [M.skip t i u,norm_zero,if_pos rfl];exact ⟨le_rfl,rfl⟩
    · simpa only [occupied,Poly.part,if_neg zero] using hf i t u j
  have ip:0 ≤ k⁻¹:=inv_nonneg.mpr (zero_le_one.trans hk)
  apply budget_mono (WilsonRootedKioskSoft.scale ip hit x)
  · intro i;split
    · exact mul_nonneg (Poly.nonnegative (fun j=>div_pos (hw j) (zero_lt_one.trans_le hk)) _) (Real.exp_pos _).le
    · exact le_rfl
  intro i;split
  · exact mul_le_mul_of_nonneg_right (price (f i) hw hk) (Real.exp_pos _).le
  · exact le_rfl

def radius (r c d s:ℝ):ℝ:=max (max 1 r) ((c+d)/s)

theorem original (M:Canopy.ShiftRows T J G p o R)(L:Lamps T I G p o R)(hw:∀v,0<w v)
    (old:M.Budget w B a c)(fresh:Gross L w B a d)(hs:0<s)(r:ℝ):
    let k:=radius r c d s
    1 ≤ k ∧ r ≤ k ∧ (roll M L).Budget (fun i=>w i/k) B a s:=by
  intro k
  have one:1 ≤ k:=(le_max_left 1 r).trans (le_max_left _ _)
  have margin:(c+d)/s ≤ k:=le_max_right _ _
  have cash:k⁻¹*c+k⁻¹*d ≤ s:=by
    rw [←mul_add,mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ (zero_lt_one.trans_le one)).mpr (by simpa only [mul_comm] using (div_le_iff₀ hs).mp margin)
  obtain ⟨q,hq,charged⟩:=(stack M L (moved M hw one old) (cost L hw one fresh)).earned
  exact ⟨one,(le_max_right 1 r).trans (le_max_left _ _),q,hq,fun x=>budget_loosen (charged x) cash⟩

theorem restore (w:V → ℝ)(k:ℝ)(hk:k≠0)(j:R.Mode):
    k^j.val.card*Poly.toll (fun i=>w i/k) j=Poly.toll w j:=by
  unfold Poly.toll
  rw [prod_div_distrib,Finset.prod_const]
  field_simp

end YM.Integration.WilsonRootedKioskFreeRadius
