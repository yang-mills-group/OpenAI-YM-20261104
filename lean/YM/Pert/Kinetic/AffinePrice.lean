import YM.Pert.Kinetic.Ebb
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} (c : G.Color) (hc : ‖c‖=1) (b : Bool) {i j : Axis} {p : BudgetPoint} {δ : ℝ} {hG : G.Simple} {A : Activities G n}
include hG hc
lemma one_fee {X : Support n} (o : Site n) {f : Pot G n} (hf : p.Regular X f) (ho : o ∈ X) {u : ℝ} (h : p.supBounds o X f u) (hflat : Nonwrapping X o → ∀ x y,IsAffineDirection o x → IsAffineDirection o y → logHessian f x y=0)
    (hn : 4 ≤ n.val) : |logHessian f (wave c b i j) (wave c b i j)| ≤ (Full.mesh n)^3 * geomE p * p.mass X u := by
   have hp:=p.threshold_pos; have he:=p.exponent_pos; have hπ:=Real.pi_pos; have hm:=Full.mesh_pos (n:=n)
   have hpay : 0≤p.mass X u:=h.1.trans (p.loMass _ _ h.1)
   by_cases hX : Nonwrapping X o
   swap
   · have hd := loose_dir (p:=p) o (wave c b i j) zero_lt_one 0 (Nat.zero_le _) (fun e => by simpa only [pow_zero,mul_one] using wave_bound c hc b hn e)
     rw [(show ((1:ℝ)/p.threshold)⁻¹=p.threshold by field_simp)] at hd
     refine (sparse_fee c hc hG hf o _ hn hX ho h hd).trans ?_
     apply mul_le_mul_of_nonneg_right _ hpay
     unfold geomE; have ht : 0≤(2*Real.pi+2)*(3:ℝ)/p.threshold^2:=by positivity
     field_simp
     exact le_add_of_nonneg_left (by positivity)
   let v : LinearJet G:={at0:=(jet c b i j o).at0,slope:=0}; let L:=jet c b i j o-v
   let s:=L.field o; let t:= (wave c b i j)- (jet c b i j o).field o
   have hi : wave c b i j=v.field o + (s+t):= by dsimp only [s,t,L]; rw [LinearJet.field_sub]; abel
   have hs' e : ‖s e‖ ≤ Full.mesh n * (separation e.1 o : ℝ) := by
      dsimp only [s,L]; rw [LinearJet.field_sub]
      rw [(show v.field o=(fun e:Edge (Site n)=> (jet c b i j o).at0 e.2) by ext1; simp only [v,LinearJet.field,Pi.zero_apply,smul_zero,Finset.sum_const_zero,add_zero])]
      exact linear_bound c hc b e o
   have hpow := p.power_ge
   have hS:=loose_dir (p:=p) o s hm 1 (by omega) (fun e=>by simpa only [pow_one] using (hs' e).trans (mul_le_mul_of_nonneg_left (by linarith) hm.le))
   have hT:=loose_dir o t (sq_pos_of_pos hm) 2 hpow (fun e=>by refine (residual_bound c hc b hn e o).trans ?_; have hz:=mul_nonneg (sq_nonneg (Full.mesh n)) (Nat.cast_nonneg (α:=ℝ) (separation e.1 o)); nlinarith only [sq_nonneg (Full.mesh n),hz])
   have h0 (z : Directions G n) : logHessian f (v.field o) z = 0 := by
      apply ((v.hessian_curl₁ hG hf hX hn {at0:=0,slope:=0} (by ext1; rw [LinearJet.positive,LinearJet.curl, LinearJet.positive,LinearJet.curl]) z).trans ?_)
      rw [(show (LinearJet.mk (0:Axis→G.Color) 0).field o=(0:Directions G n) by ext1; simp [LinearJet.field])]; simp [hessian_eq]
   have e := (LinearJet.isAffine o).2 ⟨L,rfl⟩
   have h1 : logHessian f s s=0 := hflat hX s s e e
   let cost:= 3*u/p.threshold^2
   let m:=Full.mesh n
   have hP : |logHessian f t t| ≤ m^4 * cost := by refine (scaled_price hG hf h t t (sq_pos_of_pos hm) (sq_pos_of_pos hm) hT hT).trans_eq (by unfold cost m;ring)
   have hQ : |logHessian f s t| ≤ m^3 * cost := by refine (scaled_price hG hf h s t hm (sq_pos_of_pos hm) hS hT).trans_eq (by unfold cost m;ring)
   have ht : logHessian f (wave c b i j) (wave c b i j)=logHessian f t t+2*logHessian f s t := by
      rw [hi]; rw [hessian_eq]; simp only [map_add,add_apply]; simp_rw [← hessian_eq]
      rw [h1,h0,h0,h0, hessian_symm hf s _,h0,hessian_symm hf t _,h0,hessian_symm hf t s]; ring
   have hY : m ≤ 2*Real.pi := by apply div_le_self (by positivity); exact_mod_cast n.pos -- adjust
   have hup : (2 + m)*cost ≤ (2+2*Real.pi)*(3/p.threshold^2) * p.mass X u := by
      change (2 + m) * (3*u/p.threshold^2) ≤ _
      rw [div_eq_inv_mul (3*u)]
      rw [← mul_assoc (2+m)]
      calc (2 + m) * (p.threshold ^ 2)⁻¹ * (3 * u) ≤ (2 + 2 * Real.pi) * (p.threshold ^ 2)⁻¹ * (3 * u) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by linarith only [h.1])
           _ = (2+2*Real.pi) * (3/p.threshold^2)*u := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (p.loMass X u h.1) (by positivity)
   calc _ ≤ m^3 * ((2 + m)*cost) := by rw [ht]; refine (abs_add_le ..).trans ?_; rw [abs_mul,(abs_of_pos (zero_lt_two (α:=ℝ)))]; nlinarith only [hP, hQ]
        _ ≤ m^3 * (2+2*Real.pi) * (3/p.threshold^2) * p.mass X u := by exact (mul_le_mul_of_nonneg_left hup (by positivity)).trans_eq (by ring)
        _ ≤ m^3 * geomE p * p.mass X u := by 
             apply (mul_le_mul_of_nonneg_right (by
                rw [mul_assoc]
                apply (mul_le_mul_of_nonneg_left _ (by positivity))
                unfold geomE
                suffices hy : (2 + 2 * Real.pi) * 3 ≤ (2 * Real.pi + 2) * 3 + (100 * (4 * ↑p.B + 2) / (2 * Real.pi * p.supportExponent)) ^ 3 * 18 by
                   simpa only [div_eq_mul_inv,one_mul,mul_left_comm,mul_comm,mul_assoc] using (mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr (sq_nonneg p.threshold)))
                rw [add_comm (2:ℝ)]; exact le_add_of_nonneg_right (by positivity)) hpay)
end YM.Pert.Kinetic
