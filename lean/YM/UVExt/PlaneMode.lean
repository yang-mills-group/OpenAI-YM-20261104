import YM.UVExt.StencilInvoice

/-! Pair of standing waves, dimensionless cost ~1/n. The longitudinal plaquette is not sampled at a lifted negative representative (alias issues); factors are exact folded phases. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Wilson Lattice Precision Exterior Matrix Bid Bloch Laurent RG
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} (k : Site n)

lemma d_color_plaq (v : Dir G n) (x : Site n) (p : PlaqAxes) :
 dColor G n 1 v (x,plaquette p)= (v (x+step p.val.1, coord p.val.2)-v (x,coord p.val.2)) - (v (x+step p.val.2, coord p.val.1)-v (x,coord p.val.1)) := by
   ext i; simp only [PiLp.sub_apply]; change (d 1 n *ᵥ parts G 1 v i) (x,plaquette p)=_; exact d_plaquettes x p (parts G 1 v i)
lemma panel_norm (x : Site n) : ‖cell k x‖ = 1 := by
    unfold cell mode; rw [Complex.norm_exp,show ((Complex.I*(∑ i : Axis, (mon k) i * (Lattice.lift x i : ℤ): ℂ))).re =0 from ?_] -- syntax
    · exact Real.exp_zero
    have he i : ((mon k i) * (Lattice.lift x i : ℤ):ℂ).im=0 := by unfold mon reciprocal; simp [Complex.mul_im]
    rw [Complex.mul_re] -- cleanup
    simp_rw [Complex.I_re,Complex.I_im,Complex.im_sum,he]; simp

def turn (i : Axis) := cell k (step i)-1

def station (k : Site n) (i : Axis) (z : ℂ) (a : G.Color) : Dir G n := fun p =>
    if p.2=coord i then (cell k p.1 * z).re • a else 0
def broadcast (b : Axis) (a : G.Color) (z : ℂ) := fun t i=> if t=coord b then (a i:ℂ)*z else 0
lemma station_eq (i : Axis) (a : G.Color) (z : ℂ) : wave k (broadcast i a z) = station k i z a := by
   ext x b; unfold wave broadcast station; split_ifs
   · change (cell k x.1 * ((a b : ℂ) * z)).re= (cell k x.1*z).re * (a b); rw [mul_comm (a b:ℂ),←mul_assoc]; rw [Complex.mul_re]; simp
   simp

lemma shift_station (i b : Axis) (a : G.Color) (z : ℂ) :
    shifted (step i) (station k b z a)-station k b z a = station k b ((turn k i)*z) a := by
   funext t; simp only [Pi.sub_apply,shifted,station]
   split_ifs
   · simp only [cell_add,← sub_smul,turn]; exact congr_arg (· • a) (show _ from by rw [← Complex.sub_re]; congr 1; ring)
   simp


lemma station_seed (i : Axis) (a : G.Color) (z) : ‖station k i z a‖ ≤ ‖a‖*‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun t=> ?_; unfold station; split_ifs
  · rw [norm_smul]; exact (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul,panel_norm,one_mul])) (norm_nonneg _)).trans_eq (mul_comm ..)
  simp only [norm_zero]; positivity
lemma d_station (v : Dir G n) (x : Site n) (t : PlaqAxes) : dColor G n 1 v (x,plaquette t) =
   (shifted (step t.val.1) v - v) (x,coord t.val.2) - (shifted (step t.val.2) v - v) (x,coord t.val.1) := by
 rw [d_color_plaq]
 simp only [shifted,Pi.sub_apply,add_comm x]
lemma d_plane (z : ℂ) (i : Axis) (a : G.Color) {ε : ℝ} (h : ∀ i, ‖turn k i‖ ≤ ε) :
    ‖dColor G n 1 (station k i z a)‖ ≤ 4*ε* (‖a‖*‖z‖) := by
   have he : 0≤ε := (norm_nonneg _).trans (h 0); apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
   rintro ⟨x,t⟩
   have hp (a' : Axis) (j : TypeFace 1) : ‖(shifted (step a') (station k i z a)-station k i z a) (x,j)‖ ≤ ‖a‖ * (ε * ‖z‖) := by
     rw [shift_station]
     refine (norm_le_pi_norm _ _).trans ((station_seed k i a _).trans ?_)
     rw [norm_mul]; gcongr; exact h _
   rw [show t=plaquette (plaqEquiv.symm t) from (plaqEquiv.apply_symm_apply t).symm] -- rewrite tactic test; want identify t=... 
   rw [d_station]
   exact (norm_sub_le ..).trans ((add_le_add (hp _ _) (hp _ _)).trans (by linarith [mul_nonneg he (mul_nonneg (norm_nonneg a) (norm_nonneg z))]))
lemma d_delta (v : Dir G n) i : (deltaV i v) = shifted (step i) (dColor G n 1 v) - dColor G n 1 v := by ext1 x; exact (delta_entry ..).trans (by simp only [shifted,Pi.sub_apply,add_comm])
lemma grad_plane (z : ℂ) (i : Axis) (a : G.Color) {ε : ℝ} (h : ∀ i, ‖turn k i‖ ≤ ε) : gradD (station k i z a) ≤ 4*ε^2 * (‖a‖ * ‖z‖) := by
    have he := (norm_nonneg _).trans (h 0)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j=>?_ ; rw [d_delta,←shift_d, ←d_minus, shift_station]
    apply (d_plane k _ i a h).trans
    calc
       _ = 4 * ‖a‖ * ‖z‖ * ε * ‖turn k j‖ := by rw [norm_mul]; ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left (h j) (by positivity:_≤4* ‖a‖ * ‖z‖ * ε)).trans_eq (by ring)

def ripple {n : Side} := (4:ℝ) * Real.pi / n.val
lemma ripple_pos (n : Side) : 0 < ripple (n:=n) := div_pos (by positivity) (by exact_mod_cast n.property)
lemma mon_one {n : Side} (h : 4≤n.val) (i) : cell (step 0:Site n) (step i) = if i=0 then Complex.exp (Complex.I*((2*Real.pi/n.val:ℝ):ℝ)) else 1 := by
   have hh : Lattice.lift (step (S:=Per n) 0)=step 0 := lift_eq_iff.mpr ⟨(wrap_step ..).symm, fun i => by simp [step_apply]; by_cases hi:i=0 <;> simp [hi] <;> omega⟩ -- if type
   rw [cell_step]; unfold mon reciprocal
   rw [hh, Pi.smul_apply,step_apply]; split_ifs
   · simp only [Int.cast_one, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast, mul_one, ←div_eq_inv_mul]
   simp
lemma ripple_cap (n : Side) (h : 4≤n.val) : ∀ i,‖turn (step 0:Site n) i‖ ≤ ripple (n:=n) := by
 intro i; unfold turn; rw [mon_one h]; split_ifs
 · apply Real.norm_exp_I_mul_ofReal_sub_one_le.trans; rw [Real.norm_of_nonneg (by positivity)]; unfold ripple; exact (div_le_div_of_nonneg_right (by linarith [Real.pi_pos]) (Nat.cast_nonneg _)) -- need positive 2π/n explicitly
 rw [sub_self,norm_zero]; exact (ripple_pos ..).le
lemma ripple_lower (n : Side) (h : 4 ≤ n.val) : (n.val:ℝ)⁻¹ ≤ ‖turn (step 0 : Site n) 0‖ := by
  let x := 2*Real.pi/n.val
  have hp : x≤Real.pi/2 := by unfold x; rw [div_le_div_iff₀ (by positivity [show 0< n.val from n.property]) (by norm_num)] ; have hg := mul_le_mul_of_nonneg_left (show (4:ℝ)≤n.val by exact_mod_cast h) Real.pi_pos.le; linarith
  have hx : 0≤x := by unfold x; positivity
  refine le_trans ?_ (show |(turn (step 0 : Site n) 0).im| ≤ _ from Complex.abs_im_le_norm _)
  rw [turn,mon_one h,if_pos rfl,Complex.sub_im,Complex.exp_im]; simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.one_im, mul_zero, mul_one, zero_mul,one_mul,zero_add,sub_zero, Real.exp_zero]
  change _ ≤ |Real.sin x|
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx (hp.trans (half_le_self Real.pi_pos.le)))]
  exact le_trans (by unfold x; have hn : (0:ℝ)<n.val := Nat.cast_pos.mpr n.property; field_simp [hn.ne',Real.pi_ne_zero] <;> try linarith [Real.pi_pos]) (Real.mul_le_sin hx hp)
end YM.UVExt.Paths
