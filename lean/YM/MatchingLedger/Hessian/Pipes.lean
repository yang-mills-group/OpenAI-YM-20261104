import YM.MatchingLedger.Hessian.Cells

/-!
# Projector of kinetic calibration with a polylog transparent window

`wallCut`: truncate the HESSIAN, not the theory. Far support must still be paid in the theory.
Use pairing with **difference wave − zero harmonic** to reduce inverse frequency cost. Remark:
there is no requirement of an exact zero holonomy Hessian on all torus sizes! It has its own
budget; something local at the seam of a specific chart may not be affine. No Ward premise.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Spring
open Function Filter Finset Lattice Wilson RG Pert Pert.Kinetic
open scoped Topology BigOperators Classical ContDiff Finset
variable {n : Side} {G:Gauge}
variable (hn:4 ≤ n.val)
local notation "m" => Full.mesh n

def amp (b : Bool) : Floor n:= mode 1 b -- cost uses long wave, compare via mode_add

def dump (x y:Site n) : ℝ := ∑ b:Bool, amp b x*amp b y
lemma dump_eq : dump (n:=n)=∑ b:Bool, spur (amp b) (amp b):= by funext x y; simp only [Finset.sum_apply,dump,spur]
lemma amp_one : spur (1:Floor n) 1=1:= by funext i j; exact mul_one (1:ℝ)

def swing (x y:Site n) := dump x y-1
lemma swing_form : swing (n:=n)=dump - 1:= rfl

def eigen (n:Side):= (4*Real.sin (Full.mesh n/2)^2)
include hn
lemma amp_car (x:Site n) : dump x x=1:=by
  unfold dump amp; rw [Fintype.sum_bool]; simp only [mode_base _ hn,trig,Bool.false_eq_true,↓reduceIte]; simp only [← pow_two]; rw [Real.sin_sq_add_cos_sq]
lemma delta_amp (x y:Site n)(b:Bool) : ‖amp b x-amp b y‖ ≤ Full.mesh n*separation x y := by
  let h:= (separation x y:ℝ); unfold amp
  nth_rw 1 [←show wrap n (lift (x-y))+y=x from by rw [wrap_lift]; abel] -- want LHS only!
  rw [mode_add b hn,mode_base b hn]
  apply (trig_lip ..).trans
  rw [add_sub_cancel_left]; convert! delta_le (j:=1) y x using 1
lemma swing_bound (x y:Site n) : ‖swing x y‖ ≤ Full.mesh n^2*(separation x y:ℝ)^2:=by
  let k:= Full.mesh n* (separation x y:ℝ); let zigPay (b:Bool):= amp b x-amp b y
  have he : -2*swing x y = zigPay true^2+ zigPay false^2:=by
    have hx:= amp_car hn x; have hy:= amp_car hn y; unfold zigPay swing dump at *; rw [Fintype.sum_bool] at hx hy ⊢; nlinarith only [hx,hy]
  have hh(b:Bool): zigPay b^2 ≤ k^2:= by rw [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (delta_amp hn x y b) _
  apply abs_le.mpr; rw [←mul_pow]; exact ⟨by linarith only [hh true,hh false,he], by nlinarith only [he, sq_nonneg k, sq_nonneg (zigPay true),sq_nonneg (zigPay false)]⟩ -- k
lemma eigen_pos : 0 < eigen n:= by
  have hf:= Full.mesh_pos (n:=n); have he := (elliptic_prize hn).2; have hp:=Real.pi_pos
  change m^2 * 2≤ Real.pi^2*((1/2)*eigen n) at he
  by_contra! hz; linarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg Real.pi) hz,he,sq_pos_of_pos hf]
lemma eigen_price : m^2 ≤ (Real.pi^2/4)*eigen n := by have hx:= (elliptic_prize hn).2; unfold eigen; linarith only [hx]

omit hn
lemma swing_bill (A:Block n): utter A swing= (∑ b:Bool, pulse A (amp b) (amp b))-pulse A 1 1 := by
  have he : (1:Block n)=spur (1:Floor n) 1:= amp_one.symm
  rw [swing_form, show dump (n:=n)-(1:Block n)=dump + (-1:ℝ) • 1 from by simp only [neg_smul,one_smul]; rfl,utter_comm,utter_plus,utter_scale,dump_eq,utter_many]; unfold pulse; simp_rw [utter_comm (spur (amp (n:=n) _) _)] -- simp placeholder
  rw [utter_comm (1:Block n),he]; ring

-- polylog wall/window, respects transpose but uses true torus separation.

def fallen (r : ℕ) (x y:Site n) := if r<separation x y then swing x y else 0
def guarded (r:ℕ)(x y:Site n) := if r<separation x y then 0 else swing x y
lemma panes (r:ℕ) : swing (n:=n)= fallen r+guarded r:= by funext x y; simp only [fallen,guarded,Pi.add_apply]; split <;> simp

def fuel (n:Side) : ℝ:= Fintype.card (Site n)
lemma fuel_pos (n:Side) : 0<fuel n:= Nat.cast_pos.mpr Fintype.card_pos

def purchase (n:Side) : ℝ := eigen n * fuel n /2
include hn in
lemma purchase_pos : 0<purchase n:= by unfold purchase; have hh:= fuel_pos n; have he:= eigen_pos hn; positivity -- include hn

def tone : ℝ:= Real.pi^2/4
lemma tone_nn : 0≤tone:= by unfold tone; positivity

def listen (r:ℕ) (A:Block n):= utter A (guarded r) / purchase n -- target β quantity for HELD meterK = cost β/2∑ ... ; size ∼ β (g^-2). This will require caller to normalize (both up front, before series).

-- window cost. use with all-sized Entry and price uniform not spatially decaying
variable (A Z:Block n)
include hn
private lemma quote (M:ℕ) {K:ℝ} (hK : 0≤K)(h:∀ x y:Site n,separation x y≤M → ‖A x y‖≤K) :
    ‖utter A (guarded M)‖ ≤ K*m^2*M^2*(M+M+1:ℝ)^4 * fuel n := by
  let q:= m^2*M^2; let U:= K*q
  have hm : 0 < m:= Full.mesh_pos
  unfold utter; refine (norm_sum_le ..).trans ?_
  have hw(x:Site n): ‖∑ y, A x y*guarded M x y‖ ≤ U*(M+M+1:ℝ)^4:= by
     rw [← Finset.sum_subset (Finset.subset_univ (halo M {x})) (fun y _ hy=> show A x y* guarded M x y=0 from by simp [guarded,lt_of_not_ge (fun he=> hy (near_root.mpr he))])]; apply (norm_sum_le ..).trans
     refine (Finset.sum_le_sum (g:=fun _=> U) (fun i hi=> ?_)).trans ?_
     · have hi':=near_root.mp hi; rw [guarded, if_neg (not_lt.mpr hi'),norm_mul]; exact mul_le_mul (h x i hi') ((swing_bound hn ..).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hi') _) (sq_nonneg _))) (norm_nonneg _) hK
     rw [sum_const,nsmul_eq_mul,mul_comm U (_ ^4)]; refine mul_le_mul_of_nonneg_right ?_ (by unfold U q; positivity); exact_mod_cast (show _≤(M+M+1)^4 from le_trans (Corona.halo_size {x} M) (by simp))
  apply (Finset.sum_le_sum (fun x _=> hw x)).trans_eq; unfold fuel U q; rw [sum_const,nsmul_eq_mul,card_univ]; ring

-- exact cost spectral inverse uses same-site comparisons, independent of volume and mesh.
lemma listens (M : ℕ){z:ℝ} (hz:0≤z) (hf:∀ x y:Site n,separation x y≤ M → ‖A x y-Z x y‖≤ z):
    ‖listen M A-listen M Z‖ ≤ 2*tone*z*(M:ℝ)^2*(M+M+1:ℝ)^4:= by
  have he: A-Z=A + (-1:ℝ) • Z:=by rw [neg_smul,one_smul,sub_eq_add_neg];
  have h := quote hn (A-Z) M hz (show ∀ x y:Site n,separation x y≤ M→ ‖(A-Z) x y‖≤ z from hf); rw [he,utter_plus,utter_scale] at h
  unfold listen; rw [←sub_div,norm_div,show ‖purchase n‖=purchase n from Real.norm_of_nonneg (purchase_pos hn).le,div_le_iff₀ (purchase_pos hn)]
  have hv : m^2≤ tone*eigen n:= eigen_price hn
  refine ((le_of_eq ?_).trans h).trans ?_
  · simp only [neg_mul,one_mul,sub_eq_add_neg]
  -- rearrange for gcongr
  unfold purchase
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hz) (sq_nonneg _)) (by positivity)) (fuel_pos n).le) (le_of_eq (by ring))

def royalty (r:ℝ)(u:ℕ) := Real.exp (-(r*u)/2)* 16*r⁻¹^2
lemma falls (s : ℕ) {r:ℝ} (hr:0<r) (x y:Site n) : ‖fallen s x y‖ ≤ m^2*royalty r s*beam r x y:=by
  unfold fallen; split_ifs with h
  · apply (swing_bound hn ..).trans; rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    let k:ℝ:=r* (separation x y); have hk:(0:ℝ)≤k:= by unfold k; positivity
    have hy : r*(s:ℝ) ≤ k:= mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h.le) hr.le
    have hh : (k/2)^2 / (2:ℝ) ≤ Real.exp (-(r*s)/2)*beam r x y := by
       have hh := poly_gate (orderM:=2) (div_nonneg hk zero_le_two); rw [show ((2:ℕ).factorial:ℝ)=2 from by norm_num [Nat.factorial]] at hh; unfold beam; rw [← Real.exp_add]; refine hh.trans (Real.exp_monotone ?_); linarith only [show r*(s:ℝ) ≤ k from hy] -- k unfolding
    unfold royalty; refine (le_of_mul_le_mul_left ?_ (sq_pos_of_pos hr) : _)
    unfold k at *; rw [show r^2*(Real.exp _*16*r⁻¹^2*beam r x y)=16*(Real.exp (-(r*s)/2)*beam r x y) from by field_simp ]
    nlinarith only [hh, sq_nonneg (r*(separation x y:ℝ))]
  rw [norm_zero]; unfold royalty; positivity [beam_pos r x y]

lemma wall (M : ℕ) {r:ℝ}(hr:0<r): ‖utter A (fallen M)‖ ≤ m^2 * royalty r M * paid A r:= by
  unfold paid utter; simp_rw [Finset.mul_sum]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun x _=> (norm_sum_le ..).trans (Finset.sum_le_sum fun y _=> ?_)); rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (falls hn M hr x y) (norm_nonneg _)).trans_eq (by ring)
lemma flattened (r : ℕ){ε J T:ℝ} (hJ : 0≤ J)(h :‖utter A swing-T*purchase n‖≤ m^2*(ε*fuel n)) (hy:‖utter A (fallen r)‖≤ m^2*(J*fuel n)) :
    ‖listen r A-T‖ ≤ 2*tone * (J+ε):= by
  have hM:= Full.mesh_pos (n:=n)
  have hV:= fuel_pos n
  have hz:= (norm_nonneg _).trans h
  have hp : 0≤ ε:= by exact nonneg_of_mul_nonneg_left (nonneg_of_mul_nonneg_right hz (sq_pos_of_pos hM)) hV -- order?
  have hx:utter A (guarded r)-T*purchase n= utter A swing-T*purchase n-utter A (fallen r):= by
    rw [panes r,utter_comm A (fallen r+guarded r),utter_plus,utter_comm (guarded r),utter_comm (fallen r)]; ring
  have he : listen r A-T= (utter A (guarded r)-T*purchase n)/purchase n:= by unfold listen; field_simp [(purchase_pos hn).ne']
  rw [he,hx,norm_div,show ‖purchase n‖=purchase n from Real.norm_of_nonneg (purchase_pos hn).le,(div_le_iff₀ (purchase_pos hn))]
  refine (norm_sub_le ..).trans ((add_le_add h hy).trans ?_); unfold tone purchase
  have he := mul_le_mul_of_nonneg_right (eigen_price hn) (show 0≤ (ε+J)*fuel n from by positivity)
  nlinarith only [he]

end YM.MatchingLedger.Spring
