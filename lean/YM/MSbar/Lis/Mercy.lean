import YM.MSbar.Lis.Scout
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n: Side}
local notation "X"=>Positions (Primary n G)
local notation "K"=>Primary n G
variable (F:X→ℝ)(x:Primary n G)(s:Strand G)(k m:ℕ)(i:Primary n G)(l:List (Primary n G))
local notation "Y"=> buoy F 0
local notation "ℓ"=>Measuring.chart n G
noncomputable def ace (x:Primary n G)(s:Strand G)(j:Site n) : G.Color:= Midpoint.zone (rope x) j (Exterior.axisEquiv.symm s.1) • sun G s.2
lemma axis (x:Site n)(s:Strand G): rope (argo n G x s) = (x,Exterior.axisEquiv.symm s.1):=rfl
lemma rideAt : grad (ace x s) i= sway (fun j=> Midpoint.zone (rope x) j (Exterior.axisEquiv.symm s.1)) (rope i)*(sun G s.2) i.2:=by
    let a:= ace x s; let f:= grad a; let L:=panel G n
    have hh: (panel G n) f= gradient a := L.apply_symm_apply _; have hi:(L f (rope i)) i.2= f (primary (rope i) i.2):= rfl
    rw [←show f (primary (rope i) i.2)=grad (ace x s) i from congrArg f (curr i),← hi, hh]; unfold a AnalyticBridge.VerifiedReset.gradient sway; unfold ace; simp only [PiLp.sub_apply,PiLp.smul_apply, sub_mul]; rfl
lemma signs (q:ℕ)(z:Strand G)(T:List Axis)(hh:T.length≤1)(hi:T.length≤q): |target x i T z|≤ beadPad (rope x).1 (rope i).1 q:=by
    unfold target; split; next ht=>
       cases T with
       | nil=>simp [matry];unfold beadPad;exact one_le_pow₀ (by simp)
       | cons j L=> have hh:L=[]:=by simpa using hh
                    rw [hh]; simp only [matry,List.length_nil,Nat.cast_zero,zero_add,inv_one,one_mul,mul_one]; change |coord _ _ j| ≤ _; apply (small_coord ..).trans; let m:=separation (rope i).1 (rope x).1; change _ ≤ (1+(m:ℝ))^q; calc
                        _ ≤ 1+(m:ℝ):=by exact le_add_of_nonneg_left zero_le_one
                        _ ≤ _:=by nth_rw 1 [←pow_one (1+(m:ℝ))];apply pow_le_pow_right₀ (by simp); simp_all
    rw [abs_zero]; unfold beadPad; positivity
noncomputable def tear (x:Primary n G)(s:Strand G)(i:Primary n G):=target x i [] s-grad (ace x s) i
set_option quotPrecheck false
local notation "S!"=> separation (rope i).1 (rope x).1
local notation "T!"=>beadPad (rope x).1 (rope i).1 1
lemma patch (h:tear x s i ≠0): n.val ≤ 100*(separation (rope i).1 (rope x).1+1):=by
    by_contra! hz; apply h
    let b:= Exterior.axisEquiv.symm s.1; let c:= (rope i).2
    have hh:sway (fun j=>Midpoint.zone (rope x) j b) (rope i)= if b=c then (1:ℝ) else 0:=by unfold sway; dsimp only; rw [sway_mid _ _ _ hz,zone_low]; unfold halfE c; split_ifs <;> ring
    have hx:b=c ↔ s.1=i.1.2:= Exterior.axisEquiv.symm.injective.eq_iff
    rw [tear,rideAt,hh]; simp only [hx, target,Prod.mk.eta,(show (i.1.2,i.2)=s ↔ i.1.2=s.1 ∧ i.2=s.2 from Prod.ext_iff),matry]; simp [sun]; by_cases he:s.1=i.1.2<;>by_cases hc:s.2=i.2<;>simp_all [eq_comm]
lemma sails: |tear x s i| ≤ 4*beadPad (rope x).1 (rope i).1 1 :=by
    have hp := signs x i 0 s [] (by simp) (by simp) -- args
    let f:=rope x; let j:=rope i
    let P:= beadPad f.1 j.1 1; have hP :1 ≤ P:=by unfold P beadPad; simp
    let b:=Exterior.axisEquiv.symm s.1
    have hv(f:G.Color)(i:G.ColorIndex)(hf:‖f‖=1): |f i|≤1:= by exact hf ▸ PiLp.norm_apply_le (p:=2) f i -- argument
    rw [tear,rideAt]; refine (abs_sub ..).trans ?_; change _ ≤ 4*P; refine le_trans (b:=beadPad f.1 j.1 0+(2*P+P)) (add_le_add hp ?_) ?_
    · rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg (sway _ j)) (hv _ _ (sunny _))).trans ((abs_sub ..).trans (add_le_add (sofB f j b) (sofa f j.1 b)))
    unfold beadPad; rw [pow_zero]; linarith only [hP] -- inspect binder
-- cost.Power weighted multiplier.in four remains.Merge A
include l
lemma heaped {p:ℕ}{a:ℝ}(hp:6≤p)(ha:0≤a)(u:ℝ)(hu:|u| ≤ 1+(dim (x::i::l):ℝ)): |tear x s i*u| ≤ (4*100^3/(n.val:ℝ)^3)*swipe ℓ a p (x::i::l):=by
   let T:= x::i::l; let W:ℝ:=1+(dim T:ℝ); let V:= swipe ℓ a p T; have hw:1≤W:=by unfold W; simp
   have hv:W^6≤V:=by refine (pow_le_pow_right₀ hw hp).trans (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hw) _) (Real.one_le_exp (by positivity)))
   have he : S! ≤ dim T:= curve (x:=ℓ i) (y:=ℓ x) (by simp [T,Whisk.zone]) (by simp [T,Whisk.zone]); have hd:T! ≤ W:=by unfold beadPad W; rw [pow_one]; exact_mod_cast Nat.add_le_add_left he 1
   let C:=n.val; have hx:0 < (C:ℝ):=by unfold C; positivity
   by_cases hg:tear x s i=0; rw [hg,zero_mul,abs_zero]; exact mul_nonneg (by positivity) (effect ..|>.le)
   have hi:(C:ℝ)≤100*W:=by have ht:=patch x s i hg; unfold W; exact_mod_cast (show C≤100*(1+dim T) by unfold C;omega)
   rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hx 3),abs_mul]
   refine (mul_le_mul (mul_le_mul ((sails x s i).trans (by exact mul_le_mul_of_nonneg_left hd (by norm_num: 0≤(4:ℝ)))) hu (abs_nonneg _) (by linarith only [hw] : 0 ≤ 4*W)) (pow_le_pow_left₀ hx.le hi _) (by positivity) (by have hp:0≤ W:=zero_le_one.trans hw; exact mul_nonneg (by positivity : 0 ≤ 4*W) hp)).trans ?_
   change 4*W*W*(100*W)^3 ≤ _; refine le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hw (by omega :5 ≤6)).trans hv) (by norm_num :0≤(4*100^3:ℝ)))
end YM.MSbar.Lis
