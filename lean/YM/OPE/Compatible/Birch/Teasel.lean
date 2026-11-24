import YM.OPE.Compatible.Birch.Wrap
/-! SelfLink. wind bills. systematic -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}{N:Side}
namespace Script
open Page
-- valuation kernel at 0 and transpose signs; Shift Kernel as Opp. stone of loops depends on max n^t. 
abbrev melt (i:Page I (r+2)): Page I r:= mort (mort i)
abbrev poke (p:Page I (r+2)):Cover:=(mort p 0).1-(p 0).1
def tunnel (A:Row I I) (p:Script I (r+2)): Script I (r+2):=fun i=> p i * A (i 0).2 (mort i 0).2 (poke i)
def pad (A:Row I I) (p: Script I (r+2)):Script I r:= Sack.rope melt (tunnel A p)
lemma tunnel_budget {A:Row I I}(h:A.strip s U)(ht:0 ≤ s)(hb:0 ≤ U){p:Script I (r+2)}(hp:soot m p b): soot m (tunnel A p) (b*U):=by
    let z i:= figure m i * ‖p i‖; have hz i j v: ‖A i j v‖≤ U:= by
      have hh := (show Sack (fun _=>1) (A i j) U by unfold Sack; simp only [one_mul];exact (h i j).unweighted ht); simpa only [one_mul] using hh.single v
    refine budget_minor (g:=fun i=> z i*U) ⟨fun i=>mul_nonneg (hp.1 i) hb,hp.2.1.mul_right _,by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hp.2.2 hb⟩ (fun i=>mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _)) (fun i=>?_)
    unfold z; rw [tunnel,norm_mul,_root_.mul_assoc]; gcongr; exact zero_le_one.trans (payer m i); exact hz .. --
lemma pad_charge {A:Row I I}(h:A.strip s U)(ht:0 ≤ s)(hb:0 ≤ U){p:Script I (r+2)}(hp:soot m p b): soot m (pad A p) (b*U):=by
     let p:= tunnel_budget h ht hb hp; apply (Sack.cart _ p zero_le_one (payer m) (fun i=>show figure m (melt i)≤ figure m i*1 by rw [mul_one]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (notched (mort i)).trans (notched i)) _)).tips; simp
-- scribe indexed connecting first two
variable [Fintype I]
def routeTap (A:Matrix (Tab I N) (Tab I N) ℝ)(u:Script I (r+2))(x: Fin r→deck I N)(y: Site N):= ∑ i:Tab I N,∑ j:Tab I N,A i j * scribe y u (Fin.cons (deltaH i) (Fin.cons (deltaH j) x))
private def Ipoint {n}(p:Page I (n+1))(y:Site N): Tab I N:= (y+wrap N (p 0).1,(p 0).2)
lemma Tap_reads (A: Matrix (Tab I N) (Tab I N) ℝ) (u: Script I (r+2))(x: Fin r→deck I N)(y: Site N)(h:Summable u):
   HasSum (fun i=> u i * A (Ipoint i y) (Ipoint (mort i) y)*render y (melt i) x) (routeTap A u x y):=by
    have he(i j: Tab I N): HasSum (fun g:Page I (r+2)=> A i j * (u g*render y g (Fin.cons (deltaH i) (Fin.cons (deltaH j) x)))) _:= ((instruments u h ..).summable.hasSum).mul_left _
    unfold routeTap; convert! hasSum_sum (s:=univ) (fun i _ => hasSum_sum (s:=univ) (fun j _=> he i j)) using 1
    ext1 i; simp_rw [renderer]; simp [mul_ite]; ring_nf; rw [_root_.mul_right_comm];rfl
lemma pad_layers (A:Row I I)(h:A.strip s U)(hk:0<s)(ha:0≤ U)(p:Script I (r+2))(w:ℝ)(hp:soot m p w)(n:Side)(x:Fin r→deck I n)(y:Site n) :
    (n.val:ℝ)^m * ‖routeTap (A.acts n) p x y - scribe y (pad A p) x‖ ≤ ((∏ i, ‖x i‖)* (8:ℝ)^m * widthCost s m*U)*w:=by
    have hh:= tunnel_budget h hk.le ha hp; let v(i:Page I (r+2)):= tunnel A p i*render y (melt i) x; let g:= fun i:Page I (r+2)=> p i*A.acts n (Ipoint i y) (Ipoint (mort i) y) * render y (melt i) x
    let C:= ∏ i, ‖x i‖; have hC:0 ≤ C:=prod_nonneg fun _ _=>norm_nonneg _; have ht(i) : ‖render y (melt i) x‖≤ C:= (show _ from ?_)
    · have hS : Summable v := ((sootS hh).norm.mul_right C).of_norm_bounded fun i=>by unfold v; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ht _) (norm_nonneg _)
      let z:ℝ:= n.val; suffices H: z^m * ‖(∑' i,g i)-(∑' i,v i)‖≤ _ by
           unfold scribe pad; rw [Sack.cart_bill melt (fun i=> render y i x) hS]; exact (Tap_reads _ p _ _ (sootS hp)).tsum_eq ▸ H
      let K:= C*8^m*widthCost s m*U; have hy:0 ≤ K:=by unfold K; have hv:0 ≤ widthCost s m:= zero_le_one.trans (widthCost_ge hk m); positivity
      have he:= (show HasSum g _ from Tap_reads (A.acts n) _ _ y (sootS hp)); let f(i):=g i-v i; have hs: Summable f:= he.summable.sub hS
      change _ ≤ K*w
      rw [← Summable.tsum_sub he.summable hS]; apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs.norm) (show 0 ≤ z^m from by unfold z; positivity)).trans
      rw [← tsum_mul_left]; let P i:=figure m i*‖p i‖; apply ((hs.norm.mul_left _).tsum_le_tsum (g:=fun i=> K * P i) ?_ (hp.2.1.mul_left K)).trans
      · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hp.2.2 hy
      intro i; have hv: A.acts n (Ipoint i y) (Ipoint (mort i) y)=A.acts n (0,(i 0).2) (wrap n (poke i),(mort i 0).2):=by
           change (∑' a:Cover,if (y+wrap n (mort i 0).1)= (y+ wrap n (i 0).1)+wrap n a then _ else 0)=∑' a:Cover, if (wrap n (poke i))=0+wrap n a then A (i 0).2 _ a else 0; apply tsum_congr;intro a; simp only [_root_.add_assoc,add_right_inj,poke,_root_.map_sub,zero_add]; congr! 1; simp [sub_eq_iff_eq_add,add_comm]
      let R:= A.acts n (Ipoint i y) (Ipoint (mort i) y) - A (i 0).2 (mort i 0).2 (poke i); have hW: z^m * ‖R‖ ≤ 2^m*(4^m*figure m i)*widthCost s m*U:=by
          unfold z R; rw [hv]; apply (coefWind A h hk ..).trans
          have ht:poise m (poke i) ≤4^m*figure m i:=by
             have he: notch (poke i) ≤ 4* stamp i:=by
                have hx : size (poke i)≤ size (primary (mort i))+size (primary i):=by unfold poke; rw [sub_eq_add_neg]; exact (size_add ..).trans (by rw [size_neg]; rfl)
                have ht:= (Page.primary_size (mort i)).trans (notched i); have hu:= i.primary_size; have hh:1 ≤ stamp i:=notch_one i.xy; unfold notch; omega
             unfold poise figure poise; rw [← mul_pow]; gcongr; exact_mod_cast he
          have hh:0 ≤ widthCost s m:=zero_le_one.trans (widthCost_ge hk m); gcongr
      rw [show f i=p i * R* render y (melt i) x by unfold f g v tunnel R;ring]; calc
          _ = (z^m*‖R‖)*‖p i‖*‖render y (melt i) x‖:=by rw [norm_mul,norm_mul]; ring
          _ ≤ _:=by
             apply (mul_le_mul (mul_le_mul_of_nonneg_right hW (norm_nonneg _)) (ht i) (norm_nonneg _) (mul_nonneg (le_trans (mul_nonneg (pow_nonneg (show 0 ≤ z from Nat.cast_nonneg _) _) (norm_nonneg _)) hW) (norm_nonneg _))).trans_eq; unfold K P; rw [show (8:ℝ)^m= 2^m*4^m by rw [← mul_pow]; norm_num];ring
    · unfold render; rw [norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=> norm_le_pi_norm _ _)
end Script
end YM.OPE.Flume
