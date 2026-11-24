import YM.OPE.Compatible.Squalls.Culminate
/-!
# One linked volume leg. Estimate independent of period. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
-- Norm for ℓ-one attachment on root shift
abbrev Embers (I:Type*) (r d:ℕ):=(Page I (r+1) × Page I (d+1)) × Cover
abbrev mort (i: Page I (r+1)) := Fin.tail i
def tideAt (i:Page I (r+1))(j:Page I (d+1))(x:Cover):= primary i+x-primary j
def rendX (v:Embers I r d): Page I (r+d):= Fin.append (mort v.1.1) (slide (tideAt v.1.1 v.1.2 v.2) (mort v.1.2))
def ticketX (A:Row I I)(p:Script I (r+1))(q:Script I (d+1))(v:Embers I r d):ℝ:=p v.1.1*q v.1.2 * A (v.1.1 0).2 (v.1.2 0).2 v.2
def cotton (A:Row I I)(p:Script I (r+1))(q:Script I (d+1)): Script I (r+d):= Sack.rope rendX (ticketX A p q)
lemma notched {I:Type*}(i:Page I (r+1)): stamp (mort i) ≤ stamp i:=by
    rw [perimeter (mort i),perimeter i,Fin.sum_univ_succ]; unfold mort; gcongr; exact Nat.le_add_left .. 
lemma span_join (p:Page I r)(q:Page I d): stamp (Fin.append p q) +1= stamp p+stamp q:=by
    rw [perimeter (Fin.append p q),perimeter p,perimeter q,Fin.sum_univ_add]; simp only [Fin.append_left,Fin.append_right]; omega
abbrev coal (m:ℕ)(v:Embers I r d):ℝ:= (figure m v.1.1*figure m v.1.2)*poise m v.2
lemma lend (v:Embers I r d):let C:=stamp v.1.1* stamp v.1.2 * notch v.2; stamp (rendX v) ≤ (3*d+2)*C:=by
     intro C; let i:= v.1.1; let j:=v.1.2; let b:=v.2; let x:=tideAt i j b; let p:=mort i; let q:=mort j
     have hP : stamp i ≤ C:= Nat.le_trans (Nat.le_mul_of_pos_right _ (notch_one j.xy)) (Nat.le_mul_of_pos_right _ (notch_one b)); have hp : stamp j ≤ C := Nat.le_trans (Nat.le_mul_of_pos_left _ (notch_one i.xy)) (Nat.le_mul_of_pos_right _ (notch_one b)); have ht₀: notch b≤C:= Nat.le_mul_of_pos_left _ (Nat.mul_pos (show 0 < stamp i from notch_one i.xy) (show 0 < stamp j from notch_one j.xy)) -- wrong
     have hv : size x ≤ 3*C:=by
        have h:size (primary i)+size b+size (primary j) ≤3*C:=by
           have hi:=i.primary_size;have hj:=j.primary_size; unfold notch at ht₀; omega
        unfold x tideAt; rw [sub_eq_add_neg]; apply (size_add ..).trans; rw [size_neg]; exact (Nat.add_le_add_right (size_add ..) _).trans h
     have he:= span_join p (slide x q); have ht:= Page.slide_price q x; have hi : stamp p≤stamp i:=notched i; have hj: stamp q≤stamp j:=notched j; change stamp (Fin.append p ((slide x) q)) ≤ _; linarith only [he,ht,hi,hj,hP,hp, Nat.mul_le_mul_left d hv]
lemma coinLend (m:ℕ)(v:Embers I r d): figure m (rendX v)≤coal m v*((3*d+2:ℕ):ℝ)^m:=by
   unfold figure coal poise Page.figure poise; rw [mul_comm,← mul_pow, ← mul_pow,← mul_pow] -- maybe order issue
   apply pow_le_pow_left₀ (Nat.cast_nonneg _); exact_mod_cast lend v
lemma cottonPile {A:Row I I}(h:A.strip s U)(hs_foo:0<s)(hfoo:0≤ U){p:Script I (r+1)}(hp:soot m p D){q:Script I (d+1)}(hq:soot m q b): Sack (coal m) (ticketX A p q) (D*b*(widthCost s m*U)):=by
    let f(v:Page I (r+1) × Page I (d+1)):= p v.1*q v.2; let u(v:Page I (r+1) × Page I (d+1)):= figure m v.1*figure m v.2; have hQ: Sack u f (D*b):= Sack.multiplex hp hq (fun i=>by unfold u f; rw [norm_mul]; exact le_of_eq (by ring)) (fun i=> mul_nonneg (zero_le_one.trans (payer m _)) (zero_le_one.trans (payer m _)))
    let F(i:Page I (r+1)× Page I (d+1)):= A (i.1 0).2 (i.2 0).2
    have hh(i:Page I (r+1) × Page I (d+1)): Sack (poise m) (F i) (widthCost s m*U):=by
       have ht:= width_income hs_foo (h (i.1 0).2 (i.2 0).2) m; unfold Sack; simp_rw [liftCostSame, mul_comm (liftCost ..)]; exact ht
    let z(i:Page I (r+1) × Page I (d+1))(b:Cover):=u i*‖f i‖*(poise m b*‖F i b‖); let t i:= u i*‖f i‖*(widthCost s m*U)
    have hs(i): SumBudget (z i) (t i):= ⟨fun j=> mul_nonneg (hQ.1 i) ((hh i).1 j), (hh i).2.1.mul_left _, by unfold z; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (hh i).2.2 (hQ.1 i)⟩
    unfold Sack; rw [show (fun i=> coal m i*‖ticketX A p q i‖)=(uncurry z) from funext fun i=>by change ((u i.1 * _) * ‖f i.1*F i.1 i.2‖)= z i.1 i.2; rw [norm_mul]; unfold z; ring]
    let w:=uncurry z; have hw:0≤w:=fun i=> (hs i.1).1 i.2
    -- U ≥0 if I not empty. otherwise P slots empty but row width arbitrary breaks bound e.g. D positive. require U nonneg
    let K:=widthCost s m*U; have hK: 0≤ K:=mul_nonneg (zero_le_one.trans (widthCost_ge hs_foo m)) hfoo
    have hk: Summable fun i=>∑' j,z i j := (hQ.2.1.mul_right K).of_nonneg_of_le (fun i=>tsum_nonneg ((hs i).1)) (fun i=>(hs i).2.2)
    have hv: Summable w:= (summable_prod_of_nonneg (f:=w) hw).mpr ⟨fun i=>(hs i).2.1,hk⟩; exact ⟨hw,hv,by erw [hv.tsum_prod]; change (∑' i,∑' j,z i j) ≤ _; apply (hk.tsum_le_tsum (fun i=>(hs i).2.2) (show Summable t from hQ.2.1.mul_right _)).trans; unfold t; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hQ.2.2 hK⟩
lemma cotton_cost {A:Row I I}(h:A.strip s U)(hs:0<s)(hh:0 ≤ U) {p:Script I (r+1)}(hp:soot m p D){q:Script I (d+1)}(hq:soot m q b): soot m (cotton A p q) (D*b*(widthCost s m*U)*((3*d+2:ℕ):ℝ)^m):= Sack.cart _ (cottonPile h hs hh hp hq) (by positivity) (payer m) (coinLend _)
end Script
end YM.OPE.Flume
