import YM.Contacts.Pulse.Registry
/-! Temporal recursion price, polynomial in input/prices; differences linear
in the discrepancy budgets. Width reserve must already be assigned for any
loop/winding comparisons. No stepwise replacement over infinitely many RG levels. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Filter Finset RG
open scoped Topology Classical NNReal BigOperators
variable {ι κ α β X Y T: Type*} [Group T] [MulAction T X]
variable {p:X→Y}{l:Range Y}{m:Range X}{W:MirrorWay p T m l}
variable {I:X→X→ℝ}{J:Y→Y→ℝ}{d u v:ℝ}

-- scale-meter recursion not carrying C-power losses on precision
-- b-system cap same for both
abbrev maxSum (k t:ℕ) : ℝ := ‖((((k+1)*(t+1):ℕ):ℝ)/2)‖
def shiftFee (t:ℕ):ℝ := maxSum (t+1) t
def licht (d:ℝ)(U V:ℕ→ℝ)(k:ℕ×ℕ) : ℝ := maxSum k.1 k.2 * (U (k.1+1)*(d*V (k.2+1)))
def lichtQ (d v:ℝ)(U V X Y:ℕ→ℝ)(k:ℕ×ℕ):ℝ:= maxSum k.1 k.2 * (X (k.1+1)*(d*V (k.2+1))+U (k.1+1)*(v*V (k.2+1))+U (k.1+1)*(d*Y (k.2+1)))
private lemma pay_light {e k l:ℕ} {b f z y:ℕ→ℝ}(hd : k+l=e){F K:Rack X}{G H:Rack Y} (h: Waves W I J d u v)(hf:Two W (F (k+1)) (G (k+1)) (b (k+1)) (z (k+1)))(hw:Two W (K (l+1)) (H (l+1)) (f (l+1)) (y (l+1))): Two W (light I e k l F K) (light J e k l G H) (licht d b f (k,l)) (lichtQ d v b f z y (k,l)) := by
  subst e; unfold light; rw [dif_pos rfl, dif_pos rfl]; change Two W (meter I (F (k+1)) (K (l+1))) (meter J (G (k+1)) (H (l+1))) _ _; exact ((Two.stitch_cost h (hf.renew (finSuccEquiv k)) (hw.renew (finSuccEquiv l))).renew finSumFinEquiv |>.print).scale _

abbrev TableFee := ℕ→ℕ→ℝ

def payout (d:ℝ) (T:ℕ→TableFee) (n e r:ℕ) := shiftFee r*(d*T n e (r+2))+∑ p∈ antidiagonal e,∑ q∈antidiagonal n, ∑ k∈ antidiagonal r, licht d (T q.1 p.1) (T q.2 p.2) k
def wakeup (d u v:ℝ)(T R:ℕ→TableFee)(n e r:ℕ):= shiftFee r*(v*T n e (r+2)+d*R n e (r+2)+u*T n e (r+2))+∑ p∈ antidiagonal e,∑ q∈ antidiagonal n, ∑ k∈ antidiagonal r, lichtQ d v (T q.1 p.1) (T q.2 p.2) (R q.1 p.1) (R q.2 p.2) k
private lemma twins (h:Waves W I J d u v){F:ℕ→ℕ→ Rack X}{H:ℕ→ℕ→Rack Y}{P Q:ℕ→ TableFee}{n:ℕ}(hp:∀ i≤n,∀ j k, Two W (F i j k) (H i j k) (P i j k) (Q i j k)) (e r:ℕ): Two W (wake I F e n r) (wake J H e n r) (payout d P n e r) (wakeup d u v P Q n e r):= by
   refine Two.add (((Two.loop_est h ((hp n le_rfl e (r+2)).renew (spanLift _))).print).scale _) (Two.finite (antidiagonal e) fun i _=> Two.finite (antidiagonal n) fun j hj => Two.finite (antidiagonal r) fun k hk=> ?_)
   have ht:= mem_antidiagonal.mp hj; exact pay_light (mem_antidiagonal.mp hk) (G:=H j.1 i.1) h (hp j.1 (by omega) _ _) (hp j.2 (by omega) _ _)

def levity (d:ℝ)(P : TableFee) : ℕ → TableFee
 | 0=>P
 | n+1=> fun e r=> ‖((n+1:ℕ):ℝ)⁻¹‖* payout d (fun i=> if _h:i≤ n then levity d P i else 0) n e r
termination_by t=>t
decreasing_by omega

def lowland (d u v:ℝ)(P H:TableFee) : ℕ→TableFee
 | 0=>H
 | n+1=> fun e r=> ‖((n+1:ℕ):ℝ)⁻¹‖* wakeup d u v (levity d P) (fun i=> if _h:i≤ n then lowland d u v P H i else 0) n e r
termination_by t=>t
decreasing_by omega
lemma downpay (d:ℝ)(P:TableFee) (n e r:ℕ): levity d P (n+1) e r=‖((n+1:ℕ):ℝ)⁻¹‖*payout d (levity d P) n e r:= by
  rw [levity]; unfold payout; dsimp only; rw [dif_pos le_rfl];
  apply congr_arg (‖((n+1:ℕ):ℝ)⁻¹‖ * ·); apply congr_arg; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j hj=>?_)); have ht:= mem_antidiagonal.mp hj; rw [dif_pos (by omega),dif_pos (by omega)] -- under binder
lemma mazy (d u v:ℝ)(P Q:TableFee) (n e r:ℕ): lowland d u v P Q (n+1) e r=‖((n+1:ℕ):ℝ)⁻¹‖*wakeup d u v (levity d P) (lowland d u v P Q) n e r:= by
  rw [lowland]; unfold wakeup; dsimp only; rw [dif_pos le_rfl];
  apply congr_arg (‖((n+1:ℕ):ℝ)⁻¹‖ * ·); apply congr_arg; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j hj=>?_)); have ht:= mem_antidiagonal.mp hj; rw [dif_pos (by omega),dif_pos (by omega)]
section
variable (h: Waves W I J d u v){F:ℕ→Rack X}{H:ℕ→ Rack Y}{P Q:TableFee}(hq:∀ e r, Two W (F e r) (H e r) (P e r) (Q e r))
include hq h
lemma prism (n e r:ℕ) : Two W (gathering I F n e r) (gathering J H n e r) (levity d P n e r) (lowland d u v P Q n e r):=by
  induction n using Nat.strongRecOn generalizing e r with | _ n ih=>
  cases n with
  | zero=> simp only [levity,lowland,gathering_start]; exact hq _ _
  | succ n=> rw [gathering_next,gathering_next,downpay,mazy]; exact (twins h (fun i hi j k=> ih i (by omega) j k) e r).scale _

def sky (P:ℕ→TableFee)(e r:ℕ):= ∑ i∈ range (3*e+1),P i e r
lemma completed (e r:ℕ) : Two W (Form.massaged I F e r) (Form.massaged J H e r) (sky (levity d P) e r) (sky (lowland d u v P Q) e r):= Two.finite _ fun i _=>prism h hq i e r
end
end YM.Pulse
