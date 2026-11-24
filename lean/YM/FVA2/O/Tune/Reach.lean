import YM.FVA2.O.Tune.Track
import YM.FVA2.O.Dust.QRise
/-!
# Estimates for log-time Taylor slicing

Power counting for budgets through `nav` and `helm`. See `Winner`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Tune
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook
open scoped Topology ContDiff
variable {E I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge} {F Y H:Glade G I}{B:Deck G}{K:Booked B}{M:MS_Data G K}{η:I→ℝ}{P:IntervalFamily I}{n k r:ℕ}{b:ℤ}{i:P.Inst}{x:E}
variable {w:Wire (BH G) E QP}{a c:P.Inst→ℝ}
abbrev sweep (P: IntervalFamily I)(F:Glade G I) : P.Inst → Law G:= fun i=> F (index i) (t i)
abbrev allowance (P:IntervalFamily I)(η:I→ℝ): Prop:= ∀ i, ‖η i‖ ≤ P.logPart i
lemma allotted (hp: allowance P η)(i:P.Inst): ‖η (index i)+ t i‖≤ P.primary.basic i:= (norm_add_le ..).trans (by obtain he:P.logPart (index i)≥1:=P.lg _; obtain hb:=hp (index i); obtain hz:0≤ t i:=(P.beg_nn _).trans i.ge; rw [norm_of_nonneg hz]; unfold IntervalFamily.primary; dsimp only; nlinarith )
lemma beacon {b c:Bool}{F:Pearl.Flats G}(hp:Emit.Host F n)(he: allowance P η): Latch.Lease b c P.primary ( sweep P (nameR ( Outlook.four n F ) η )) ( fun i=> P.primary.length i ^ (-(n:ℤ)) ) := nameD hp (a:=t) (fun _=>rfl) ( allotted he )
lemma brightB (he: allowance P η): Latch.Lease true true P.primary ( sweep P ( Lives.gather M η n ) ) ( fun i=>P.primary.length i ^ (-(4:ℤ)) ) := beacon (Emit.Host.host (Dock.gang (M.bulkOK n))) he
local notation "A₀" => ( fun i:P.Inst=> lineA G (t i) )
local notation "B₀" => ( fun i:P.Inst=> lineB G (t i) )
def die (P:IntervalFamily I) : P.Inst→ℝ:= fun i=> (P.primary.length i)⁻¹
lemma μA (P:IntervalFamily I)(G:Gauge) : Sheet P.primary 1 ( fun i=>lineA G (t i) ):= cost_D ( S:=P.primary ) (a:=t) (fun _=>rfl)
lemma μB (P:IntervalFamily I)(G:Gauge) : Sheet P.primary (die P) ( fun i=>lineB G (t i) ):= edgeT P.primary ( t:=t ) (fun _=>rfl) shapeB O.Ward.rB -- ns
lemma die_p : Latch.nn ( die P ):= fun i=>inv_nonneg.mpr ((P.primary.pos i).le)
lemma partA (h:Warm F false)(hr: Lens false P.primary (sweep P F) a (r+2))(ha: Latch.nn a): Lens false P.primary (sweep P ((both G I).P F)) a r:= by
    change Lens false P.primary (sweep P (Rcy (fun _=>lineA G) F)) a r; rw [spine h realityA]; exact (one_mul a) ▸ penny hr ha (μA P G) (fun _=>zero_le_one) (Tall _ 5 (by omega)) (fun E _=>tom _ 5 (by omega))
lemma partB (h:Warm F false)(hr:Lens false P.primary (sweep P F) a (r+2))(ha:Latch.nn a): Lens false P.primary (sweep P (Rcy (fun _=>lineB G) F)) (die P * a) r:= by rw [spine h realityB]; exact penny hr ha (μB P G) die_p (Tall _ 5 (by omega)) (fun E _=>tom _ 5 (by omega))
lemma treeA (hp:allowance P η)(hr:Latch.Lease false false P.primary (sweep P F) a)(ha:Latch.nn a): Latch.Lease false false P.primary (sweep P (( both G I ).X (Lives.gather M η n) F)) a:= by
    apply Latch.Lease.sticks (trunks ( K:=fun i=>lineA G ( t i ) ) (fun i j=> Latch.polar (μA P G i j)) ( brightB hp ) hr.highp (fun i=>zero_le_one) (fun i=>length_p ..) ha); intro i; simp only [positive, Pi.one_apply,Pi.mul_apply]; exact le_of_eq (by field_simp [( P.primary.pos i ).ne'])
lemma treeB (hp:allowance P η)(hr:Latch.Lease false false P.primary (sweep P F) a)(ha:Latch.nn a): Latch.Lease false false P.primary (sweep P (( both G I ).C (Lives.gather M η n) F)) (die P*a):= by
    apply Latch.Lease.sticks (trunks ( K:=fun i=>lineB G ( t i ) ) (fun i j=> Latch.polar (μB P G i j)) ( brightB hp ) hr.highp die_p (fun i=>length_p ..) ha); intro i; simp only [positive,die, Pi.mul_apply]; exact le_of_eq (by field_simp [( P.primary.pos i ).ne'])
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma A_sum (s:Finset E){F:E→ Glade G I}(hp:∀ i∈s,Latch.Lease false false P.primary (sweep P (F i)) a)(ha:Latch.nn a): Latch.Lease false false P.primary (sweep P (∑ i∈s,F i)) a:= by
    classical induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact Latch.Lease.zero ha| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (hp _ (by simp)).plus (ih fun j hj=> hp j (mem_insert_of_mem hj))
variable {X:T (Glade G I)}
lemma A_can (hp:allowance P η)(ha:Latch.nn a)(hv:∀ m<n,Latch.Lease false false P.primary (sweep P ( X m )) a): Latch.Lease false false P.primary (sweep P (pairW (both G I).X (Lives.gather M η) X n)) a := by
    rw [paired]; refine A_sum _ ?_ ha; intro i hi; by_cases he:i.1=0; · rw [he,zero_B M,map_zero,LinearMap.zero_apply]; exact Latch.Lease.zero ha
    exact treeA hp (hv i.2 (by obtain h:= Finset.mem_antidiagonal.mp hi; omega)) ha
lemma B_can (hp:allowance P η)(ha:Latch.nn a)(hv:∀ m<n,Latch.Lease false false P.primary (sweep P (X m)) a): Latch.Lease false false P.primary (sweep P (pairW (both G I).C (Lives.gather M η) X n)) (die P * a):= by
    have he': Latch.nn (die P*a):=fun i=> mul_nonneg (die_p i) (ha i); rw [paired]; refine A_sum _ ?_ he'; intro i hi; by_cases he:i.1=0; · rw [he,zero_B M,map_zero,LinearMap.zero_apply]; exact Latch.Lease.zero he'
    exact treeB hp (hv i.2 (by obtain h:= Finset.mem_antidiagonal.mp hi; omega)) ha
lemma Q_travel (ha:Latch.nn a)(he:Latch.Lease false false P.primary (sweep P F) a): Latch.Lease false false P.primary (sweep P ( Lives.Z G I F )) (die P*a):= by
    refine Latch.Lease.sticks ( O.Cool.lease_Q (η:=t) (fun _=>rfl) he ha) (fun i=>?_); simp only [Pi.mul_apply]; exact le_of_eq (congr_arg (· * a i) (zpow_neg_one (P.primary.length i)))
lemma h_cost (h:Warm (X n) false)(hp:allowance P η)(ha:Latch.nn a)(hr:Lens false P.primary (sweep P (X n)) a (r+2))(hv:∀ m<n,Latch.Lease false false P.primary (sweep P (X m)) a): Lens false P.primary ( sweep P ( helm M η X n ) ) a r:= ( partA h hr ha ).plus ( pinch ( A_can hp ha hv ) (fun i=>Bool.noConfusion i) )
lemma VAT (h:Warm F false)(ha:Latch.nn a)(he:Latch.Lease false false P.primary (sweep P F) a): Latch.Lease false false P.primary (sweep P ( (both G I).J F )) (die P*a):= by rw [front G I,LinearMap.add_apply]; apply Latch.Lease.plus ( Q_travel ha he ) (poses (fun _ _=> partB h ( pinch he (fun i=>Bool.noConfusion i) ) ha )) -- unif
lemma B_life (h:Warm (X n) false)(hp:allowance P η)(ha:Latch.nn a)(hr:Latch.Lease false false P.primary (sweep P (X n)) a)(hv:∀ m<n,Latch.Lease false false P.primary (sweep P (X m)) a): Latch.Lease false false P.primary (sweep P (nav M η X n)) (die P*a):= ( VAT h ha hr ).plus ( B_can hp ha hv )
lemma Q_ok (he: O.Lives.Certified X M η b )(ha:Latch.nn a)(hp: allowance P η)(hr:Lens false P.primary (sweep P (X n)) a (r+2))(hv:∀ m<n,Latch.Lease false false P.primary (sweep P (X m)) a): Lens false P.primary (sweep P ( Lives.Z G I ( X n ) )) (die P*a) r:= by
    have h:= (partB (he.1.life n).cross hr ha).plus (pinch ( B_can (M:=M) hp ha hv ) (fun i=>Bool.noConfusion i)); obtain hh': Lives.Z G I (X n)= -(Rcy (fun _=>lineB G) (X n)+pairW (both G I).C (Lives.gather M η) X n):= by
       apply eq_neg_of_add_eq_zero_left; rw [ ← add_assoc, show Lives.Z G I (X n) + Rcy _ (X n) = (both G I).J (X n) from rfl ]; exact congr_fun he.2 n
    rw [hh']; exact fun E _ _ w hw hp'=> Costs.neg (h E w hw hp')
end YM.FVA2.O.Tune
