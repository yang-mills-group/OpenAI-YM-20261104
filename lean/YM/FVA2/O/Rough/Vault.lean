import YM.FVA2.O.Rough.City
/-!
# Log times for the overlap bounds (`Home`)

Rough budgets (no derivatives) for the same MS evolution and `nav`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Rough
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook
open scoped Topology ContDiff Interval
variable {α E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {η:I→ℝ}{a x:α→ℝ}{n m:ℕ}{b c:Bool}
structure Home (α I:Type) extends Scale α where
   pick : α→ I
   t: α→ℝ
   slot u:exp ( t u )=length u
variable {G: Gauge}{S:Home α I} {X Y:T ( Glade G I )}{B:Deck G}{K:Booked B}{M:MS_Data G K}
variable {V F H:Glade G I} {x:α→ℝ}
def liveP (S:Home α I) (η:I→ℝ) : Prop:= ∀ i, ‖η ( S.pick i ) + S.t i‖ ≤ S.basic i
abbrev sendT (S:Home α I)(F:I→ℝ→ E)(i:α) := F (S.pick i) (S.t i)
lemma ageB (hp:liveP S η): Latch.Lease true true S.toScale (sendT S ( Lives.gather M η n )) (fun i=> (S.length i)^(-(4:ℤ))):= nameD ( Emit.Host.host ( Dock.gang ( M.bulkOK n ) ) ) (η:=η∘ S.pick ) S.slot hp
lemma ageM {p q:CostsM G}{K:Blue G}{b:ℤ} (hp: liveP S η)(h:Dock.comet m b M.bulk p K q): Latch.Lease false false S.toScale (sendT S ( letIn m η K n )) (fun i=> ( S.length i ) ^ ( - (m:ℤ) )):= nameD ( Emit.Host.host ( Dock.gang (h n) ) ) (η:=η∘ S.pick ) S.slot hp
local notation "S0"=> S.toScale
local notation "X1"=> ( fun _ : I=> lineB G )
local notation "X0"=> ( fun _ : I=>lineA G )
abbrev TrueT (S:Home α I): α→ℝ:= fun i=> (S.length i)⁻¹
lemma true_nn (S:Home α I) : nn (TrueT S):= fun _=> inv_nonneg.mpr ( (S.pos _).le)
lemma capeA (S:Home α I)(G:Gauge): Sheet S.toScale 1 ( fun i=>lineA G (S.t i) ):= cost_D S.slot
lemma capeB (S:Home α I)(G:Gauge): Sheet S.toScale (TrueT S) ( fun i=>lineB G (S.t i) ):= edgeT _ S.slot shapeB O.Ward.rB
abbrev taxi (S: Home α I)(F:Glade G I)(a:α→ℝ)(n:ℕ) : Prop:= Well S.toScale (sendT S F) a n
abbrev totalT (S:Home α I)(F:Glade G I)(a:α→ℝ) (b:Bool): Prop:= FormP S.toScale (sendT S F) a b
lemma taxi_cycle (hp: Warm F false)(ht:taxi S F x (n+2))(he:nn x): taxi S ((both G I).P F) x n := by change taxi S ( Rcy X0 F ) x n; rw [spine hp realityA ]; exact (one_mul x) ▸ ht.cycle_q he (capeA S G) (fun _=>zero_le_one)
lemma taxi_B (hp:Warm F false)(ht:taxi S F x (n+2))(he:nn x) : taxi S (Rcy X1 F) (TrueT S*x) n:= by rw [spine hp realityB ]; exact ht.cycle_q he ( capeB S G ) (true_nn _)
lemma canA (hp:liveP S η)(he:totalT S F x true)(hv:nn x): totalT S ((both G I).X ( Lives.gather M η n ) F) x false:= by
    apply FormP.stays ( branch_q ( U:=fun i=> lineA G (S.t i) ) ( ageB hp ) he (fun i j=>Latch.polar ( capeA S G i j )) (fun _=>zero_le_one) (fun _=>length_p ..) hv ); intro i; simp only [ positive,Pi.mul_apply, Pi.one_apply ]; exact le_of_eq (by field_simp [( S.pos i ).ne'])
lemma canB (hp:liveP S η)(he:totalT S F x true)(hv:nn x): totalT S ((both G I).C ( Lives.gather M η n ) F) (TrueT S*x) false:= by
    apply FormP.stays ( branch_q ( U:=fun i=> lineB G (S.t i) ) ( ageB hp ) he (fun i j=> Latch.polar (capeB S G i j )) (true_nn _ ) (fun _=> length_p ..) hv ); intro i; simp only [ TrueT,positive, Pi.mul_apply ]; exact le_of_eq (by field_simp [( S.pos i ).ne'])
variable {J:Type}
lemma at_sums (s:Finset J){X:J→ Glade G I}(he:∀ i∈s,totalT S ( X i ) a b)(hn:nn a): totalT S (∑ i∈s,X i) a b:= by classical induction s using Finset.induction_on with| empty=> rw [ Finset.sum_empty ]; exact FormP.unit hn| insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact FormP.plus ( he i (by simp) ) ( ih fun j hj=> he j (mem_insert_of_mem hj))
lemma triA (hp:liveP S η)(he:∀ i<n,totalT S (X i) x true)(hx:nn x): totalT S (pairW (both G I).X (Lives.gather M η) X n) x false := by
    rw [paired]; refine at_sums _ ?_ hx; intro i hi; by_cases h:i.1=0; · rw [ h,zero_B M,map_zero,LinearMap.zero_apply ]; exact FormP.unit hx
    exact canA hp (he i.2 (by obtain h':= mem_antidiagonal.mp hi; omega)) hx
lemma triB (hp:liveP S η)(he:∀ i<n,totalT S (X i) x true)(hx:nn x): totalT S (pairW (both G I).C (Lives.gather M η) X n) (TrueT S*x) false:= by
    rw [paired]; refine at_sums _ ?_ (joy (true_nn S) hx); intro i hi; by_cases h:i.1=0; · rw [ h,zero_B M,map_zero,LinearMap.zero_apply]; exact FormP.unit (joy (true_nn S) hx)
    exact canB hp (he i.2 (by obtain h':= mem_antidiagonal.mp hi; omega)) hx
lemma helm_size (h:liveP S η)(hx:Warm (X n) false)(hv:taxi S (X n) x (m+2))(hp:∀ i<n,totalT S (X i) x true)(he:nn x): taxi S ( helm M η X n ) x m:= Well.plus (taxi_cycle hx hv he) ( Well.cram ( triA h hp he ) (fun i=>Bool.noConfusion i) )
lemma nav_bill (hp:liveP S η)(he:Warm (X n) false)(hx:taxi S (X n) x 2)(ht:∀ i<n,totalT S ( X i ) x true)(hw:nn x): taxi S ( nav M η X n ) (TrueT S*x) 0 := by
    change taxi S (_+pairW (both G I).C (Lives.gather M η) X n) _ _; rw [promised,front G I,LinearMap.add_apply ]; refine Well.takeM ( Well.plus ( taxi_B he hx hw ) ( Well.cram ( triB (M:=M) hp ht hw ) (fun i=>Bool.noConfusion i) )) ?_; intro i w hz; rw [ List.length_eq_zero_iff.mp hz]; unfold sendT; simp only [Pi.add_apply]; rw [ show Lives.Z G I ( X n ) ( S.pick i ) ( S.t i ) []=0 from q0 _,zero_add ]
end YM.FVA2.O.Rough
