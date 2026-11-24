import YM.MS.SpaceOut.Entrance
/-!
# Occupant, tower follows from single Taylor storage. BIG geometry path permit η inputs. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista Logarithm LogTime Program Wilsonian Wind Knobs
open scoped Topology ContDiff Interval
variable {G:Gauge}{W E I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 {S:Scale I}{M:Visa I} {F: I→Law G}{L:I→Side}{ H:Wind.Pack G}{X:Rake.Site G I}
    {Y:Wind.Dec G}{B:High.Recount G}{η v x:I→ℝ}{b c:Bool}
lemma hint ( w:Wire ( BH G ) E QP )(h:∀ i,1≤ S.length i): Bound S ( fun _ p=>hook lace (sail w p) ) 1:= by
    induction w with| nil=> exact Costs.scalar (p:=fun _=>(1:ℂ)) ( Cost.of_le fun _ _ _=> by simp )| cons i l ih=>
       rcases i with ⟨i,L⟩; let P:= offset i.1; have he(p:E): lace (i,L p)= Tone.bill P ( - L p ):= Tone.rights ..; have ht: paid S (fun _=>‖P‖) S.length:= ⟨ ‖P‖+1,(by positivity),0,fun i=> by rw [pow_zero,mul_one]; apply le_trans _ (le_mul_of_one_le_right ( show 0≤‖P‖+1 by positivity ) (h i )); linarith ⟩ -- shadow
       simp only [ hook,List.map_cons, sail_cons,List.prod_cons,he ]; exact pulse_bill (-L) ih ( paid_at ht (fun i=> S.pos i|>.le)) -- `Norm param ℓ.C.`
lemma owns_money (h:∀ i,1≤ S.length i)(hp: Lease b c S F x): Lease b c S (fun i=> sleeve lace ( F i )) x:= fun E _ _ w hx hK=> by unfold Cape; convert ( Costs.mul ( hint w h ) ( hp E w hx hK )) using 1; rfl; ext; simp
lemma anchorC (v:I→Prop)(h:Lease b c ( leftS S v ) (fun i=> F i.1) (fun i=> x i.1))(hp:Lease b c ( leftS S (fun i=>¬v i) ) (fun i=> F i.1 ) (fun i=>x i.1)): Lease b c S F x:= fun E _ _ w hW ht=> meet_cost (v:=v) _ S.full _ _ ( h E w hW ht ) ( hp E w hW ht ) -- cost_i λ projection
-- large sector.
lemma sky_h (h:∀ i,1≤v i)(hp:∀ i,S.length i=v i)(he:∀ i,(1+|η i|)*(1+log (v i))≤S.basic i)(k:ℕ)(ht:∀ r,fig true r→ Trust true 4 (col Y k) ( B k ) r): Lease true true S (fun i=> Y k (η i) (v i)) (fun i=>S.length i ^ ( -(4:ℤ) )) := by
    let Φ(i:I):= meet.choose ( η i ) (log (v i)) (show log (v i)∈ Set.Ici 0 from log_nonneg ( h i )); let V:=meet.primary; have hz (i:I) :0<v i:= lt_of_lt_of_le zero_lt_one ( h i ); have hu i: V.length (Φ i)=v i:= exp_log ( hz i ); have hh: Bus S V Φ:= ⟨ ⟨1,zero_lt_one,1,fun i=> by rw [pow_one,one_mul,Pi.one_apply,mul_one]; exact he i ⟩,1,zero_lt_one,fun i=>by rw [hu,hp,one_mul] ⟩; intro E _ _ w hW hr;
    have he(w':Legs ( Lane4 G ))(i:I): Y k (η i) (v i) w'=lane meet (col Y k) (Φ i) w':= by change _= Y k (η i) (exp (log (v i))) w' ; rw [ exp_log (hz i) ];
    let W:=Plane.Chart (lane meet (col Y k)) w; unfold Cape Plane.Chart; simp_rw [ he ]; apply Job.ticket hh ( ht w.length hr E w hW rfl |>.1 ) (paidMono (fun i=>?_)) ( pos_nn _ (fun i=> length_p .. ) _ ); -- implicit Z=head
    dsimp only [Function.comp]; change V.length (Φ i)^ ( pitch w-_ )≤ _; rw [ show pitch w-(4:ℤ)=pitch w+ ( -(4:ℤ) ) from (by omega), zpow_add₀ (V.pos _|>.ne'), hu, hp]
local notation "Ω"=> unbounded M
abbrev warmV (η:I→ℝ)(M:Visa I): Prop:= ∀ i,1+|η i|≤M.bank i
lemma sky_budget {p:Team}(hf:warmV η M)(hV:PC G p Y)(he: Fixed ( col Y ) B true 4 1): Vista.bulk Ω ( Orbit.Scope G Y η ):= by
    intro i ht; let S:=(Ω).price; let T:= (Ω).time; let U(k:T):= τ ( tstart k ); let y(k:T):= η k.1; let F(k:T):= Y i (y k) (U k); let r(k:T):= S.length k^ ( -(4:ℤ)); change Lease true true S (fun i=>sleeve lace ( F i )) r; apply owns_money  (fun i=> lamp_l _) ; -- split
    let v(k:T): Prop:= 1≤U k; have hu(k:T):0≤ tstart k:= k.2.property; have hr(k:T): S.length k = max 1 ( U k ) := rfl; have hy(k:T): (1+|y k|)*(1+tstart k) ≤ S.basic k:= by change _≤ wallet M _ _; unfold wallet; rw [ abs_of_nonneg (hu k) ]; apply mul_le_mul_of_nonneg_right (hf k.1) (by linarith [hu k])
    apply anchorC v;
    · refine sky_h (v:=fun i:Subtype v=>U i.1) (η:=y∘Subtype.val) (fun i=> i.2) (fun i=>?_) (fun i=>?_) i (he i ht); · change S.length i.val= U i.val; rw [hr, max_eq_right i.2]
      apply le_trans _ (hy i.1); dsimp only [ comp_apply ]; gcongr; 
      apply Real.exp_le_exp.mp; rw [ exp_log (by exact lt_of_lt_of_le zero_lt_one i.2) ]; unfold U τ; linarith
    let C (k:T):Prop:= ¬v k; have hv(t:Subtype C): ( leftS S C ).length t=1:= (hr t.1).trans ( max_eq_left ( le_of_not_ge t.2 ) ); rw [ show (fun i:Subtype C=>r i.1)=(1:Subtype C→ℝ) from funext fun i=>by change ( leftS S C ).length i ^ ( -(4:ℤ) )=_; rw [ hv, one_zpow ]; rfl ]; refine maximumT ( a:=fun i:Subtype C=> U i.1 ) ( T:=1) (fun i=>?_ ) hv _ ( hV.owes i ) (η:=fun i=> y i.1) ?_; · rw [ Real.norm_of_nonneg ( show 0 ≤ U i.1 from sub_nonneg.mpr (Real.one_le_exp (hu i.1)) ) ]; exact le_of_not_ge i.2
    exact ⟨ 1,zero_lt_one,1,fun i=> by rw [pow_one,one_mul,Pi.one_apply,mul_one]; apply le_trans _ ( hy i.val ); dsimp only [y]; rw [norm_eq_abs]; nlinarith [hu i.val,abs_nonneg (η i.val.1)] ⟩
end YM.MS.SpaceOut
