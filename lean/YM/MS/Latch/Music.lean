import YM.MS.Latch.Bin
/-!
# Comfort station. fixed origin instantaneous spectral properties for global past solvers -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Belt
open scoped Topology ContDiff Interval
variable {I J E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] {S:Scale I} {Z: Scale J}{P:I→J}
 {G:Gauge}{b c:Bool}{A Z':Belt I}{R:ℝ}{a: I→ℝ}
-- Compact windows attached to one config
def single (I:Type): Scale I:= { length:=1,pos:=fun _=>zero_lt_one,basic:=1,one_le:=fun _=>le_rfl }
def CK (T:ℝ): Belt Unit:={ slot _:=Set.Icc (-T) T,price:= single _,meas:=fun _=>measurableSet_Icc }
lemma CKW (T:ℝ): Walk (CK T):= ⟨fun p q _ _=>le_rfl, fun p q _ he=> by change 1≤1*(1+δf p q); simp [he]⟩
abbrev camp (r:ℝ):=( CK r ).time
def tap (F:Moments I E)(i:I)(T:ℝ)(p:camp T):= F i p.2
lemma htT (p:camp R): ‖(p.2.val:ℝ)‖≤R:= abs_le.mpr p.2.property
lemma existsC (t:ℝ): t∈ Set.Icc ( - (‖t‖+1)) (‖t‖+1):= by obtain h:= abs_le.mp ( show |t|≤ ‖t‖+1 from by simp [norm_eq_abs]); exact h
omit [NormedSpace ℝ E] in
lemma tx (i:I)(p:E): (single I).full.cheap i p=1+‖p‖:= by simp [single,Scale.full,Scale.weight]
lemma cw (i:I): (single I).length i=1:= rfl
-- μ fixed with dust.Any.S.Ent.Candle.
structure Cohere (μ:Measure QP): Prop where
   wallet: ∃ d:ℕ,Integrable ( (single Unit).dust d () ) μ
lemma funds (J:Type) {μ:Measure QP}(he:Cohere μ):∃ d:ℕ, Mint (single J) (fun _=>μ) d ∧ glob (single J) (fun _=>μ) d:= by
   obtain ⟨d,h⟩:= he.wallet; let F (q:QP):=(single Unit).dust d () q; let v:=∫ p,F p∂μ; refine ⟨d,fun E _=> ⟨max v 1, lt_max_of_lt_right zero_lt_one,0,?_⟩,⟨fun _=>Eventually.of_forall fun _=>trivial, fun _=>?_⟩⟩; · intro i p hp; change v≤ _; simp [Snap.fee,cw]
   exact h
-- ancillary continuity for line convolutions
variable {F H X: Moments I (Law G)}{μf:I→Measure QP}{U V K: Moments I (Edge G)}
structure Warm (F:Moments I (Law G))(b: Bool): Prop where
    cost: ∀ i T,0≤ T→Lease b false ( single (camp T) ) ( tap F i T ) 1
    walk: Stroll b F
structure S0 (K:Moments I (Edge G)): Prop where
    span : ∀ i k j p, Continuous (fun q=> K i q k j p)
    cost : ∀ i T,0≤T→ CourseK (single (camp T)) 1 ( tap K i T )
structure BackF (K:Moments I (Edge G)): Prop where
    span : ∀ i k j p, Continuous (fun q=> K i q k j p)
    cost : ∀ i T,0≤ T→ Sheet (single (camp T)) 1 ( tap K i T )
lemma comfort (hF:Warm F b)(i:I)(t:ℝ)(w:Wire (BH G) E QP)(hw:Course b w): Bound (single J) (fun (_:J)=> fieldVal ( F i t ) w) 1:= by
   let T:=‖t‖+1; let P:camp T:= ⟨(),t,existsC t⟩; let q:J→camp T:= fun _=> P; have hS : Bus (single J) (single (camp T)) q:= ⟨paidMono (fun _=> le_rfl),1,zero_lt_one, by simp [single]⟩; apply ticket hS ( hF.cost i T (by unfold T; positivity) E w hw ( fun v=> Bool.noConfusion v )) ( paidMono fun i=>( by simp [ Function.comp_apply,cw] ) ) (fun i=> zero_le_one) -- unification
lemma walk_tree (hk:S0 K)(hx:Warm X true)(hy: Warm H b): Warm (fun i t=> tree parity (K i t) (X i t) ( H i t )) b:= by
   constructor
   · intro i T hT; convert trunks (hk.cost i T hT) ( Lease.highp (hx.cost i T hT)) (Lease.highp (hy.cost i T hT)) (fun _=>zero_le_one) (fun _=>zero_le_one) (fun _=>zero_le_one) using 1; rfl; ext k; simp [positive,cw]; -- maybe rfl
   intro i v hv; unfold tree; refine gath v _ (fun l r hV=>?_); unfold attaches; dsimp only; refine continuous_finsetSum _ (fun k _=> continuous_finsetSum _ (fun j _=>?_ )); simp_rw [neg_neg];
   exact Continuous.add ((hk.span ..).mul (( continuous_const.mul (hx.walk _ _ (fun _=>by simp)) ).mul (hy.walk _ _ (fun s=>by simp only [net_cons]; exact (split_net hV).trans (hv s)) ))) (( hk.span .. ).mul ( ( continuous_const.mul ( hx.walk _ _ (fun _=>by simp)) ).mul (hy.walk _ _ (fun s=>by simp only [net_cons]; exact (split_net hV).trans (hv s)) ))) -- inspect
where
 gath (v:Legs (Lane4 G))(K:ℝ→ Shared (Lane4 G) ℂ)(he:∀ l r,Split l r v→Continuous (fun x=> K x l r)): Continuous (fun x=> scatter (field Landau.parity) v ( K x )):= by induction v generalizing K with| nil=> exact he _ _ .nil| cons i l ih=> exact ih _ (fun l r hp=> (he _ _ hp.left).add ( continuous_const.mul (he _ _ hp.right)))
end YM.MS.Latch.Job
