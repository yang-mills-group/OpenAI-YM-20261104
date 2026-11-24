import YM.MS.Latch.Voice
/-!
# Transport of integrated cost. Compatible compact-left & infinite-left.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I J E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{b c:Bool}{S:Scale I}{k:ℕ}{K:Belt I}
    {F H X:Moments I (Law G)}{T ε:ℝ}{A B:K.time→ℝ}
-- caps via direct Lease.Meas. Income assumption for p^d.A.B.P. unchanged used past.C.K. `Walk` membership.[
def Break (b c:Bool)(P:Belt I)(A B:P.time→ℝ): Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E],∀ w: Wire (BH G) E QP,Course b w→fig c w.length→∃ ε:ℝ,0<ε∧ Slide P ε (Qbud w P.price A) (Qbud w P.price B) -- G not exposed: use explicit G
lemma Dance {Y}(h: Walk K)(hu:Break (G:=G) b c K A B)(hp:Here b c K H A)(he:Lease b c K.price Y B)(hv:Stroll b H)(hx: Dash b K F H Y): Here b c K F B:= by
    intro E _ _ w hw hK; refine factorS (fig c) K.price (plug F) B (b:=b) (fun E _ _ _ w hw hK=> ?_) w hK hw;
    obtain ⟨a,ha,hL⟩:= hu E w hK hw; let f i t (p:E):= H i t (sail w p); unfold Cape; rw [show Chart (plug F) w = (fun i p=> Y i (sail w p)+ past K f i p ) from funext fun i=> funext fun p=>hx i _ (sail_course p hK) ]; exact Costs.add ( he E w hK hw ) ( Belt.pastCost (f:=f) (hp E w hK hw) h hL ha (fun i p=> (hv _ _ (sail_course p hK)).aestronglyMeasurable) )
lemma Dint (h:Walk K)(hu:Break (G:=G) b c K A B)(hx: Stroll b F)(hP: Here b c K F A)(p:K.time)(l:Legs (Lane4 G))(hp:Course b l)(he:fig c l.length): Integrable (fun i=> F p.1 i l) (Mu p):= by
   let v:=ray l; have hv:=ray_course hp; have hK : fig c (ray l).length:=by simpa using he
   obtain ⟨ε,hε,hF⟩:= hu ℝ ( ray l ) hv hK; obtain ht: Majorant ( Mu p ) (fun t u=> F p.1 t (sail v u)) := atMonth ( f:=fun i t u=> F i t (sail v u)) ( hP ℝ _ hv hK ) h hF hε (fun i u=> (hx i.1 _ ( sail_course u hv )).aestronglyMeasurable) p; simpa only [ v, ray_sail ] using ht.values 1
lemma constant_at {F:I→Law G}{A:I→ℝ}(H:Lease b c S F A)(i:I)(Z:Scale J)(hp:∀ j,1≤Z.length j)(w:Wire ( BH G ) E QP)(hw:Course b w)(hx:fig c w.length): Bound Z (fun _=> fieldVal (F i) w) 1:= by
    let P:=fun _:J=>i; have hS: Bus Z S P:= by
         refine ⟨⟨_,S.basic_pos i,0,fun _=>?_⟩, _, S.pos i,fun j=>?_⟩; · simp [ P ];
         exact le_mul_of_one_le_right (S.pos i|>.le) (hp j)
    apply ticket (P:=P) hS (H E w hw hx) ?_ (fun i=>zero_le_one); let v:= Qbud w S A i; refine ⟨max v 1,lt_max_of_lt_right zero_lt_one,0,fun c=>?_⟩; simp only [P,Function.comp_apply,pow_zero,mul_one]; exact le_max_left ..
-- dash add etc.Time primitives
abbrev train (b:Bool)(F:Moments I (Law G)): Prop:= ∀ i x (l:Legs (Lane4 G)),Course b l→ IntegrableOn (fun t=> F i t l) (Set.Iic x)
def river (F:Moments I (Law G)): Moments I (Law G):= fun i t l=>∫ s in Set.Iic t,F i s l
lemma swamp (h:train b F) (i:I)(x y:ℝ) {v:Legs (Lane4 G)} (he:Course b v): river F i x v = river F i y v + ∫ s in y..x,F i s v:= by apply eq_add_of_sub_eq'; exact intervalIntegral.integral_Iic_sub_Iic ( h i y v he ) ( h i x v he ) -- name order
lemma swampT (ht:train b F)(hf: Stroll b F): Stroll b (river F):= by
    intro i v he; rw [continuous_iff_continuousAt]; intro t; rw [show (fun t:ℝ=>river F i t v)=(fun t:ℝ=>_) from funext fun t=>swamp ht i t 0 he]; exact ( HasDerivAt.const_add _ ( hfun (hf i v he) t ) ).continuousAt
lemma cap0 (R:ℝ)(p:camp R): (CK R).stream p=Set.Icc (-R) (tstart p):= by
    have hp : (-R≤tstart p)∧ ( tstart p≤R ) := p.2.property; ext; change (_∈ Set.Icc _ _ ∧ _∈ Set.Iic _) ↔ _; simp only [Set.mem_Iic,Set.mem_Icc]; grind
lemma pathM (R:ℝ)(p:camp R):0≤δf p p:= by simp [δf]
lemma stripe (R:ℝ)(_h:0 ≤ R):Slide (CK R) 1 1 1:= by
   refine ⟨fun _=>zero_le_one, Real.exp (2*R),Real.exp_pos _, fun p q hp _=>?_ ⟩; have hs :(-R≤ tstart q)∧ (tstart p≤R):= ⟨q.2.property.1,p.2.property.2⟩; simp only [Pi.one_apply,mul_one,neg_one_mul,← Real.exp_add]; refine Real.one_le_exp ?_; unfold δf; change 0 ≤ 2*R + -( tstart p-tstart q ); linarith [hs.1,hs.2]
end YM.MS.Latch.Job
