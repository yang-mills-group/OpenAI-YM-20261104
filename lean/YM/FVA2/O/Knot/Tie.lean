import YM.FVA2.O.Knot.Banks
/-!
# Real-scale integrations between any two finite points.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Knot
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve Vane
open scoped Topology ContDiff Interval
variable {J I:Type}{G:Gauge}{k:ℤ}{S:Scale I}{η b:I→ℝ}{F H:Glade G I}{X:T ( Glade G I )}
def tieQ (b:I→ℝ)(F:Glade G I): Glade G I:= fun i t l=> ∫ s in (b i)..t, F i s l
@[simp] lemma tie_begin (b:I→ℝ)(F:Glade G I)(i:I): tieQ b F i ( b i )=0:= by funext l; simp [tieQ]
lemma tie_v (h:Warm F false): Velocity (tieQ b F) F:= by
    intro i t l; obtain hx:= h.walk i l (fun i=>Bool.noConfusion i); exact intervalIntegral.integral_hasDerivAt_right (hx.intervalIntegrable ..) (hx.stronglyMeasurableAtFilter ..) hx.continuousAt
lemma warm_tie (h:Warm F false): Warm (tieQ b F) false:= by
    constructor; · intro i t ht E _ _ w hw _; apply factorS (S:=single (camp t)) (fun _=>True) _ _ ?_ w trivial hw; intro E _ _ _ v hv hz; obtain hp:= Gym.cafe_p ( booking h i v ) ( fun p=> h.walk i (sail v p) (fun x=>Bool.noConfusion x)) ( b i ); exact ( hp.basic t ht ).raise (Cost.of_le fun i p _=>show 1≤( single ( camp t ) ).length i^pitch v*1 from by simp [Job.cw] ) -- factor args
    exact fun i l _=> continuous_iff_continuousAt.mpr fun _=> (tie_v (b:=b) h _ _ l).continuousAt
lemma perf_s (h:Diversity F k): Diversity (tieQ b F) k:= by intro i t l hx; unfold tieQ; simp_rw [ h i _ l hx ]; exact intervalIntegral.integral_zero
lemma Tie_t (h:Bank F k): Bank (tieQ b F) k:= by
    obtain ⟨k',hk⟩:=h.heat; refine ⟨ warm_tie h.cross,⟨ _,perf_s hk ⟩,fun i t=>?_⟩; unfold tieQ intervalIntegral; let H(a b:ℝ):=fun l=>∫ r in Set.Ioc a b,F i r l; have ht(a b:ℝ): Solid false ( H a b ) k:= intSolid _ (fun w=> ( h.cross.walk i w (fun x=>Bool.noConfusion x) |>.intervalIntegrable a b ).1 ) (h.tone i); exact (ht _ _).sub (ht _ _)
lemma tie_add (h:Warm F false)(ht: Warm H false): tieQ b (F+H)= tieQ b F + tieQ b H:= funext fun i=> funext fun _=> funext fun l=> intervalIntegral.integral_add ( h.walk i l (fun x=>Bool.noConfusion x)|>.intervalIntegrable .. ) (ht.walk i l (fun x=>Bool.noConfusion x)|>.intervalIntegrable ..)
lemma tie_sum (s:Finset J){f:J→Glade G I}(h:∀ i∈s,Warm (f i) false): tieQ b (∑ i∈s,f i)=∑ i∈s,tieQ b (f i):= by funext i t l; unfold tieQ; simp_rw [Finset.sum_apply]; exact intervalIntegral.integral_finsetSum fun j hj=>( h j hj|>.walk i l (fun x=>Bool.noConfusion x)).intervalIntegrable ..
def seatB (b:I→ℝ)(F:Glade G I): Glade G I:= fun i _=> F i ( b i )
lemma freeze_d (h:Diversity F k): Diversity ( seatB b F ) k:=fun _ _=> h _ _
lemma bank_at (h:Bank F k): Bank ( seatB b F ) k:= by
    obtain ⟨k,hk⟩:=h.heat; refine ⟨ ⟨fun i t ht E _ _ w hw hz=>?_ ,fun _ _ _=>continuous_const⟩,⟨ k,freeze_d hk ⟩,fun _ _=> h.tone _ _⟩; exact (Job.comfort (J:=camp t) h.cross i (b i) w hw).raise (Cost.of_le fun p x _=> show 1 ≤ (Job.single _).length p ^ pitch w*1 by simp [Job.cw] ) -- input name hF.b? 
end YM.FVA2.O.Knot
