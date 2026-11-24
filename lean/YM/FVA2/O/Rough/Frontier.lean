import YM.FVA2.O.Rough.Vault
/-!
# Upper evolution from the matching region

For positive ranks (`k+1`, number of legs). `fountain`: transfer estimates
(no propagating of additional momentum-derivative estimates here). Used for
the uniform error bound on `blade` in `Rough/Level`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Rough
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land
open scoped Topology ContDiff Interval
variable {E F I:Type} [ NormedAddCommGroup E ][NormedSpace ℝ E] {R:IntervalFamily I}
variable {G:Gauge}{X Y:T (Glade G I)} -- rename interval Z
variable {a η:I→ℝ}{n j k:ℕ}{b:ℤ}{u:ℝ} {B:Deck G}{K:Booked B}{M:MS_Data G K} {F H:Glade G I}
def face (R:IntervalFamily I) : Home R.Inst I :={
    toScale:=R.primary
    pick:= index
    t:= IntervalFamily.t
    slot _:=rfl }
def initial (R:IntervalFamily I): Home I I:={
    toScale:= R.dawn
    pick:=id
    t:= R.beg
    slot _:=rfl }
abbrev peak (R:IntervalFamily I)(t:ℝ)(a:I→ℝ)(u:R.Inst) : ℝ:= a ( index u ) * exp (-t * (IntervalFamily.t u - R.beg ( index u )))
abbrev wake (R:IntervalFamily I)(n:ℝ)(a:I→ℝ):= fun i=> a i * exp (n*R.beg i)
lemma pays_p (hp:nn a): nn ( peak R u a ):= fun _=> mul_nonneg (hp _) (exp_pos _|>.le)
lemma wake_nn (hp:nn a): nn (wake R u a ):= fun _=> mul_nonneg (hp _) (exp_pos _|>.le)
lemma encode (i:R.Inst)(w:ℤ): R.primary.length i^w*peak R u a i=pays ( wake R u a ) ((w:ℝ)-u) i:= by
    unfold peak pays wake; rw [ show -(u:ℝ)*(t i- R.beg (index i))= u*R.beg (index i)-u*t i from (by ring), Real.exp_sub, sub_mul,Real.exp_sub ]; rw [ ← Real.rpow_intCast, ← Real.exp_mul ]; field_simp
lemma encode0 (i:I)(j:ℤ): R.dawn.length i^j*a i=wake R u a i*exp (((j:ℝ)-u)*R.beg i) := by have he:= encode ( u:=u ) ( a:= a ) ( R.start i ) j; rw [show peak R u a ( start R i )= a i from (by simp only [peak,start,index,t,sub_self,mul_zero,exp_zero,mul_one])] at he; exact he
lemma captive (hc:Diversity F b)(he:b<j)(hp:nn a): taxi ( face R ) F ( peak R u a ) j := Well.takeM (Well.unit (pays_p hp)) (fun i w hw=> hc _ _ _ (by omega))
-- use JetBound.forward at j=0 
lemma fountain (h: Warm F false)(ht: Warm H false)(hd:Velocity F H)(ha:nn a)(hp: taxi ( face R ) H ( peak R eps_gain a ) (k+1))(hx:taxi (initial R) F a (k+1)): taxi (face R) F ( peak R eps_gain a ) ( k+1 ):= by
    intro E _ _ w hw; specialize hx E w hw; specialize hp E w hw; have hz': R.dawn.full.Part R.dawn ( fun i=> (Tune.canvas F w) i ( R.beg i ) ) ( fun i _=> (wake R eps_gain a) i * exp (( (pitch w:ℝ)-eps_gain)*R.beg i) ) 0 := by refine Cost.Part.start.mpr ?_; exact Cost.Le.trans hx ( Cost.of_le fun i p _=> (encode0 i (pitch w)).le );
    have hs : R.primary.full.Part R.primary ( here ( Tune.canvas H w ) ) ( fun i _=> pays (wake R eps_gain a ) (( pitch w:ℝ ) - eps_gain ) i ) 0:= Cost.Part.start.mpr ( Cost.Le.trans hp ( Cost.of_le fun i p _=> (encode i (pitch w) ).le) ) -- `.trans` resolution
    have hW:1≤ pitch w:= by obtain hh:= length_pay (G:=G) (sail w 0); rw [ sail_dim, sail_len,hw ] at hh; unfold pitch; omega
    refine Cost.Le.trans ( Cost.Part.start.mp (R.forward (wake_nn ha) (Track_now R h ht hd w 0) hs hz' ?_ )) (Cost.of_le fun i p _=> ( encode i (pitch w)).symm.le ); have hw:1 ≤ (pitch w:ℝ):= (by exact_mod_cast hW); have ht:= High.s_gain; rw [Nat.cast_zero,add_zero]; linarith
end YM.FVA2.O.Rough
