import YM.FVA2.O.Seam.Finish
/-!
# Scalar evaluations on the full MS side after projection

Take the `blade` at positive infinite log-scale. Prove the relation
with precisely `tour`, and behavior under the `Fiscal` convolution
that includes mixing with the possibly nonzero positive-order coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse Knot
open scoped Topology ContDiff Interval
variable { I W J : Type }{G:Gauge}{ F H X:T ( Glade G I )}{ B: Deck G }{K:Booked B}{M:MS_Data G K}{P:Geo I}
variable {u:ℤ} {n k d:ℕ}{ a:T ( I→ℝ )}{b:I→ℝ}
abbrev feasts (v:T ( I→ℂ )) (p:T ( I→ℝ )): T ( I→ℂ ):= fun k i=>∑ j∈ Finset.range (k+1), ( p j i :ℂ ) * v (k-j) i
abbrev billH (X:T ( Glade G I )): T ( I→ ℂ ) := fun i=> blade ( X i )
abbrev Fiscal (p:Details B I k)(v:Counter B k→ T ( I→ℂ )): T ( I→ℂ ) := ∑ i: Counter B k, feasts (v i) (p i)
lemma read_two (h:Response X M P.η u)(he: Response F M P.η u): billH (X+F) = billH X+billH F:= funext fun i=> funext fun k=> Tendsto.limUnder_eq ( (total_peak h k i).add (total_peak he k i) )
lemma read_B (h:Response F M P.η u): billH (Hue.seat b F) = fun n i=> (b i:ℂ)* billH F n i:= funext fun n=> funext fun k=> Tendsto.limUnder_eq (( total_peak h k n ).const_mul _ )
lemma read_z : billH (0: T ( Glade G I ) )=0:= funext fun _=> funext fun _=> Filter.Tendsto.limUnder_eq ( f:= atTop ) (g:=fun (_:ℝ)=> (0:ℂ)) (x:= (0:ℂ) ) tendsto_const_nhds
lemma read_sum (s:Finset J){F:J→ T ( Glade G I )}(hp: ∀ i∈s,Response ( F i ) M P.η u): billH (∑ i∈s,F i)=∑ i∈s,billH ( F i ):= by
    classical induction s using Finset.induction_on with
    | empty=> rw [ Finset.sum_empty, Finset.sum_empty,read_z ]
    | insert i s hi ih=>
        have h(j)(h:j∈s):= hp j (mem_insert_of_mem h); rw [ Finset.sum_insert hi, Finset.sum_insert hi, read_two ( hp _ (mem_insert_self ..) ) ( Response.all_fin s h ), ih h ]
lemma read_fo (h:Response F M P.η u): billH (entrance a F)= feasts (billH F) a:= by
    funext k i; rw [ show billH (entrance a F) k=billH ( hall a F k ) k from congr_arg Vane.blade ( hereΛ ( le_refl k ) ).symm ]; rw [hall, read_sum ( Finset.range ( k+1 ) ) (F:=fun i=>hold0 i (Hue.seat (a i) F)) (fun i _=> shift_Response ( h.scale (a i) ) ), Finset.sum_apply, Finset.sum_apply ]; exact Finset.sum_congr rfl fun j hj=> by obtain he:j≤k:= Nat.le_of_lt_succ ( Finset.mem_range.mp hj ); rw [billH,hx_holder he,show ∀ i n, Vane.blade (Hue.seat ( a j ) F n) i=_ from fun i n=> congr_fun ( congr_fun ( read_B ( b:=a j ) h ) n ) i]
variable { X' : Counter B k→ T ( Glade G I )}{r:Details B I k}{ s:Counter B k → T ( I →ℂ )}
lemma read_F (h:∀ i, Certified ( X' i ) M P.η u)(he:∀ i,billH ( X' i )=s i): billH (FrameZ r X')=Fiscal r s:= by
    rw [FrameZ,read_sum _ (F:= fun i=> entrance (r i) ( X' i ) ) (fun i _=>( entrance_C _ ( h i ) ).1) ]; exact Finset.sum_congr rfl (fun i _=> by rw [ read_fo (h i|>.1), he i ] )
variable [LinearOrder W]{ s:Finset W}{x: Position W I}{R:W→ Label B}
abbrev glyph (P: Geo I)(M:MS_Data G K)(x:Position W I)(R:W→ Label B)(s:Finset W): T ( I→ℂ ) := fun n i=> Dial.tour M R (P.η i) ( Dial.pointI x i ) s n
lemma clocked (hp:separable x): billH ( thicket P M x R s )= glyph P M x R s:= funext fun n=> funext fun i=> blade_t hp ( serves hp ) i n
end YM.FVA2.O.Seam
