import YM.FVA2.O.Read.Diode
/-!
# Scale conversion of exterior fields at length T=exp(t)

This conversion uses the prescribed exterior fields. Auxiliary cover-filter history estimates are separate.
`LongT` reads on the far profile before smearing; the T^d factor for exterior labels
and transformation by the running frame included. `routeY` identifies the corresponding
unit-scale computation in the running coupling; only remaining overall factor is T to minus
the weight of the central field. These results concern **formal continuum** coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable {G:Gauge}{ I: Type }{n m k d:ℕ }{t:ℝ}{ H:ℝ→ Frames G }{T U:Cast G}{ V:Arenas G }{A:Album G}
variable {r:ℝ→ Cn }{ u:Scan G n }{ v:Scan G m }{ x:Points n }{ y:Points m }
-- time portfolio
lemma step_seats (T:Frames G)(p:Cn)(h:Rooted p)(i j:Grade G d): (seats T d i j).subst p= seats ( fun i=> Reg.Point.stepV p ( T i ) ) d i j:= by
    ext k; rw [← Constants.actual_subst _ _ h ]; simp_rw [seats, Reg.Point.stepV, coeff_mk,rules, LinearMap.sum_apply,map_sum,LinearMap.smul_apply,paygrade,_root_.map_smul ]
variable (h:Law V r H)
include h
lemma reverse_t (t:ℝ): (r t).subst (r (-t))= PowerSeries.X:= Eq.trans (h.additive (-t) t|>.1.symm) (by rw [neg_add_cancel,h.ground.1])
lemma frames_t (t:ℝ)(u:ℕ): mirror ( H (-t) u )= Reg.Point.stepV (r (-t)) ( H t u ):= by apply Base.alone ( h.paid .. ); obtain hV:= (h.additive (-t) t).2 u; rw [ neg_add_cancel,h.ground.2,Scale.old_g t ( H (-t) u ) ( h.ready _ _ ) ] at hV; exact hV.symm
lemma back (t:ℝ)(u:ℕ): H (-t) u = Reg.Point.stepV ( r (-t) ) ( mirror ( H t u ) ):= by rw [ Frame.step_mirror ( H t u ) ( h.paid .. ) ( r (-t) ) ( (h.led _).start ) ( (h.led _).real ),← frames_t h,( h.paid .. ).twice ] -- name conflict Frame
lemma kfe (b j:Grade G k) : Astro H (-t) k b j= (Night H t k b j).subst (r (-t)):= by rw [step_seats ( replay ( H t ) ) ( r (-t) ) (( h.led _ ).start )]; change seats ( H (-t) ) _ _ _=_; exact congr_arg (fun T=> seats T k b j) (funext ( back h t ))
lemma khform (b j:Grade G k): Night H (-t) k b j=( Astro H t k b j ).subst ( r ( -t ) ) := Eq.trans (congr_arg ( fun T=> seats T k b j ) (funext ( frames_t h t ))) ( step_seats ( H t ) ( r (-t) ) (( h.led _ ).start ) b j ).symm -- binder
omit h
local notation "V0"=> install V
local notation "Vt"=> TuneQ
abbrev LensT (H:ℝ→Frames G)(t:ℝ)(Y:Points m→ Scan G m→ Cn)(x:Points m)(v: Scan G m):= Acres (-t) (totalG v) * concert (Astro H (-t)) v ( Y ( squeeze (-t) x ) )
abbrev LongT (H:ℝ→Frames G) (A:Album G)(t:ℝ)(b:Q G)(y:Points m)(v:Scan G m):= LensT H t (fun y w=> lonelyG A y b w) y v
abbrev ShowT (H:ℝ→Frames G)(A:Album G)(t:ℝ)(x:Points n)(u:Scan G n)(y: Points m)(v:Scan G m):= LensT H t (fun y w=> party A x y u w) y v
abbrev ProgramY (H:ℝ→ Frames G)(r:ℝ→Cn)(V:Arenas G)(t:ℝ)(b:Q G)(y:Points m)(v:Scan G m):= concert (Night H (-t)) (Single b ) (fun c=> party ( tune ( r (-t) ) ( install V ) ) (0:Points 1) y c v)
lemma Acres_joy (a b:ℕ): Acres t (a+b)= Acres t a*Acres t b:= by unfold Acres; rw [← map_mul, Score.fee,Nat.cast_add,mul_add,Real.exp_add, Complex.ofReal_mul ]; -- defeq
-- move exponent across concert of the same grade
lemma price_deg (a:ℕ)(T:Cast G)(F:Scan G n→ Cn): concert T u ( fun p=> Acres t (a+totalG p)* F p )= Acres t ( a+totalG u ) * concert T u F:= by rw [ concert_sum_r ]; unfold concert; exact rfl
include h
lemma townParty (he:Regular V) (b:Q G) (y: Points m)(v:Scan G m) : lonelyG V0 ( squeeze (-t) y ) b v= Acres t ( heft b+totalG v ) * concert (Night H (-t)) (Single b) (fun w=> concert (Night H (-t)) v (party ( tune ( r (-t) ) ( install V ) ) (0:Points 1) y w) ):= by
    have H0: squeeze (-t) (0:Points 1)=0:= smul_zero _;
    obtain ht:= step_party h he (-t) (0:Points 1) ( Single b ) ( squeeze (-t) y ) v; rw [ H0,neg_neg,Project.before,totalOne,Stellar,party_h ] at ht; exact ht
lemma routeY (he:Regular V)(b:Q G): LongT H V0 t b y v= Acres t (heft b) * ProgramY H r V t b y v:= by
    unfold LongT LensT; simp_rw [ townParty h he ]; rw [ price_deg ]; unfold ProgramY; -- concert swap by lemma helper
    let F (u:Scan G 1)(v:Scan G m):= party ( tune ( r ( -t ) ) V0 ) (0:Points 1) y u v; let T:= Night H (-t); let U:= Astro H (-t); have hp : U*T=1:= spin_v ( slot h _ );
    have he' (u:Scan G 1): concert U v ( fun w=> concert T w ( F u ) )=F u v:= by rw [ ← concerto,hp,soloist ];
    rw [ ← mul_assoc, Acres_joy, mul_left_comm,mul_comm ( Acres (-t) _ ) ( Acres t (totalG v) ), acres_b,mul_one ]; congr 1; rw [concert_k U T ( fun (w:Scan G m) (u:Scan G 1 )=> concert T w ( F u ) ) ]; simp_rw [he']; rfl
end YM.FVA2.O.Read
