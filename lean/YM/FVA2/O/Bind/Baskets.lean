import YM.FVA2.O.Enh.Care
/-!
# Reduce the FAR pricing horizon

`Basket_step`: improve to the sharp gap of one by using one more output weight.
Formal kernels with uniform power-log accounting. See `O/Enh/{Poker,Rain,Above}`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Bind
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh
variable { G:Gauge }{I:Type}{n m k i j d n':ℕ}{ v b c:ℝ }{ V:Arenas G }{B:ℝ→Frames G}{R:ℝ→Cn}{A:Album G}
variable { s:Set ( Points n )}{K:Set ( Points m )}{y:Points m}{f g:Fable G n}{a:Scan G n}{X:Scan G m}
local notation "A0"=> install V
abbrev wage (i:ℕ)(A:Album G)(y:Points m)(x: Scan G m)(p: Q G→ Cn): Cn:= Settle i (fun q=> p q * lonelyG A y q x)
lemma Lamp_step (p:Q G→ Cn): Lamp A (i+1) y X p= Lamp A i y X p+wage (i+1) A y X p:= Finset.sum_range_succ _ _
lemma lapK {x:Points n} : Basket A a X ( f x ) (i+1) x y=Basket A a X (f x) i x y - wage (i+1) A y X (f x):= by unfold Basket; rw [ Lamp_step ]; abel
lemma Basket_keeper (h:Fiasco A s k b d a f)(he:c≤b): Fiasco A s k c d a f:= fun m s p hx hp=> ChargeP.grow ( h m s p hx hp ) (by linarith)
lemma priceH (h:Law V R B)(hp: IsCompact K)(ht:K⊆Outside m)(hx:Regular V)(hO:Observed A0)(he:PlainF s f d n')(hw:k ≤ d): ChargeP n' ((k:ℝ)+(totalG X:ℝ)) (fun (i:s×K) t=> wage k A0 ( squeeze (-t) i.2.val ) X (f i.1.val)):= by
    unfold wage Settle; apply ChargeP.sum; intro j hj; apply ChargeP.times; · intro i hi; exact Rain.pull ( Rain.cash (he (own j) hw i hi) ( E:=ℂ ) ) Prod.fst
    exact ChargeP.pull ( Uniform.teeth_P h hx hp ht hO X (own j) n') Prod.snd
lemma Basket_step (h:Law V R B)(he:Regular V)(hx:Observed A0)(hV:PlainF s f (k+1) d)(hp:Fiasco A0 s (k+1) b d a f)(hv:0≤b): Fiasco A0 s k 1 d a f:= by
    intro m S v he' hS; obtain H:= hp m S v he' hS; have hr:= priceH ( k:=k+1 ) ( X:=v ) h he' hS he hx hV le_rfl; change ChargeP d _ _; have hz(c:Points n)(y:Points m): Basket A0 a v ( f c ) k c y= Basket A0 a v ( f c ) (k+1) c y+wage (k+1) A0 y v ( f c ) := by rw [lapK,sub_add_cancel]
    simp_rw [hz]; exact ChargeP.plus ( ChargeP.grow H ( by rw [ Nat.cast_add,Nat.cast_one ]; linarith ) ) ( hr.grow ( by push_cast; exact le_rfl ) ) -- `.grow` for RangeP?
lemma paths_F (ht:i≤d)(hv:j ≤ k)(h:PlainF s f d k): PlainF s f i j:= fun _ hx _ he=> h _ (hx.trans ht) _ (lt_of_lt_of_le he hv)
lemma watch (ht:i≤k)(h:Fiasco A s d b k a f): Fiasco A s d b i a f:= fun m S x hp hu=> ( h m S x hp hu ).move ht
lemma levels (h:Law V R B)(he:Regular V)(hx:Observed A0)(hp:PlainF s f d n')(hF:Fiasco A0 s d b n' a f)(hh:k≤d)(hb: 0 ≤ b)(hv:b≤1): Fiasco A0 s k b n' a f:= by
    induction hh using Nat.decreasingInduction with| self=> exact hF | of_succ i he' IH=> exact Basket_keeper ( Basket_step h he hx ( paths_F he' le_rfl hp ) IH hb ) hv
lemma restrict_P {s':Set (Points n)}(hp:s'⊆s)(hx:PlainF s f d k): PlainF s' f d k:= by intro u hi l ht; obtain ⟨C,h⟩:= hx _ hi l ht; exact ⟨C,fun i=> h ⟨i.val,hp i.property⟩⟩
lemma subsetF {s':Set (Points n)}(hp:s'⊆s)(h:Fiasco A s k b d a f): Fiasco A s' k b d a f:= fun m S v hs he=> ChargeP.pull ( h m S v hs he ) (fun i:(s'×S)=> (Set.inclusion hp i.1,i.2))
end YM.FVA2.O.Bind
