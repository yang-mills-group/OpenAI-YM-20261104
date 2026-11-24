import YM.X.Chili.Virgin
import YM.X.Haze.Ear
/-!
# Shell step class. costs for π profile integration on root marks incl forwarded differences.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Friend
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension LatticePT MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Fielding Haze Clove Interval CellsInt
open Ocean
open scoped Topology ContDiff Classical BigOperators
variable {p:ℕ→Side} {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
variable {q:ℕ+} (hq:1<q.val){k m:ℕ}{a b n : ℤ}{R r:ℝ}{f g:Mist V}
def alter (x:Cover)(f:Mist V) : Mist V:= fun k z=> f k (z+x)
def forward (i:Axis)(f:Mist V):= alter (step i) f - f
@[simp] lemma alter_add {x:Cover}(f g:Mist V): alter x (f+g)=alter x f+alter x g:= rfl
lemma alter_step (i:Axis)(x:Cover)(f:Mist V): alter x (forward i f) = forward i (alter x f):= by funext k z; change f k (z+x+step i)-_= f k (z+step i+x)-_; rw [add_right_comm];rfl
lemma step_cost (x:Cover)(h:Visa q r a 0 f)(hr:R<r)(hy:R≥0) (hq:1<q.val): Visa q R a 0 (alter x f):= by
    obtain ⟨c,hc,ht⟩:= h.who; refine ⟨⟨c,hc,?_⟩,fun z hz hv y ht=>?_⟩
    · filter_upwards [ht,gate_shift hq _ _ hr hy x] with i hi hh z hz; have hx:=hi (z+x) (hh _ hz); simpa only [price,zpow_zero,mul_one, alter] using! hx
    exact h.whereL z hz (hv.trans hr.le) _ (pace_shift hq true ht x)
lemma alter_conj (x y:Cover) : alter x (alter y f)=alter (x+y) f:= by ext1 i; ext1 z; unfold alter;rw [add_assoc]
lemma downtick (L:List Axis)(i:Axis)(f:Cover→V): Interval.grads (i::L) f= Interval.grads L (Interval.differ i f):= by
    induction L generalizing i f with
    | nil=>rfl
    | cons j l IH=> rw [Interval.grads, IH j,show Interval.differ i (Interval.grads l (Interval.differ j f))= Interval.grads l (Interval.differ i (Interval.differ j f)) from IH i _,IH]; congr 1; funext z;unfold Interval.differ; rw [add_right_comm]; abel
-- use recursion from right, retains h parameter, also common symbol at no-shift.
structure Chase (q:ℕ+)(r:ℝ)(a:ℤ)(f:Mist V): Prop where
   toll (L:List Axis)(R:ℝ)(h:R≥0)(hv:R<r): Visa q R (a+L.length) 0 (fun k:ℕ=>Interval.grads L (f k))
variable {G:Gauge}
namespace Chase
lemma visa (h:Chase q r a f)(he:R≥0)(hx:R<r): Visa q R a 0 f:= by obtain ht:= h.toll [] R he hx; simpa only [List.length_nil,Interval.grads,Nat.cast_zero,add_zero] using! ht
lemma step (h:Chase q r a f)(i:Axis): Chase q r (a+1) (forward i f):= by
    constructor; intro L R hr hp; have ht:=h.toll (i::L) R hr hp; rw [show a+1+L.length=a+(i::L).length from by simp; ring]; simp_rw [downtick] at ht; exact ht
lemma grow (h:∀ R:ℝ, R≥0→ R<r→Visa q R a 0 f)(hx:∀ i:Axis, Chase q r (a+1) (forward i f)): Chase q r a f:= by
    constructor; intro L R hr hp; cases L
    · rw [List.length_nil,Nat.cast_zero,add_zero]; exact h R hr hp
    case cons i L=>
      simp_rw [downtick]; have he:= (hx i).toll L R hr hp; rw [show a+(i::L).length=a+1+L.length from by simp; ring]; exact he
lemma step2 (h:∀ T:ℝ,T≥0→T<r→Visa q T a 0 f)(hb:∀ i:Axis,Chase q r (a+1) (forward i f)): Chase q r a f:= grow h hb
lemma hikes (f g:Mist V)(L:List Axis): (fun k:ℕ=> Interval.grads L ((f+g) k)) = (fun k:ℕ=> Interval.grads L (f k))+(fun k:ℕ=> Interval.grads L (g k)):= by
    induction L generalizing f g with
    | nil=> rfl
    | cons i L IH=> funext k z; have hp(x:Cover): Interval.grads L ((f+g) k) x=Interval.grads L (f k) x + Interval.grads L (g k) x := congr_fun (congr_fun (IH f g) k) x; change Interval.differ i (Interval.grads L ((f+g) k)) z=Interval.differ i (Interval.grads L (f k)) z + Interval.differ i (Interval.grads L (g k)) z; unfold Interval.differ;rw [hp,hp]; abel
lemma translates (L:List Axis)(f:Mist V)(x:Cover): (fun k:ℕ=>Interval.grads L (alter x f k))= alter x (fun k:ℕ=>Interval.grads L (f k)):= by
    induction L with
    | nil=> rfl
    | cons i L IH=>
        funext k z; rw [Interval.grads,differ,show Interval.grads L (alter x f k)=_ from congr_fun IH k];unfold alter; simp only [Interval.grads,differ,add_right_comm]
include hq in
lemma alts (x:Cover)(h:Chase q r a f):Chase q r a (alter x f):= by
    constructor; intro L R hr hp; obtain ⟨s,hS,ht⟩:= exists_between hp; rw [translates]; exact step_cost x (h.toll _ s (by linarith) ht) hS hr hq
lemma plus (h:Chase q r a f)(hp:Chase q r a g): Chase q r a (f+g):=⟨fun L R hr hx=> hikes f g L ▸ Visa.add (h.toll L R hr hx) (hp.toll L R hr hx)⟩
include hq in
lemma falls (h:Chase q r a f)(he:b≤a):Chase q r b f:=⟨fun L R hr hx=> Visa.stretch hq (h.toll L R hr hx) hr (by omega) (by omega)⟩
lemma moves {W:Type*}[NormedAddCommGroup W][NormedSpace ℝ W]{L:V→L[ℝ] W}(h:Chase q r a f): Chase q r a (fun k z=>L (f k z)):= by
    constructor; intro l R hr hx; let u(k:ℕ)(z:Cover):= L (f k z); have hp(l:List Axis)(j:ℕ)(z:Cover): Interval.grads l (u j) z=L (Interval.grads l (f j) z):= by induction l generalizing z with| nil=>rfl|cons i l IH=>simp_rw [Interval.grads,differ,map_sub,IH]
    change Visa q R _ _ (fun k:ℕ=>Interval.grads l (u k)); simp_rw [show ∀ i:ℕ,Interval.grads l (u i)=_ from fun i=> funext (hp l i)]; exact (h.toll l R hr hx).mapL L
lemma costs (t:ℝ)(h:Chase q r a f): Chase q r a (t • f) := Chase.moves (L:= t • ContinuousLinearMap.id ℝ V) h
lemma cuts (h:Chase q r a f)(hp:Chase q r a g):Chase q r a (f-g):= by rw [sub_eq_add_neg, ← neg_one_smul ℝ]; exact h.plus (hp.costs _)
end Chase
end YM.PositionX.Friend
