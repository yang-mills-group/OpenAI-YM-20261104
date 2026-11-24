import YM.Qlocal.Lined
import YM.Qlocal.Canopy.Earmark
/-!
 # Product/resizing rules for the TRUE contour-level estimates. Exact coupling powers
 and finite log with real witnessed storage. Horizon observations shrink in the argument
 separate. Keep log comparison in the field-amplitude scale Γ (not grade rounding).
 Locally weighted Cover all stencils and earnings elsewhere.
 `TaylorCap` here pointwise also with all derivative Brush bounds; Πsup from book scheduling
 when instantiating. Curves.V.St.Ph.S.Clipping pleasure via same Lane estimator (later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Canopy
open Function Finset Filter Topology
open AllOrder Ker Laplace Laplace.SigmaP Response Catch Catch.Clock PositionX.Jet
open ConnectedActivityE6 Blaze Brush PertExtension PertExtension.Series
open PhysicalNext Repeat Fare Lapis
open scoped Topology ContDiff BigOperators Classical
variable {ι σ : Type*} {S: Catch.Clock ι}{X:ι→ Type} [∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)]
    {j k q n m r:ℕ} {d t:ι→ℝ}{a b g:∀ i,X i→ℝ}{A B :ℝ}{x:∀ i,X i}
namespace Lithe
lemma stretched {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] {f:X→ℝ}{u:X}{c:ℝ}(hp:0 ≤ c)(he:Brush j A (c+c) f u): Brush j (2^j*A) c f u:= by
 refine ⟨he.smooth,hp,fun i hi=> (he.order _ hi).trans ?_⟩; rw [←two_mul,mul_pow]; calc
   _ ≤ A * ((2:ℝ)^j*c^i):=by gcongr; exact he.nonneg; norm_num
   _ = _ := by ring
lemma daylight (h: Catch.Cover S j A d a x)(hB:Catch.Cover S j B d b x) : Catch.Cover S j (A+B) d (fun i=>a i*b i) x:= by
 intro e he; let r:= (e-(A+B))/3; have hr:0<r:=by unfold r;linarith
 filter_upwards [S.positive,h (A+r) (lt_add_of_pos_right _ hr),hB (B+r) (lt_add_of_pos_right _ hr), S.slack (b:=e) (a:=(A+r)+(B+r)) (by unfold r;linarith) (2^j)] with i hi ha hb hz; exact (stretched ha.pos (ha.paints hb)).climb (by rw [← Real.rpow_add hi]; exact hz.le) le_rfl
-- M₁ actual ordinate & estimate after coefficient coupons all at coordinates (=Motion.Scale.w already pulled back);
-- tape unscaled in t. `d` reciprocal damping. Perspective.
abbrev Tape (X:ι→Type):= (i:ι) → X i→ Word ℝ
def beam (P:Tape X)(k:ℕ)(t:ι→ℝ)(i:ι)(x:X i): ℝ:= PositionX.Jet.delay (P i x) k (t i)
local notation "Hx"=> Catch.Cover S j
structure Sail {X:ι→Type} [∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℝ (X i)](S:Catch.Clock ι) (t d:ι→ℝ) (j k:ℕ) (P:Tape X)(a:∀ i,X i→ℝ)(x:∀ i,X i): Prop where
 wage : ∀ p ≤ k, Catch.Cover S j 0 d (fun i x=> P i x p) x
 total: Catch.Cover S j 0 d a x -- redundant.H.Record.
 cost : ∀ p ≤ k, Catch.Cover S j (graded (p+1)) d (fun i=> a i-beam P p t i) x
variable {P Q:Tape X}
namespace Sail
variable (ht : S.Meter t (-(1/2))) (hd:∀ᶠ i in S.rail,0≤ d i)
local notation "H"=> Sail S t d j k
-- normalize to total.Pe.N.
include hd ht
lemma shine (P:Tape X)(hB:∀ p ≤ k,Hx 0 d (fun i x=> P i x p) x): Hx 0 d (beam P k t) x := by
 let f(p:ℕ)(i)(x:X i):= (t i)^p • P i x p; have hv p (hp:p ≤ k) : Hx 0 d (f p) x := ((hB p hp).caliber (ht.pow p)).weak (by simp); apply (Catch.Cover.booking (F:=f) (range (k+1)) (fun k hk=> hv k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) hd).home; filter_upwards with i; ext1 x; exact Finset.sum_apply ..
lemma sails (P:Tape X)(hB:∀ p≤ k,Hx 0 d (fun i x=> P i x p) x) (hx: Hx (graded (k+1)) d (fun i=> a i-beam P k t i) x): H P a x:= by
 let v(h:ℕ):=  (fun i=> a i-beam P h t i); have he : Hx 0 d a x:= by
    apply (Catch.Cover.add (hx.weak (show (graded (k+1))≤0 from ?_)) (shine ht hd P hB)).home; swap; · unfold graded; exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity) -- if grade as -1/2*?
    filter_upwards with i; ext1 x; change a i x- _+_= _; abel
 refine ⟨hB,he,fun p hp=>?_⟩; have hg(h:ℕ)(hh:p≤ h)(he:h≤k): Hx (graded (p+1)) d (fun i=> beam P h t i-beam P p t i) x:= by
    induction hh with
    | refl=> simp_rw [sub_self]; exact Catch.Cover.fixed (fun _=> (0:ℝ)) hd (by simp_rw [norm_zero]; exact Meter.nil S _)
    | @step l hh ih=>
       have ht : Hx (graded (p+1)) d (fun i x=> (t i)^(l+1) • P i x (l+1)) x:= ((hB (l+1) he).caliber (ht.pow _)).weak (by unfold graded; push_cast; nlinarith only [Nat.cast_le (α:=ℝ)|>.mpr hh]); apply (Catch.Cover.add (ih (by omega)) ht).home; filter_upwards with i; ext1 x; dsimp only [beam,PositionX.Jet.delay,Pi.add_apply,Pi.sub_apply]; rw [sum_range_succ (fun q=>(t i)^q • P i x q) (l+1)]; abel
 apply (Catch.Cover.add (hx.weak ?_) (hg k hp le_rfl)).home; swap; · unfold graded; push_cast; nlinarith [Nat.cast_le (α:=ℝ)|>.mpr hp]
 filter_upwards with i; ext1 x; apply sub_add_sub_cancel
omit ht hd
variable (hp:Sail S t d j k P a x) (hq:Sail S t d j k Q b x)
include hp
lemma hire (h:Hx (graded (k+1)) d (fun i=>g i-a i) x): H P g x:=by
 let c:=graded (k+1); have ht:Hx 0 d g x:= (Cover.home ((h.weak (show c≤0 from (by unfold c graded; nlinarith [Nat.cast_nonneg (α:=ℝ) (k+1)]))).add hp.total ) (Eventually.of_forall (fun i=> sub_add_cancel _ _))) -- errs
 refine ⟨hp.wage,ht,fun u hu=>?_⟩; exact (Cover.add (h.weak (by unfold graded; push_cast; nlinarith [Nat.cast_le (α:=ℝ)|>.mpr hu])) (hp.cost u hu)).home (Eventually.of_forall (fun i=> sub_add_sub_cancel ..))
-- estimate weights any stable scalar (Budget.Actor.Price inertia). scales allow xray.Kλ.R.
lemma scaled (v:ι→ℝ)(h:S.Meter v 0): H (fun i=>v i • P i) (fun i=>v i • a i) x:= by
 refine ⟨fun p h'=>?_ ,?_,fun p h'=>?_⟩ -- variable shadowing h.Height
 · exact ((hp.wage _ h').caliber h).weak (by simp) -- collision?
 · exact (hp.total.caliber h).weak (by simp)
 refine ((((hp.cost p h').caliber h)).weak (by simp)).home (Eventually.of_forall (fun i=>?_)); ext1 x; unfold beam; change v i • (_-_) = v i • a i x-PositionX.Jet.delay (v i • P i x) p (t i); rw [smul_sub]; congr 1; unfold PositionX.Jet.delay; rw [Finset.smul_sum]; exact sum_congr rfl fun i _=> smul_comm ..
include hq
lemma earned: H (P+Q) (a+b) x:= by
 refine ⟨fun i hi=> Cover.add (hp.wage _ hi) (hq.wage _ hi), hp.total.add hq.total, fun i hi=>?_⟩; apply (Cover.add (hp.cost _ hi) (hq.cost _ hi)).home; filter_upwards with z; ext1 u; simp only [Pi.sub_apply,Pi.add_apply,beam,PositionX.Jet.delay,smul_add,sum_add_distrib]; abel
omit hq
lemma rest : H (-P) (-a) x:= by change H (fun i=> -(P i)) (fun i=> -(a i)) x; simpa only [neg_one_smul] using (scaled hp (fun _=> -1) (Meter.const S (-1))) -- need beta defeq.
include hq in
lemma emerged: H (P-Q) (a-b) x:=by simpa only [sub_eq_add_neg] using earned hp hq.rest
omit hp
include hd
lemma free (r:ℝ): H (fun i (_:X i)=> just r) (fun i (_:X i)=> r) x:= by
 let f(t:ℕ)(i:ι)(_ : X i):= just r t; let v:=(k:ℕ); refine ⟨fun i hi=> Cover.fixed _ hd (Meter.const S ‖just r i‖), Cover.fixed _ hd (Meter.const S ‖r‖), fun i hi=>?_⟩;
 apply (Cover.fixed (X:=ι) (fun _=> (0:ℝ)) hd ?_).home; swap; · simp only [norm_zero]; exact Meter.nil S _ -- context pee before `Finite`. syntax
 filter_upwards with n; funext u; change 0=r- PositionX.Jet.delay (just r) i _; unfold PositionX.Jet.delay; rw [sum_eq_single (0:ℕ)]; · simp [just]
 · intro j _ hj; simp [just,hj]
 simp
lemma dark: H (0:Tape X) 0 x:= by
 have hc:= free (j:=j) (k:=k) (t:=t) (x:=x) hd 0; rw [show (fun i (_:X i)=> just (0:ℝ)) = 0 from (by ext i x p; simp [just])] at hc; exact hc
lemma quota (u:Finset σ)(Q:σ→ Tape X)(a:σ→ (i:ι)→X i→ℝ)(h:∀ i∈u,H (Q i) (a i) x): H (∑ i∈u,Q i) (∑ i∈u,a i) x:= by induction u using Finset.induction_on with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact dark hd
   | insert i u hi ih=>rw [sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).earned (ih fun i hi=>h i (mem_insert_of_mem hi)) -- h x includes implicit ht? not intended.
omit hd
include hp
lemma cross {P':Tape X}(h:P=P')(hq:a=g): H P' g x:= by subst P' g; exact hp
end Sail
end Lithe
end YM.Qlocal.Canopy
