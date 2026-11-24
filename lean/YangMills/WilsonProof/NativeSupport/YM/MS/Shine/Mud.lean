import YM.MS.Shine.Mud
import YangMills.WilsonProof.NativeSupport.YM.MS.Shine.Heart
/-!
# Dimensional continued Mellin support

Weighted cancellations do not require convergent path through large positive ε (manuscript proves from graph definition analytically agrees). Uses unique e-weights at forests. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{b:Bool}{D W:Set ℂ}{R T:ℝ}{c:ℂ}{F H:Mob G}{U:Rip G}{x:ℂ→ℂ}{f g:ℂ→ Mob G} {k:ℤ} {m n:ℕ}
lemma Lift.cycle (h:Lift f F)(hp:Knot b U)(he:∀ᶠ i in dotty, Sturdy b (f i)): Lift (fun i=> ocean i U (f i)) (ocean 0 U F):= by
    obtain ⟨x,R,hr,hx',hH,rfl,Hx⟩:= Lift.spin h he; obtain ⟨T,ht,hV⟩:= dotty_mem.mp high0; let A:= min R T; let D:= disc A; have hA :0<A:= lt_min hr ht; have hh:D⊆disc R:= ball_subset_ball (min_le_left ..);
    refine Lift.congr (Lift.trim ( wind_he (u:=fun _=>U) ( hx'.mono hh) (Hop.crate hp.price) (fun i hi=> ?_) (fun i hi=> Hx i (hh hi)) (fun _ _=>hp.token) isOpen_ball ) hA) ?_
    · by_cases he:i=0; · rw [he]; simpa using Town_nat 0
      exact hV _ (ball_subset_ball (min_le_right ..) hi) he
    filter_upwards [hH] with i hi; exact congr_arg _ hi
lemma Lift.tree (h:Lift f F)(hr:rPrice U)(he:Lift g H): Lift (fun i=> arbor U (f i) (g i)) (arbor U F H):= by
    obtain ⟨x,R,hR,h,hX,rfl⟩:=h; obtain ⟨u,T,hT,v,Ht,rfl⟩:= he; refine Lift.congr (Lift.trim ((h.mono (ball_subset_ball (min_le_left R T))).woods (v.mono (ball_subset_ball (min_le_right R T))) (Hop.crate hr)) (lt_min hR hT)) ?_; filter_upwards [hX,Ht] with t ht hH; rw [ht,hH]
lemma Lift.portQ (h:Lift f F){Q:Shade G}(hp:Priced Q): Lift (fun i=>portZ Q (f i)) (portZ Q F):= by obtain ⟨x,R,hr,h,hX,rfl⟩:=h; exact Lift.congr (Lift.trim (Hol.port hp h) hr) (hX.mono (fun i hi=> congr_arg _ hi))
-- expose .spotX etc

def mer (f:ℂ→Mob G): Prop:= ∃ n:ℕ, altitude n f
lemma pay_add (m n:ℕ)(f:ℂ→Mob G): paid (m+n) f=paid m (paid n f):= funext fun i=> by unfold paid; rw [pow_add,mul_smul]
lemma pay_zero (f:ℂ→Mob G): paid 0 f=f:=by ext; simp [paid]
lemma pay_live (m:ℕ)(h:Live f): Live (paid m f) := Live.high (x:=fun i=>i^m) h (fun p _=>by fun_prop) (show (0:ℝ)<1 from zero_lt_one)
lemma pay_price (h:altitude n f): ∀ᶠ i in dotty,kPrice (f i):= by
    filter_upwards [ Live.price h,dotty_non] with i hi hI; rw [show f i = (i^n)⁻¹ • paid n f i from Eq.symm (inv_smul_smul₀ (pow_ne_zero n hI) (f i))]; convert! fall_scale (U:=fun _:Unit=> (i^n)⁻¹) hi (const_sc ..) using 1; ext; simp
namespace altitude
lemma congr (h:altitude n f)(he:f=ᶠ[dotty] g): altitude n g:= Live.congr h (he.mono fun i hi=> congr_arg ((i^n) • · ) hi)
lemma climb (h:altitude n f)(he:n≤m): altitude m f:= by obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le' he; unfold altitude; rw [pay_add]; exact pay_live _ h
lemma zero : altitude m (0:ℂ→Mob G):= by unfold altitude; rw [show paid m (0:ℂ→Mob G)=0 from by ext; simp [paid]]; exact Live.zero
lemma add (h:altitude m f)(he:altitude m g): altitude m (f+g):= by convert Live.add h he using 1; unfold altitude; rw [show paid m (f+g)=paid m f + paid m g from funext fun i=> smul_add (i^m) (f i) (g i)]
lemma neg (h:altitude m f): altitude m (-f):= by unfold altitude; rw [show paid m (-f)= -paid m f from funext fun i=> smul_neg ..]; exact Live.neg h
lemma sub (h:altitude m f)(he:altitude m g): altitude m (f-g):= by rw [sub_eq_add_neg]; exact h.add he.neg
lemma smul (h:altitude m f)(hp:Forest (disc R) x)(hr:0<R): altitude m (x • f):= by unfold altitude; rw [show paid m (x • f)=x • paid m f from funext fun i=>smul_comm (i^m) (x i) (f i)]; exact Live.high h hp hr
lemma trees (h:altitude m f)(hx:rPrice U)(hp:altitude n g): altitude (m+n) (fun i=> arbor U (f i) (g i)):= by
   unfold altitude; rw [show paid (m+n) (fun i=>arbor U _ _) = (fun i=>arbor U (paid m f i) (paid n g i)) from funext (fun i=> by unfold paid; simp only [← schedule,map_smul,LinearMap.smul_apply,pow_add, mul_smul]; exact smul_comm (i^m) (i^n) _)]; obtain ⟨a,h⟩:= h; obtain ⟨p,hp⟩:=hp; exact ⟨_,Lift.tree h hx hp⟩
lemma rode (h:altitude m f)(hp:Knot b U)(ht:∀ᶠ i in dotty, Sturdy b (f i)): altitude m (fun i=> ocean i U (f i)):= by
   obtain he:= pay_price h; obtain ⟨a,h⟩:= h; refine ⟨_,Lift.congr (Lift.cycle h hp (ht.mono fun i hi=> Sturdy_scale hi (i^m))) ?_⟩; filter_upwards [ht,he] with i hi hP; exact scaleR hp ⟨hP, hi⟩ (i^m)
lemma portQ (h:altitude m f)(Q:Shade G)(hp:Priced Q): altitude m (fun i=>portZ Q (f i)):= by
   obtain ⟨F,h⟩:= h; refine ⟨_,Lift.congr ( Lift.portQ h hp) (Eventually.of_forall fun i=> map_smul (sweepQ Q) (i^m) (f i))⟩
lemma mount (h:altitude m f)(t:ℝ)(a:ℂ): altitude m (fun i=> plow a t (f i)):= by obtain ⟨F,h⟩:=h; exact ⟨_,Lift.congr ( Lift.plowX h t a) (Eventually.of_forall fun i=> map_smul (plower a t) (i^m) (f i))⟩
lemma spot (h:altitude m f)(k:ℤ): altitude m (fun i=> Garment.spot k (f i)):= by obtain ⟨F,h⟩:=h; exact ⟨_,Lift.congr (Lift.spotX h k) (Eventually.of_forall fun i=> map_smul (Garment.spot k) (i^m) (f i))⟩
end altitude
namespace mer
lemma uLive (h:Live f): mer f:=⟨0,by unfold altitude; rw [pay_zero]; exact h⟩
lemma congr (h:mer f)(he:f=ᶠ[dotty] g): mer g:=by obtain ⟨n,h⟩:=h; exact ⟨n,h.congr he⟩
lemma price (h:mer f): ∀ᶠ i in dotty,kPrice (f i):= by obtain ⟨n,h⟩:=h; exact pay_price h
lemma zero : mer (0:ℂ→ Mob G):= ⟨0,altitude.zero⟩
lemma add (h:mer f)(hv:mer g): mer (f+g):= by obtain ⟨n,h⟩:=h; obtain ⟨m,hv⟩:=hv; exact ⟨max n m,(h.climb (le_max_left ..)).add (hv.climb (le_max_right ..))⟩
lemma neg (h:mer f): mer (-f):= by obtain ⟨n,h⟩:=h; exact ⟨_,h.neg⟩
lemma sub (h:mer f)(hv:mer g): mer (f-g):=by rw [sub_eq_add_neg]; exact h.add hv.neg
lemma fin (S:Finset I){F:I→ℂ→ Mob G}(h:∀ i∈S,mer (F i)): mer (∑ i∈S,F i):= by
   classical
   induction S using Finset.induction with| empty=> simpa only [Finset.sum_empty] using mer.zero| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=>h j ( Finset.mem_insert_of_mem hj))
lemma high (h:mer f)(hp:Forest (disc R) x)(hr:0<R): mer (x • f):= by obtain ⟨n,h⟩:=h; exact ⟨_,h.smul hp hr⟩
lemma static (h:mer f)(c:ℂ): mer (c • f):= h.high (x:=fun _=>c) (fun _ _=> differentiableAt_const _) zero_lt_one
lemma trees (h:mer f)(hv:rPrice U)(hp:mer g): mer (fun i=> arbor U (f i) (g i)):= by obtain ⟨n,h⟩:=h; obtain ⟨k,hp⟩:=hp; exact ⟨ _,h.trees hv hp⟩
lemma rode (h:mer f)(hp:Knot b U)(ht:∀ᶠ i in dotty, Sturdy b (f i)): mer (fun i=> ocean i U (f i)):= by obtain ⟨n,h⟩:=h; exact ⟨_,h.rode hp ht⟩
lemma portQ (h:mer f)(Q:Shade G)(hp: Priced Q): mer (fun i=> portZ Q (f i)):= by obtain ⟨n,h⟩:=h; exact ⟨_,h.portQ Q hp⟩
lemma mount (h:mer f)(t:ℝ)(z:ℂ): mer (fun i=> plow z t (f i)):= by obtain ⟨n,h⟩:=h; exact ⟨_,h.mount t z⟩
lemma spot (h:mer f)(k:ℤ): mer (fun i=> Garment.spot k (f i)):= by obtain ⟨n,h⟩:=h; exact ⟨_,h.spot k⟩
end mer
end YM.MS.Shine
