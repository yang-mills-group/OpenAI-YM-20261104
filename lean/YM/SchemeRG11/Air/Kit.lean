import YM.SchemeRG11.Air.Loft
/-! Correct Peano projection keeping full derivative precision. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Air
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels Long
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T:Align.Itinerary}{R:ℝ}
variable {M F: Type*}[AddCommGroup M][AddCommGroup F][Module ℝ M][Module ℝ F]
lemma wearer(L:M→ₗ[ℝ] F):∃ V:F→ₗ[ℝ] M,L ∘ₗ V ∘ₗ L=L:=by
 obtain ⟨r,H⟩:=LinearMap.exists_leftInverse_of_injective L.range.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
 obtain ⟨s,K⟩:=LinearMap.exists_rightInverse_of_surjective L.rangeRestrict (LinearMap.range_eq_top.mpr (by rintro ⟨v,m,h⟩; exact ⟨m,Subtype.ext h⟩))
 refine ⟨s ∘ₗ r,LinearMap.ext fun i=>?_⟩; change (L.rangeRestrict (s (r (L i)))).val=(L.rangeRestrict i).val; rw [show r (L i)=L.rangeRestrict i from LinearMap.congr_fun H (L.rangeRestrict i),show L.rangeRestrict (s (L.rangeRestrict i))=_ from LinearMap.congr_fun K _]; rfl
lemma istr {I:Type*}{f:I→ℕ→ℝ}{g:ℕ→ℝ}(s:Finset I)(h:∀ i∈s,f i=O[atTop] g): (fun k=>∑i∈s,f i k)=O[atTop] g:=by induction s using Finset.induction_on with
 | empty=>rw [show (fun _=>∑i∈(∅:Finset I),_)=fun _ : ℕ=>(0:ℝ) from funext fun _=>Finset.sum_empty]; apply isBigO_zero
 | insert i s hi ih=> simp only [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=>h j (by simp [hj]))
lemma bigger {I:Type*}[Fintype I](L:(I→ℝ)→ₗ[ℝ] ℝ)(f:ℕ→I→ℝ)(g:ℕ→ℝ)(h:∀i,(fun j=>f j i)=O[atTop] g): (fun k=>L (f k))=O[atTop] g:=by
 let B:= Pi.basisFun ℝ I
 have he(p:I→ℝ):L p=∑ i:I,L (B i)*p i:=by
   conv_lhs=> rw [← B.sum_repr p]
   rw [map_sum]; exact Finset.sum_congr rfl fun i _=> by rw [map_smul]; unfold B; simp [mul_comm]
 simp_rw [he (f _)]; exact istr _ (f:=fun i k=>L (B i)*f k i) (fun i _=>(h i).const_mul_left _)
abbrev ClassB(n:ℕ):= spanHull ℝ n
abbrev shapeK(n:ℕ):= (Unit ⊕ Axis) × Mob n
lemma dive_lower {f:Bevy ℝ}(h:f∈ClassB n):Flock.dive f∈ cap ℝ n:=dive_cap n f (in_hull.mpr fun i=>cap_succ _ (in_hull.mp h i))
lemma lap_down {f:Plane ℝ}(h:f∈cap ℝ n):lap f∈cap ℝ n:= lap_lower (cap_height (by omega) h)
def tipdot (n:ℕ): ↥(ClassB n)→ₗ[ℝ](shapeK n→ ℝ):=LinearMap.pi (fun i=> LinearMap.proj i.2 ∘ₗ formation n ∘ₗ (match i.1 with | Sum.inl _=>Flock.dive | Sum.inr a=> lap ∘ₗ (LinearMap.proj a)) ∘ₗ (ClassB n).subtype)
lemma fulldot (f:ClassB n)(h:tipdot n f=0): f.val∈ team ℝ n:=by
 refine ⟨f.property,?_,fun i=>?_⟩
 · apply flights_zero (dive_lower f.property); intro t ht; exact congrFun h (Sum.inl (),⟨⟨t.card,ht⟩,⟨t,rfl⟩⟩)
 apply flights_zero (lap_down (in_hull.mp f.property i)); intro t ht; exact congrFun h (Sum.inr i,⟨⟨t.card,ht⟩,⟨t,rfl⟩⟩)
abbrev Waves:=ℕ→ Bevy ℝ
def brittle (T:Align.Itinerary)(R:ℝ)(f:Waves):Prop:= ∀ a,Boarded T R (fun k=> f k a)
def keeps (T:Align.Itinerary)(R:ℝ)(f:Waves):Prop:= ∀ᶠ i in atTop,∀x,Near T R i x→Flock.dive (f i) x=0 ∧∀a,lap (f i a) x=0
lemma finitize(f:Slate)(s:Fliers)(h:∀p:Cover,∀ᶠ i in atTop, f i p=0)(x:Cover): ∀ᶠ i in atTop, fleet s (f i) x=0:=by
 induction s using Multiset.induction generalizing x with
 | empty=> exact h x
 | cons j t ih=>
    filter_upwards [ih (x+step j), ih x] with i hi hk; rw [fleet_cons]; change soar j _ _=_; rw [soar_apply,hi,hk,sub_self]
lemma stencilO(f:Slate)(s:Fliers)(p:ℕ→ℝ)(h:∀x,(fun i=> f i x)=O[atTop] p)(x:Cover): (fun i=>fleet s (f i) x)=O[atTop] p:=by induction s using Multiset.induction generalizing x with
 | empty=>exact h x
 | cons j t ih=>
    convert! IsBigO.sub (ih (x+step j)) (ih x) using 1; funext i; rw [fleet_cons];rfl
lemma payB {f:Waves}{g:ℕ→ClassB n}(hp: R>0)(hf:keeps T R f)(h:∀a:Axis,(∀ p:Cover,(fun i=> (f i a-(g i).val a) p)=O[atTop] latch T (n+1))):∀ x:shapeK n,(fun i=>tipdot n (g i) x)=O[atTop] latch T (n+1):=by
 let u:=fun i=> f i-(g i).val; let P:= latch T ((n:ℤ)+1)
 have he(x:Cover): ∀ᶠ i in atTop,Flock.dive (f i) x=0 ∧∀a,lap (f i a) x=0:=(hf.and (gate_const T hp x)).mono (fun i hi=>hi.1 _ ((gate_iff ..).mp hi.2))
 rintro ⟨j,y⟩
 let s:= y.snd.val
 cases j with
 | inl j=>
   have hw (p:Cover): (fun i=> Flock.dive (u i) p)=O[atTop] P:=by
      simp_rw [dive_apply,Finset.sum_apply,rear_apply]; exact istr _ (f:=fun a i=> u i a p-u i a (p-step a)) fun i _=> (h i p).sub (h i _)
   apply IsBigO.congr' (stencilO (fun i=> Flock.dive (u i)) s _ hw 0 |>.neg_left) _ (Filter.EventuallyEq.refl _ _)
   filter_upwards [finitize (fun i=> Flock.dive (f i)) s (fun p=> (he p).mono (fun i hi=>hi.1)) 0] with i hi; cases j; change -(fleet s _ 0) = fleet s (Flock.dive _) 0; unfold u; rw [map_sub,map_sub,Pi.sub_apply,hi]; abel
 | inr a=>
   have hw(p:Cover): (fun i=> lap (u i a) p)=O[atTop] P:=by
      simp_rw [lap,LinearMap.sum_apply,Finset.sum_apply]; refine istr _ ?_
      intro j _; simp only [Module.End.mul_apply,rear_apply,soar_apply]; exact ((h a _).sub (h a _)).sub ((h a _).sub (h a _))
   apply IsBigO.congr' (stencilO (fun i=> lap (u i a)) s _ hw 0 |>.neg_left) _ (Filter.EventuallyEq.refl _ _)
   filter_upwards [finitize (fun i=>lap (f i a)) s (fun p=> (he p).mono (fun i hi=>hi.2 _)) 0] with i hi; change -(fleet s (lap (u i a)) 0)=fleet s (lap ((g i).val a)) 0; unfold u; rw [Pi.sub_apply,map_sub,map_sub,Pi.sub_apply,hi]; abel
lemma lands (n:ℕ){f:Waves}(hp:R>0)(h:brittle T R f)(he:keeps T R f): ∃ g:ℕ→team ℝ n,∀ a s,Local T R (n+1) ((n:ℤ)-s.card) (fun i=> fleet s (f i a-(g i).val a)) :=by
 choose p H Q using (fun m a=>capMaker n (f m a))
 let g(i:ℕ):ClassB n:=⟨p i,in_hull.mpr (H i)⟩
 let O(a:Axis):= fun i=> f i a
 have hx(a:Axis)(s:Fliers)(he:s.card<n):(fun i=> fleet s (O a i-p i a) 0)=O[atTop] latch T ((n:ℤ)+1):=by unfold O; simp only [_root_.map_sub,Pi.sub_apply,Q _ a s he,sub_self]; apply isBigO_zero
 have hr(a k): (fun i=> (f i a-(g i).val a) k)=O[atTop] latch T (n+1):=noted (billow (f:=O a) (g:=fun i=> p i a) (fun i=> H i a) (h a) (hx a) 0) hp _
 let U:=tipdot n
 obtain ⟨K,W⟩:= wearer U
 have hv(j:ℕ): U (g j-K (U (g j)))=0:=by rw [map_sub,sub_eq_zero]; exact (LinearMap.congr_fun W _).symm
 refine ⟨fun i=>⟨_, fulldot _ (hv i)⟩,?_⟩; intro a
 apply billow (n:=n) (f:=O a) (fun i=>team_wing (fulldot _ (hv i)) a) (h a) -- check
 intro s hs
 let X : ↥(ClassB n)→ₗ[ℝ] ℝ:=LinearMap.proj 0 ∘ₗ fleet s ∘ₗ LinearMap.proj a ∘ₗ (ClassB n).subtype
 have Hk:= bigger (X.comp K) _ _ (payB hp he hr)
 convert! (hx a s hs).add Hk using 1; funext k; change fleet s (O a k-((g k).val a-(K (U (g k))).val a)) 0= _ + _; rw [sub_sub_eq_add_sub,add_sub_right_comm,map_add,Pi.add_apply]; rfl
end YM.SchemeRG11.Air
