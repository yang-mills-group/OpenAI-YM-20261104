import YM.SchemeRG11.Long.Loom
/-! Base class for edge cost factors and OPEN test polynomial inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World
open scoped Classical
variable {T:Align.Itinerary} {R:ℝ} {I:Type*}
variable {u v x y:ℤ}{f g:Slate}
abbrev RigidF(T:Align.Itinerary):= Wall T (fun _ _=>True) 0
structure Plain(T:Align.Itinerary)(u:ℤ)(f:Slate):Prop where
 wall: RigidF T u f
 watch: Streams T (fun _=>True) u f
namespace Plain
lemma widened(h:Plain T u f)(a:u≤v):Plain T v f:= ⟨h.wall.weaken a,h.watch.weaken a⟩
lemma zero :Plain T u 0:=⟨Wall.zero,Streams.zero⟩
lemma const(c:ℝ):Plain T 0 (fun _ _=>c):= ⟨Wall.const _,Streams.const _⟩
lemma add(h:Plain T u f)(k:Plain T u g):Plain T u (f+g):=⟨h.wall.add k.wall,h.watch.add k.watch⟩
lemma sub(h:Plain T u f)(k:Plain T u g):Plain T u (f-g):=⟨h.wall.sub k.wall,h.watch.sub k.watch⟩
lemma neg(h:Plain T u f):Plain T u (-f):=⟨h.wall.neg,h.watch.neg⟩
lemma scale(h:Plain T u f)(c:ℝ):Plain T u (c • f):= ⟨h.wall.pay_s c,h.watch.pod c⟩
lemma mul (h:Plain T u f)(w:Plain T v g): Plain T (u+v) (f*g) :=⟨by simpa only [zero_add] using h.wall.mul w.wall,h.watch.mul w.watch⟩
lemma sums(s:Finset I)(f:I→Slate)(h:∀i∈s,Plain T u (f i)):Plain T u (∑i∈s,f i):=⟨Wall.sum s f fun i w=>(h i w).1, Streams.sum s f fun i w=>(h i w).2⟩
lemma piles(s:Finset I)(f:I→Slate)(h:∀i∈s,Plain T u (f i)):Plain T u (fun k x=>∑i∈s,f i k x):=by have he:= sums s f h; rwa [show (fun (k:ℕ) (x:Cover)=>∑i∈s,f i k x)=_ from funext fun k=>funext fun x=> (show _=(∑i∈s,f i) k x from by simp only [Finset.sum_apply])]
lemma prod(s:Finset I)(u:I→ℤ)(f:I→Slate)(h:∀i∈s,Plain T (u i) (f i)): Plain T (∑i∈s,u i) (∏i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty=>rw [Finset.sum_empty,Finset.prod_empty]; exact const 1
 | insert i s hi ih=>rw [Finset.sum_insert hi,Finset.prod_insert hi]; exact (h i (by simp)).mul (ih (fun j hj=> h j (by simp [hj])))
lemma pow(h:Plain T u f)(n:ℕ):Plain T ((n:ℤ)*u) (f^n):=by induction n with
 | zero=>rw [pow_zero,Nat.cast_zero,zero_mul]; exact const 1
 | succ n ih=>rw [pow_succ,Nat.cast_add_one,add_mul,one_mul]; exact ih.mul h
lemma moved(z:Cover)(h:Plain T u f):Plain T u (fun i x=> f i (z+x)):=⟨Wall.moving (Eventually.of_forall fun _ _ _=> trivial) h.wall,h.watch.moving z⟩
end Plain
abbrev view(f:Cover→ℝ):Slate:=fun _=> f
lemma plain_coord (a:Axis):Plain T 1 (view (fun x=>(x a:ℝ))):=by
 refine ⟨⟨1,by norm_num, Eventually.of_forall fun i p _=>?_⟩,fun p _ _ z hz=>?_⟩
 · rw [zpow_zero,one_mul,one_mul,zpow_one]; exact (castabs p a).trans (by unfold d; linarith)
 refine ⟨p a,?_⟩; simp only [view,zpow_one]; exact ((EuclideanSpace.proj a).continuous.continuousAt.tendsto.comp (show Tendsto _ atTop _ from hz)) -- check
lemma plain_bin(n:ℕ)(a:Axis): Plain T n (view (fun x=> Flock.bin (x a) n)):=by
 induction n with
 | zero=>rw [Nat.cast_zero]; exact Plain.const 1
 | succ n ih=>
    let f:= view (fun (x:Cover)=>(x a:ℝ)); let g:Slate:=fun _ _=>(n:ℝ)
    have hz:Plain T 1 (f-g):= plain_coord a|>.sub ((Plain.const _).widened zero_le_one)
    have he:= (hz.scale (((n:ℝ)+1)⁻¹)).mul ih
    convert he using 1
    · push_cast; omega
    funext i x; change Flock.bin _ (n+1)=_; rw [Flock.bin]; change _= (_*((x a:ℝ)-(n:ℝ)))* _; rw [div_eq_mul_inv]; ring
lemma count_sum (s:Fliers):∑i:Axis,s.count i=s.card:=by
 induction s using Multiset.induction with
 | empty=>simp
 | cons i s ih=>
   have he(j:Axis):(i ::ₘ s).count j= s.count j+ if i=j then 1 else 0:=by by_cases h:i=j<;>simp [h,Ne.symm]
   simp_rw [he,Finset.sum_add_distrib,ih];simp
lemma plume_z (s:Fliers):Plain T s.card (view (pas s)):=by
 have hh:= Plain.prod (T:=T) Finset.univ (fun i:Axis=>((s.count i : ℕ):ℤ)) _ (fun i _=> plain_bin (T:=T) (s.count i) i)
 rw [← Nat.cast_sum,count_sum] at hh; convert hh using 1; funext i x; simp only [Finset.prod_apply]; rfl
lemma branchCost (n:ℕ)(f:Plane ℝ)(h:f∈ cap ℝ (n+1)): Plain T n (view f):=by
 induction n generalizing f with
 | zero=>
    have hh:f=fun _=>f 0:= funext fun x=> landed (member.mp h) _ (show Multiset.card (0:Fliers)=0 by rfl) x 0
    rw [Nat.cast_zero,hh]; apply Plain.const
 | succ n ih=>
   let b (s: Sym Axis (n+1)):= fleet s.val f 0
   let p:Plane ℝ:=∑ i:Sym Axis (n+1), b i • pas i.val
   have hg(s:Fliers)(hs:s.card=n+1): fleet s f=fleet s p:=by
      unfold p; rw [_root_.map_sum]; rw [Finset.sum_eq_single (s:=Finset.univ (α:=Sym Axis (n+1))) (⟨s,hs⟩:Sym Axis (n+1)),map_smul,mono_test rfl,if_pos rfl]; funext x; change _=fleet s f 0*(1:ℝ); rw [mul_one]; exact landed (member.mp h) _ hs x 0
      · intro i _ hk; rw [map_smul, mono_test (hs.trans i.property.symm), if_neg fun h=>hk (Subtype.ext h.symm),smul_zero]
      simp
   have hh := ih (f-p) (by intro s hs; rw [map_sub,sub_eq_zero]; exact hg s hs)
   have hv : Plain T (n+1:ℕ) (view p):=by
      have he(i:Sym Axis (n+1)):Plain T (n+1:ℕ) (view (b i • pas i.val)):=by have H:=((plume_z (T:=T) i.val).scale (b i)); rw [i.property] at H; exact H
      convert Plain.piles Finset.univ (fun i=>view (b i • pas i.val)) (fun i _=>he i) using 1
      ext i x; dsimp only [view,p]; simp only [Finset.sum_apply]
   convert (hh.widened (show (n:ℤ)≤ (n+1:ℕ) by omega)).add hv using 1; funext i x; exact (sub_add_cancel _ _).symm
lemma flight_cost (n:ℤ)(f:Plane ℝ)(hf:f∈cap ℝ (n+1).toNat)(s:Fliers): Plain T (n-s.card) (view (fleet s f)):=by
 induction s using Multiset.induction generalizing n f with
 | empty=>
   by_cases h:n<0
   · rw [show (n+1).toNat=0 by omega,groundZero] at hf; rw [show f=0 from hf,map_zero]; exact .zero
   rw [Multiset.card_zero,Nat.cast_zero,sub_zero]; have hh:= branchCost (T:=T) n.toNat f (show _ from (show n.toNat+1=(n+1).toNat by omega) ▸ hf)
   rw [Int.toNat_of_nonneg (by omega)] at hh; exact hh
 | cons i s ih=>
   rw [fleet_cons']; change Plain _ _ (view (fleet s (soar i f)))
   by_cases h:n<0
   · rw [show (n+1).toNat=0 by omega,groundZero] at hf; rw [show f=0 from hf,map_zero,map_zero]; exact .zero
   rw [show n-((i ::ₘ s).card:ℤ)= (n-1)-(s.card:ℤ) by rw [Multiset.card_cons]; omega]; apply ih (n-1); rw [show (n-1+1).toNat=n.toNat by omega]; apply soar_lower _ f _ i; rwa [show n.toNat+1=(n+1).toNat by omega]
end YM.SchemeRG11.Long
