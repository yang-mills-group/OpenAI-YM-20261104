import YM.RegulatorIR.Pupil.Solar
import YM.RegulatorIR.Momentum.Crest

/-! Rank-two polynomial normalization. Leading gesture cancellation on full
Cover obtained from W1 exactly (no estimate of subtractions enters here).
No torus-incompatibility assumption set on input jets beyond W1. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G : Gauge}{T:Packet (Foot G) 2}
abbrev CapG (G:Gauge):= Regalia G.ColorIndex
-- alternate root for applying post-time

def starE (T:Packet (Foot G) 2)(x y:CapG G)(p:Cover) := twin T (ask 0 x) (ask p y)
def costM (T:Packet (Foot G) 2) := ∀ x y: CapG G,∀ a:Room,∀ n:ℕ,n ≤ 3 → Summable fun p=> starE T x y p*dial a p^n
def shine (T:Packet (Foot G) 2)(n:ℕ)(a:Room)(x y : CapG G):= recital (starE T x y) n a

lemma stretch_T (a: Room)(x y: Cover) : dial a (x+y) = dial a x+dial a y:=by simp_rw [dial,Pi.add_apply,Int.cast_add,mul_add,sum_add_distrib]
lemma pace_T (a: Room)(i:Axis): dial a (step i)=a i:=by rw [show step i=(hop i:Cover) from funext (fun j=>by simp),dial_step]
lemma spin_T (p:Signed)(a:Room)(x:Cover): dial (p.act a) (p.act x)=dial a x:=by
 unfold dial; rw [← p.perm.sum_comp]; apply sum_congr rfl; intro i _; rw [Signed.act_at, Signed.act_at]; split <;> first|rfl|simp
 exact fun _ _=>Finset.mem_univ _

lemma powS {P:Cover→ℝ}{n:ℕ}(a:Room)(c:ℝ)(h:∀ i≤n,Summable fun q=> P q*dial a q ^i):
 Summable (fun q=>P q*(dial a q+c)^n) ∧ ∑'q,P q*(dial a q+c)^n = ∑ i∈Finset.range (n+1),recital P i a * (c^(n-i)*(n.choose i)):=by
 let f(i:ℕ)(q:Cover):=P q*dial a q^i
 let g(i:ℕ):=c^(n-i)*n.choose i; let s:=Finset.range (n+1)
 have he(i:ℕ)(hi:i∈s) : Summable fun q=> f i q * g i:= (h i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).mul_right _
 have hx q:P q*(dial a q+c)^n=∑ i∈s,f i q*g i:=by rw [add_pow,mul_sum];unfold f g; apply sum_congr rfl; intro i _;ring
 simp_rw [hx]; refine ⟨summable_sum he,?_⟩ -- name
 rw [Summable.tsum_finsetSum he]; simp_rw [tsum_mul_right]; rfl

namespace Rules
variable (H:Rules T) (P:costM T) (x y:CapG G)
include H
lemma cell_v (c:Cover): Momentum.cell (ask c x) y T=starE T x y:=by
 funext t; refine Eq.trans ?_ (show T (tol c ∘ ![ask 0 x,ask t y])= _ from H.throughout ..); apply congr_arg T; ext1 i;fin_cases i <;> change ask _ _=( (_+_,_),_) <;> simp [ask,area]
lemma symmetric (v:Cover): starE T x y (-v)=starE T y x v:=by
 unfold starE; rw [H.twinSym]; symm; refine Eq.trans ?_ (show T (tol v ∘ ![ask (-v) y,ask 0 x])= _ from H.throughout ..); apply congr_arg T; ext1 i; fin_cases i <;> change ask _ _= ( (_+_,_),_) <;> simp [ask]
omit P
lemma rotor (n:ℕ)(a:Room): shine T n a x y=shine T n (-a) y x:=by
 unfold shine recital; rw [← (Equiv.neg Cover).tsum_eq (fun v=>starE T x y v*dial _ _^n)]; apply tsum_congr;intro i; change starE T x y (-i)*dial a (-i)^n=starE T y x i*dial (-a) i^n; rw [show _= _ from H.symmetric x y i];apply congr_arg (_*·); apply congr_arg (fun i:ℝ=>i^n); simp [dial, neg_mul]

def cLift (p:Signed)(v:Axis): Cover:= if p.flip v then -step (p.perm v) else 0
def claw (p:Signed)(x:CapG G): CapG G:= (p.perm x.1,x.2)
omit H in
lemma asksSpin (b:Signed)(s:Cover): shore b (ask s x)= ask (b.act s+cLift b x.1) (claw b x):=by
 cases hx:b.flip x.1 <;> simp [shore,ask,claw,cLift,Step.used,Axial.rotateE,Step.rotate,posDir,hx,affine,sub_eq_add_neg]
lemma turnStar (p:Signed)(v:Cover): starE T (claw p x) (claw p y) (p.act v+(cLift p y.1-cLift p x.1)) = Pupil.sign p x.1*Pupil.sign p y.1*starE T x y v:=by
 have h:= H.glow p (ask 0 x) (ask v y); rw [asksSpin, asksSpin,p.act_zero,zero_add] at h
 let c:=cLift p x.1; let d:=cLift p y.1
 refine Eq.trans ?_ h; unfold starE twin; refine Eq.trans ?_ (show T (tol (-c) ∘ ![ask c _,ask (p.act v+d) _])=_ from H.throughout ..)
 apply congr_arg; ext1 i; fin_cases i
 · change ask 0 _=(((-c)+c,_),_);simp [ask]
 change ask (p.act v+(d-c)) _= ask (-c+(p.act v+d)) _; rw [show p.act v+(d-c)= -c+(p.act v+d) by abel]

include P
lemma act_lift (p:Signed)(a:Room)(n:ℕ)(he:n ≤3)(H':∀ i<n,shine T i a x y=0): shine T n (p.act a) (claw p x) (claw p y) = Pupil.sign p x.1*Pupil.sign p y.1*shine T n a x y:=by
 let c:= cLift p y.1-cLift p x.1; let g:= (p.actEquiv (R:=ℤ)).toEquiv.trans (Equiv.addRight c)
 let s:= Pupil.sign p x.1 * Pupil.sign p y.1
 unfold shine recital; rw [← g.tsum_eq]; change (∑' q,starE T (claw p x) _ (p.act q+c)*dial _ (p.act q+c)^n)=_
 simp_rw [stretch_T,spin_T,show ∀ q,starE T _ _ (p.act q+c)=_ from turnStar H x y p, mul_assoc (Pupil.sign p x.1*Pupil.sign p y.1)] -- rw s?
 rw [tsum_mul_left]; apply congr_arg;rw [(powS a _ (fun i (hi:i≤n)=>P x y a i (le_trans hi he))).2]
 rw [sum_eq_single_of_mem n (by simp)]; unfold recital; simp
 intro i hi h; rw [show recital (starE T x y) i a=0 from H' i (by rw [Finset.mem_range] at hi;omega),zero_mul]
variable (a:Room)(j:G.ColorIndex)
-- all sums anchored by input absolute polynomial moments
lemma neutral (k:ℕ)(he:k ≤3):
    (∑ i:Axis,shine T k a x (i,j))=∑ i:Axis,∑ n∈ Finset.range (k+1), shine T n a x (i,j)*(a i^(k-n)*(k.choose n)):=by
 let Y(i:Axis):=starE T x (i,j); let f(i:Axis)(z:Cover):=Y i z*dial a z^k;let g(i:Axis)(z:Cover):=Y i (z-step i)*dial a z^k
 have hx i : Summable (f i):= P x (i,j) a k he
 let l(i:Axis):= shine T k a x (i,j)
 have hh(i:Axis)(t:Cover):g i (t+step i)=Y i t*(dial a t+a i)^k:=by unfold g;rw [stretch_T,pace_T,add_sub_cancel_right]
 have he'(i) := powS a (a i) (fun n (hp:n≤k)=>P x (i,j) a n (hp.trans he))
 have hp(i:Axis) : Summable (g i):= by
    let X:= Equiv.addRight (Lattice.step i:Cover)
    have ht: Summable (fun t:Cover=> g i (t+step i)):=by simp_rw [hh]; exact (he' i).1
    change Summable (g i ∘ X) at ht
    exact X.summable_iff.mp ht
 calc
    _ = ∑' t:Cover,∑ i:Axis, f i t:= (Summable.tsum_finsetSum (fun i (_:i∈Finset.univ)=> hx i)).symm
    _ = ∑' t:Cover,∑ i:Axis,g i t:=by
       apply tsum_congr;intro z; apply sub_eq_zero.mp; rw [← Finset.sum_sub_distrib]; unfold f g; simp_rw [← sub_mul,← sum_mul]; rw [show ∑ i:Axis, (Y i z-Y i (z-step i))=0 from H.diverge ..,zero_mul]
    _ = _:=by
       rw [Summable.tsum_finsetSum (fun i _=>hp i)];apply sum_congr rfl;intro i _; rw [← (Equiv.addRight (step i:Cover)).tsum_eq (g i)]; change (∑' t:Cover,g i (t+step i))= _;simp_rw [hh]; exact (he' i).2
lemma cloud0 : shine T 0 a x y=0:=by
 have hv(i) (b:Room): shine T 0 b x i=shine T 0 a x i:=tsum_congr (fun j=>by simp) -- j implicit
 let b:Room:= Lattice.step y.1; have h:= neutral H P x b y.2 1 (by omega); simp_rw [Finset.sum_range_succ] at h
 simp only [zero_add, sum_range_zero,Nat.choose_self,Nat.choose_zero_right,Nat.cast_one,mul_one,Nat.sub_self,pow_zero,Nat.sub_zero,pow_one] at h -- maybe simp progress
 rw [Finset.sum_add_distrib] at h; let f(i:Axis):=shine T 0 b x (i,y.2)*b i
 have hP: (∑ i:Axis,f i)=0:=by unfold f; linarith
 rw [Finset.sum_eq_single y.1] at hP; simp [f,b,hv]  at hP; exact hP
 · intro i _ hh; simp [f,b,hh]
 simp
lemma cloud1 : shine T 1 a x y=0:=by
 let p:= Geometry.invS
 have hf:p.act a= -a:=by ext i; simp [p,Signed.act,Geometry.invS]
 have hr:= act_lift H P x y p a 1 (by omega) (fun i hi=>by interval_cases i; exact cloud0 H P x y a);rw [hf] at hr
 change shine T 1 (-a) x y=(-1)*(-1)*shine T 1 a x y at hr -- rfl?
 have ht: shine T 1 (-a) x y= -shine T 1 a x y:=by unfold shine recital; simp_rw [dial_opposite, pow_one,mul_neg]; exact tsum_neg ..
 rw [ht] at hr;linarith
lemma cloud2 : ∑ i:Axis,shine T 2 a x (i,j)*a i=0:=by
 let rideM (i:ℕ):= shine T i a; have hp:= neutral H P x a j 3 (by omega)
 have ht (i:Axis) : ∑ k∈ Finset.range (3+1), rideM k x (i,j)*(a i^(3-k)*(↑((3:ℕ).choose k):ℝ))= 3*(rideM 2 x (i,j)*a i)+rideM 3 x (i,j):=by
    unfold rideM; simp_rw [Finset.sum_range_succ]; rw [cloud0 H P,cloud1 H P]; norm_num [Nat.choose]; ring
 change _ = ∑ i:Axis,∑ k∈ Finset.range (3+1),rideM k x (i,j)*_ at hp -- try
 simp_rw [ht] at hp; rw [sum_add_distrib,← mul_sum] at hp;change ∑ i:Axis,rideM 3 x (i,j)= _ at hp; change ∑ i:Axis,rideM 2 x (i,j)*a i=0;linarith
end Rules
end YM.RegulatorIR.Pupil
