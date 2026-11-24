import YM.MSbar.Loop.Kinetic

/-! Commutator `[R, lap P]` on each finite support, not an extra assumption on the Fourier grids.
Prove in terms of symbol functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar
open Function Finsupp Super Finset
open scoped BigOperators Classical
namespace Super.Transport
variable {T:Type*}{p:T→Bit} {d:Bit}(X:Transport p d) (a:T × T)
lemma left (c:ℂ): X.leftCarry a c=c • X.leftCarry a 1:= by
   unfold leftCarry; rw [Finset.smul_sum];simp_rw [one_mul, ← smul_eq_mul (a:=c),smul_single] -- rhs
lemma right (c:ℂ): X.rightCarry a c=c • X.rightCarry a 1:= by
   unfold rightCarry; rw [Finset.smul_sum,mul_one]; apply Finset.sum_congr rfl; intro b hb; rw [smul_single,smul_eq_mul]; ring_nf
def born_stock : Stock T→ₗ[ℂ] Stock T := - Finsupp.linearCombination ℂ (fun a=> X.leftCarry a 1+X.rightCarry a 1)
lemma computed (P:Stock T): X.born P = X.born_stock P:=by
    unfold born born_stock; rw [LinearMap.neg_apply]; congr! 1
    unfold Finsupp.linearCombination; dsimp [Finsupp.sum,LinearMap.smulRight]; apply Finset.sum_congr rfl; intro x hx; rw [X.left x (P x),X.right x (P x),smul_add]
lemma easy (c:ℂ): X.born (Finsupp.single a c) = -(X.leftCarry a c+X.rightCarry a c):= by rw [X.computed,born_stock,LinearMap.neg_apply,Finsupp.linearCombination_single, X.left a c, X.right a c,smul_add]
lemma bank {ι : Type*} (f:ι→Stock T) (P : Finset ι) : X.born (∑ i∈P,f i)=∑ i∈P,X.born (f i):=by simp_rw [X.computed];exact map_sum ..
end Super.Transport
namespace Loops
variable {C M: Type*} [AddCommGroup M] {p:C→Bit} {I:Finset C} {R:Row C M} {f : Amps C M} {B A:Line C M} {k:Bit}
def shift (p:C→Bit) (I:Finset C) (k:Bit)(R:Row C M)(B:Line C M) : Line C M := fun a b t=>
    -(∑ c∈I,(B c b t*R c a t + sign k (p a) * B a c t * R c b (-t))) -- sign: scope inside!
private lemma left (h:Kinetic p I k R) (a b:C)(t:M)(v:ℂ) : (rotate h).leftCarry ((a,t),(b,-t)) v= ∑ x∈I,Finsupp.single ((x,t),(b,-t)) (v*R a x t):=by
    unfold Transport.leftCarry; let L:=Finsupp.linearCombination ℂ (fun x:Wave C M=>Finsupp.single (x,(b,-t)) v)
    change (∑ x∈(linear I R (a,t)).support, Finsupp.single (x,(b,-t)) (v*linear I R (a,t) x))=_
    calc
     _ = L (linear I R (a,t)):= by unfold L Finsupp.linearCombination; dsimp [Finsupp.sum]; apply Finset.sum_congr rfl; intro x _; rw [smul_single,smul_eq_mul,mul_comm]
     _ = _:= by unfold linear; rw [map_sum]; apply Finset.sum_congr rfl; intro x _; simp only [L,Finsupp.linearCombination_single]; rw [smul_single,smul_eq_mul,mul_comm]
private lemma right (h:Kinetic p I k R) (a b:C)(t:M)(v:ℂ) : (rotate h).rightCarry ((a,t),(b,-t)) v= ∑ x∈I,Finsupp.single ((a,t),(x,-t)) (sign k (p a)*v*R b x (-t)):=by
    unfold Transport.rightCarry; let L:=Finsupp.linearCombination ℂ (fun x:Wave C M=>Finsupp.single ((a,t),x) (sign k (p a)*v))
    change (∑ x∈(linear I R (b,-t)).support, Finsupp.single ((a,t),x) (sign k (p a)*v*linear I R (b,-t) x))=_
    calc
     _ = L (linear I R (b,-t)):= by unfold L Finsupp.linearCombination; dsimp [Finsupp.sum]; apply Finset.sum_congr rfl; intro x _; rw [smul_single,smul_eq_mul,mul_comm]
     _ = _:= by unfold linear; rw [map_sum]; apply Finset.sum_congr rfl; intro x _; simp only [L,Finsupp.linearCombination_single]; rw [smul_single,smul_eq_mul,mul_comm]
private lemma flip3 (F:C→C→C→Stock (Wave C M)):
    ∑ x∈I,∑ y∈I,∑ z∈I,F x y z= ∑ z∈I,∑ y∈I,∑ x∈I,F x y z:=by
    rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (f:=fun x z=>F x _ z)]; rw [Finset.sum_comm]
lemma bank (h: Kinetic p I k R) (K:Finset M): (rotate h).born (Stocking I K B)=Stocking I K (shift p I k R B):= by
   unfold Stocking; simp_rw [Transport.bank,Transport.easy, left h,right h]; refine Finset.sum_congr rfl (fun t _=> ?_); unfold shift
   simp only [← singleAddHom_apply,map_neg,map_sum,map_add,Finset.sum_add_distrib,Finset.sum_neg_distrib]
   congr! 2
   · exact flip3 _
   refine Finset.sum_congr rfl fun j hj=> Finset.sum_comm
end Loops
end YM.MSbar
