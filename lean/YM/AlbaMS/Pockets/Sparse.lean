import YM.AlbaMS.Super.Plex
import Mathlib.Data.Fintype.Order

/-!
Stack of orders in marks & coupling. Use one true commutative ring incl for
fermion algebra. Ring comparisons vs disjoint-support labels on actual reads
through finite stencils. Kernels can be arbitrary rank, possibly infinite
coefficient types. Real columns at ε pole aren't of this form (spent in
meromorphic calculation), statements for regulator comparison here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι K W R S : Type*} [Fintype K] [AddCommMonoid W] [CommRing R] [CommRing S]

/-- portal into additive ordered tag universe: meet from below if available.
Including origin & height. -/
structure Ladder (K W : Type*) [AddCommMonoid W] where
  passage : K→ W
  room : Injective passage
  ort : K
  begin_ : passage ort=0
  down {a b : W}{i:K}: a+b=passage i → a∈ range passage
  d : K→ℕ
  d0 : d ort=0
  lift {i : K} : i≠ort→0<d i
  raises {i j k : K} : passage i+passage j=passage k → d i+d j=d k
namespace Ladder
variable (P : Ladder K W) (i j k : K)
def cut (i j k : K) := P.passage i+P.passage j=P.passage k
def sums (k : K): Finset (K × K) := Finset.univ.filter (fun x=> P.cut x.1 x.2 k)
omit [Fintype K] in
lemma switch : P.cut i j k ↔ P.cut j i k := by unfold cut;rw [add_comm]
omit [Fintype K] in
@[simp] lemma cut_zero : P.cut P.ort j k ↔ j=k:=by unfold cut;rw [P.begin_,zero_add,P.room.eq_iff]
omit [Fintype K] in
@[simp] lemma zero_cut : P.cut i P.ort k ↔ i=k:=by rw [P.switch,P.cut_zero]
lemma member (x) : x∈P.sums k ↔ P.cut x.1 x.2 k:=by simp [sums]
omit [Fintype K] in
lemma raises' {i j k : K} (h:P.cut i j k): P.d k=P.d i + P.d j:=(P.raises h).symm
end Ladder
-- synonym data points, addition transparent; later assign conv multiplication. Prefer structured type to avoid Pi mul diamond
@[ext] structure Tags (D : Ladder K W)(R : Type*) where
  val : K→ R
namespace Tags
variable {D : Ladder K W} (F G H : Tags D R) (i j k : K)
instance : FunLike (Tags D R) K R := ⟨Tags.val,fun _ _ he=>Tags.ext he⟩
instance : Add (Tags D R):= ⟨fun F G=>⟨F.val+G.val⟩⟩
instance : Neg (Tags D R):= ⟨fun F=>⟨-F.val⟩⟩
instance : Sub (Tags D R):= ⟨fun F G=>⟨F.val-G.val⟩⟩
instance : Zero (Tags D R):= ⟨⟨0⟩⟩
instance {S : Type*}[SMul S R] : SMul S (Tags D R):= ⟨fun g F=> ⟨g • F.val⟩⟩
instance : AddCommGroup (Tags D R):= Function.Injective.addCommGroup Tags.val (fun _ _ he=> Tags.ext he) rfl (fun _ _=>rfl) (fun _=>rfl ) (fun _ _=>rfl ) (fun _ _=>rfl ) (fun _ _=>rfl)
omit [Fintype K] [CommRing R] in
lemma same (h:∀ i,F i=G i):F=G:=Tags.ext (funext h)
omit [Fintype K] in
@[simp] lemma read0 : (0:Tags D R) i=0:=rfl
omit [Fintype K] in
@[simp] lemma read_plus : (F+G) i=F i+G i:=rfl
omit [Fintype K] in
@[simp] lemma read_minus : (F-G) i= F i-G i:=rfl
omit [Fintype K] in
@[simp] lemma read_neg : (-F) i= -F i:=rfl
omit [Fintype K] in
@[simp] lemma read_pay (c:R) : (c • F) i=c*F i:=rfl
omit [Fintype K] in
@[simp] lemma read_tick (c:ℕ): (c • F) i= c • F i:=rfl
instance : Mul (Tags D R):= ⟨fun F G=> ⟨fun k=>∑ i : K,∑ j:K,if D.cut i j k then F i* G j else 0⟩ ⟩

def gem (D : Ladder K W)(i:K)(c:R): Tags D R:=⟨fun x=> if i=x then c else 0⟩
omit [Fintype K] in
lemma gem_read (c:R) : gem D i c j=if i=j then c else 0:=rfl
lemma mul_read : (F*G) k=∑ i : K,∑ j:K,if D.cut i j k then F i* G j else 0:=rfl
lemma product_cell : (F*G) k=∑ x∈D.sums k,F x.1*G x.2:=by rw [mul_read,Ladder.sums,Finset.sum_filter,Fintype.sum_prod_type]
private lemma gem_prod (c:R) : gem D D.ort c * F=c • F:=by
  apply same; intro i; rw [mul_read]; simp_rw [gem_read, ite_mul, zero_mul]
  rw [Finset.sum_eq_single D.ort]; simp; intro j _ he; simp [Ne.symm he]; simp
private lemma mul_addG : F*(G+H)= F*G+ F*H := same _ _ (fun i => by simp_rw [read_plus,product_cell, read_plus,mul_add,Finset.sum_add_distrib]) -- simp twice?
private lemma flipG : F*G=G*F:= by
  apply same; intro k; rw [mul_read,mul_read,Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; rw [D.switch]; exact ite_congr rfl (fun _=> mul_comm ..) (fun _=>rfl)
private lemma nests {i j k l}(x:R): (∑ a:K, if D.cut a k l then if D.cut i j a then x else 0 else 0) = ∑ a:K, if D.cut i a l then if D.cut j k a then x else 0 else 0:= by
  by_cases he:D.passage i+D.passage j+D.passage k = D.passage l
  · obtain ⟨a,ha⟩:= D.down he; rw [add_assoc,add_comm (D.passage i)] at he
    obtain ⟨b,hb⟩:= D.down he
    rw [Finset.sum_eq_single a,Finset.sum_eq_single b];
    · have h:D.cut a k l:=by unfold Ladder.cut; rw [ha];rw [add_assoc, add_comm (D.passage i), he] -- fix
      have hh:D.cut i b l:=by unfold Ladder.cut; rw [hb,add_comm];exact he
      rw [if_pos h,if_pos hh,if_pos (show D.cut i j a from ha.symm),if_pos (show D.cut j k b from hb.symm)]
    · intro j hj hjb; split_ifs with hs hp; exact False.elim (hjb (D.room (hp.symm.trans hb.symm))); all_goals rfl
    · simp
    · intro j hj hja; split_ifs with hs hp; exact False.elim (hja (D.room (hp.symm.trans ha.symm))); all_goals rfl
    simp
  have h a : ¬(D.cut a k l ∧ D.cut i j a):=by unfold Ladder.cut; intro ⟨hj,hk⟩; exact he (by rw [hk,hj])
  have H a : ¬(D.cut i a l ∧ D.cut j k a):=by unfold Ladder.cut; intro ⟨hj,hk⟩; exact he (by rw [add_assoc,hk,hj])
  refine (Finset.sum_eq_zero (s:=Finset.univ) (fun a _=> by split_ifs with hj hk; exact False.elim (h a ⟨hj,hk⟩); all_goals rfl)).trans ((Finset.sum_eq_zero fun a _=> by split_ifs with hj hk; exact False.elim (H a ⟨hj,hk⟩); all_goals rfl).symm)
private lemma associate : F*G*H=F*(G*H):= by
  apply same; intro l; simp_rw [mul_read, Finset.sum_mul,ite_mul,zero_mul,Finset.mul_sum,mul_ite,mul_zero,mul_assoc]
  let A z h i j:=if D.cut z h l then if D.cut i j z then F i*(G j* H h) else 0 else 0; let B i z j k:= if D.cut i z l then if D.cut j k z then F i*(G j*H k) else 0 else 0
  have hh (f:K→ R)(p : Prop) [Decidable p] : ite p (∑ a:K,f a) 0=∑ a:K,ite p (f a) 0:=by by_cases he:p<;>simp [he]
  simp_rw [hh]; change (∑ z:K,∑ h:K,∑ i:K,∑ j:K,A z h i j)=∑ i:K,∑ z:K,∑ j:K,∑ k:K,B i z j k
  simp_rw [Finset.sum_comm (f:=fun h:K=>fun i:K=>∑ j:K,A _ h i j)] -- swap h,i
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Finset.sum_comm]; rw [Finset.sum_comm (f:=fun z j=>∑ k:K,B i z j k)];
  simp_rw [Finset.sum_comm (f:=fun z=>fun j : K=> A z _ i j)]; rw [Finset.sum_comm];
  refine Finset.sum_congr rfl fun j _=>?_ ; rw [Finset.sum_comm (f:=fun z k=> B i z j k)]; exact Finset.sum_congr rfl fun _ _=> nests _
omit [Fintype K] in
@[simp] lemma pay_gems (c d:R): c • gem D i d=gem D i (c*d):=by apply same; intro x; by_cases h:i=x<;>simp [h,gem_read]
omit [Fintype K] in
@[simp] lemma gem_add (c d:R): gem D i (c+d)= gem D i c+gem D i d:=by apply same;intro x; by_cases h:i=x<;>simp [h,gem_read]
omit [Fintype K] in
@[simp] lemma gem_nil : gem D i (0:R)=0:=by apply same;intro x;simp [gem_read]
omit [Fintype K] in
lemma pay1 : (1:R) • F=F:=same _ _ fun i=> by simp
instance : CommRing (Tags D R) where
  one:=gem D D.ort 1
  mul_assoc:=associate
  mul_comm:=flipG
  left_distrib:=mul_addG
  right_distrib F G H:=by rw [flipG,mul_addG,flipG H F,flipG H G]
  one_mul F:=(gem_prod ..).trans (pay1 F)
  mul_one F := (flipG ..).trans ((gem_prod ..).trans (pay1 F))
  mul_zero F:=same _ _ fun i=>by simp [mul_read]
  zero_mul F:=same _ _ fun i=>by simp [mul_read]
  natCast n:=gem D D.ort (n:R)
  intCast n:=gem D D.ort (n:R)
  natCast_zero := by change gem _ _ _=0; simp
  natCast_succ n:=by change gem D D.ort (((n+1:ℕ)):R)=_; rw [Nat.cast_add,Nat.cast_one,gem_add]; rfl
  intCast_ofNat n:=by change gem _ _ _=gem _ _ _; rw [Int.cast_natCast]
  intCast_negSucc n:= by
    change gem _ _ _= - gem _ _ _; apply eq_neg_of_add_eq_zero_left; rw [← gem_add]; simp
lemma pay_left (c:R): gem D D.ort c * F=c • F:= gem_prod ..
def inject (D : Ladder K W) : R→+*Tags D R where
  toFun := gem D D.ort
  map_one':=rfl
  map_zero':=gem_nil _
  map_add':=gem_add _
  map_mul' _ _:= Eq.symm ((gem_prod ..).trans (pay_gems ..))
instance [Algebra S R]: Algebra S (Tags D R) where
  algebraMap:= (inject D).comp (algebraMap S R)
  commutes' s F:= mul_comm _ F
  smul_def' s F:= by change s • F=gem _ _ _*F;rw [gem_prod];apply same;intro i;exact Algebra.smul_def ..
lemma mult_left (c:R): inject D c * F=c • F:= gem_prod ..
lemma mult_read (c:R): (inject D c*F) i=c*F i:= by rw [mult_left];rfl

def peek (i:K): Tags D R→+ R where
  toFun F:= F i
  map_zero':=rfl
  map_add' _ _:=rfl
def pixel (D : Ladder K W)(i:K): R→+Tags D R where
  toFun:=gem D i
  map_zero':=gem_nil _
  map_add':=gem_add _
@[simp] lemma peek_apply : peek i F= F i:=rfl
@[simp] lemma pixel_at (c:R): pixel D i c=gem D i c:=rfl
end Tags
end YM.MSBar.Bric
