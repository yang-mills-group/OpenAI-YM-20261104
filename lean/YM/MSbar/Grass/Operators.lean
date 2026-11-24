import YM.MSbar.Grass.Associative
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite Laplacian and cross-contraction algebra. All sums include multiplicity 1/2; no
symmetry assumption needed for these operators apart from pace. Left derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset
open scoped BigOperators Classical
variable {T:Type*}{p:T→Bit} {a b:T} {f g h : Series T} {d e c j k : Bit}
abbrev Order (T:Type*) := Series T→ₗ[ℂ] Series T
abbrev Double (T:Type*) := Series T →ₗ[ℂ] Order T
abbrev Stock (T:Type*) := (T×T)→₀ℂ

def twice (a:T×T) : Order T:= (field a.2).comp (field a.1)
def laps (K:Stock T) : Order T:= ∑ a∈K.support,(K a/2) • twice a
def member (p:T→Bit)(d:Bit)(a:T×T) : Double T:=
    sign (p a.2) (p a.1+d) • ((merge p).comp (field a.1)).compl₂ (field a.2) +
    sign (p a.1) d • ((merge p).comp (field a.2)).compl₂ (field a.1)
def pairs (p:T→Bit)(d:Bit)(K:Stock T) : Double T:= ∑ a∈K.support,(K a/2) • member p d a
lemma price_loop (K:Stock T) (f) : laps K f=∑ a∈K.support,(K a/2) • field a.2 (field a.1 f):=by simp [laps,twice,LinearMap.sum_apply]
lemma member_pair (x:T×T) : member p d x f g=sign (p x.2) (p x.1+d) • join p (field x.1 f) (field x.2 g)+sign (p x.1) d • join p (field x.2 f) (field x.1 g):=rfl
lemma price_pair (K:Stock T) : pairs p d K f g=∑ a∈K.support,(K a/2) • (member p d a f g):=by simp [pairs,LinearMap.sum_apply]

variable {K H : Stock T}
abbrev Grade (p:T→Bit) (k:Bit) (K:Stock T) := ∀ a∈K.support,p a.1+p a.2=k
namespace Grade
lemma homogeneous (he : Grade p k K) (h : Homogeneous p d f) : Homogeneous p (k+d) (laps K f):=by
   rw [price_loop]; apply Homogeneous.sum; intro x hx
   have hh : p x.2+(p x.1+d)=k+d:= by rw [← add_assoc,add_comm (p x.2),he _ hx]
   exact hh ▸ ((h.derives x.1).derives x.2).scaling _
lemma loss (he : Grade p k K)(hh : Homogeneous p d f)(hp : Homogeneous p e g) : Homogeneous p (k+d+e) (pairs p d K f g):=by
   rw [price_pair]; apply Homogeneous.sum; intro x hx; rw [member_pair,← he x hx]; apply Homogeneous.scaling
   apply Homogeneous.add
   · have h:(p x.1+d)+(p x.2+e)=p x.1+p x.2+d+e:=by abel
     rw [← h]; exact ((hh.derives x.1).join (hp.derives x.2)).scaling _
   have h:(p x.2+d)+(p x.1+e)=p x.1+p x.2+d+e:=by abel
   rw [← h]; exact ((hh.derives x.2).join (hp.derives x.1)).scaling _

lemma product (he : Grade p k K)(hf : Homogeneous p d f)(g): laps K (join p f g)=
    join p (laps K f) g+ sign k d • join p f (laps K g)+ pairs p d K f g:=by
    simp_rw [price_loop,price_pair, join_sum_left,join_sum_right, join_scale_left,join_scale_right,Finset.smul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x hx; rw [← he x hx,member_pair,product_rule hf.shape g,map_add,map_smul,product_rule (hf.derives _).shape g,product_rule hf.shape]
    rw [sign_add]; ext v; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
lemma comm_field (he : Grade p k K)(hf:Homogeneous p d f)(a:T): field a (laps K f)=sign (p a) k • laps K (field a f):=by
    simp_rw [price_loop,map_sum,map_smul, Finset.smul_sum]; refine Finset.sum_congr rfl fun x hx=> ?_
    rw [(hf.derives x.1).comm x.2 a,hf.comm x.1 a,map_smul,←he x hx,sign_add_right,braid (p x.2),braid (p x.1)]; simp_rw [smul_smul]; congr! 1; ring
lemma id_loop (he : Grade p k K)(h: Grade p j H)(hf:Homogeneous p d f) : laps H (laps K f)=sign j k • laps K (laps H f):=by
    rw [price_loop H,price_loop H f]; simp_rw [map_sum,map_smul,Finset.smul_sum]
    refine Finset.sum_congr rfl fun x hx=> ?_; rw [he.comm_field hf,map_smul,he.comm_field (hf.derives _),← h x hx,sign_add]; simp_rw [smul_smul]; congr! 1; ring
end Grade
end YM.MSbar.Super
