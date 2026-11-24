import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import YM.MS.Book.Pairs

/-!
Bilinear algebra for lift of identities through both perturbative order and marker index.
Mark message always in original finite-set indices. The spectrum of engineering dimensions does not matter.
We intentionally restrict all assertions within the even part (including the primitive/wave-adjusted
insertions of ghost number zero). Evenness, time evolution and parity will be supplied explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Function Finset Book.Convolve
variable {E F H A I J Z W:Type}
  [AddCommGroup E][Module ℂ E] [AddCommGroup F][Module ℂ F] [AddCommGroup H][Module ℂ H]

structure SplitP (I:Type) where
    origin : I
    grade : I→ℕ
    zeroC i: grade i=0 ↔ i=origin
    pieces:I→Finset ( I×I )
    quiet x y:(origin,y)∈ pieces x↔ x=y
    pays {x u v}: (u,v)∈pieces x→ grade u+grade v=grade x
    sym {x u v} : (u,v)∈pieces x↔(v,u)∈ pieces x
    trip (E:Type)[AddCommMonoid E](x:I)(F:I→I→I→E): (∑ v∈ pieces x,∑ u∈ pieces v.2,F v.1 u.1 u.2)=∑ v∈pieces x,∑ u∈ pieces v.1,F u.1 u.2 v.2

abbrev Linear (E F: Type)[AddCommGroup E][ Module ℂ E ][AddCommGroup F][Module ℂ F]:= E →ₗ[ℂ] F
abbrev Bil (E F H: Type)[AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F][AddCommGroup H][Module ℂ H]:= E →ₗ[ℂ] F →ₗ[ℂ] H
variable (P:SplitP I)
namespace SplitP
lemma home : P.pieces P.origin={ ( P.origin,P.origin ) }:= by
    ext p; rcases p with ⟨p,q⟩; have hz:P.grade P.origin=0:= (P.zeroC P.origin).mpr rfl; constructor; · intro h; obtain H:= P.pays h; exact Finset.mem_singleton.mpr (Prod.ext ((P.zeroC _).mp (by dsimp; omega)) ((P.zeroC _).mp (by dsimp; omega)))
    intro h; rw [ Finset.mem_singleton.mp h ]; exact ( P.quiet .. ).mpr rfl
omit [Module ℂ E] in
lemma also (L:I→I→E)(x:I): ∑ i∈P.pieces x,L i.1 i.2= ∑ i∈P.pieces x,L i.2 i.1:= by
   classical
   apply Finset.sum_bij (fun i _=>i.swap) (fun b hb=> P.sym.mp hb) (fun a _ b _ h=> Prod.swap_injective h) (fun b hb=>⟨ b.swap,P.sym.mp hb,rfl⟩); exact fun _ _=>rfl
abbrev Lift (L:Bil E F H) : Bil (I→E) (I→ F) ( I→ H ):= {
   toFun F:= {
       toFun X:= fun i=>∑ v∈P.pieces i, L (F v.1) (X v.2)
       map_add' a b:= by funext i; simp_rw [Pi.add_apply,map_add, Finset.sum_add_distrib]
       map_smul' a b:= by funext i; simp_rw [Pi.smul_apply,map_smul, Finset.smul_sum]; rfl }
   map_add' a b:= by apply LinearMap.ext; intro H; funext i; simp [Finset.sum_add_distrib]
   map_smul' a b:= by apply LinearMap.ext; intro H; funext i; simp [ Finset.smul_sum ]
}
lemma loan (L:Bil E F H)(f:I→E)(g:I→F)(i:I): P.Lift L f g i=∑ j∈ P.pieces i, L (f j.1) (g j.2):=rfl
def refineV (x:E): I→E:=open Classical in fun i=>if i=P.origin then x else 0 -- replace
lemma tile (L:Bil E F H)(x:E)(v:I→F): P.Lift L ( P.refineV x ) v = fun i=> L x (v i):= by
   classical
   funext i; rw [ loan, Finset.sum_eq_single_of_mem (P.origin,i) (( P.quiet i i ).mpr rfl) ]; · dsimp only; rw [ refineV, if_pos rfl ]
   intro j hj he; have hz : j.1≠ P.origin:= by intro he'; exact he (Prod.ext he' (Eq.symm ((P.quiet i j.2).mp (show ( P.origin,j.2 )∈P.pieces i from he' ▸ (show (j.1,j.2)∈P.pieces i from hj)))))
   rw [ refineV,if_neg hz,map_zero ]; rfl
lemma tm (L: Bil E F H)(x:F)(v:I→E): P.Lift L v (P.refineV x)=fun i=> L (v i) x:= by
   rw [ show P.Lift L v (P.refineV x)=P.Lift L.flip ( P.refineV x ) v from funext (fun i=> P.also (fun j k=>L (v j) (P.refineV x k)) i), tile ]; rfl

end SplitP

def allIndex (M:Submodule ℂ E)(I:Type): Submodule ℂ ( I→ E ):= Submodule.pi Set.univ fun _=> M
lemma universe0 (M:Submodule ℂ E){f:I→E}: f∈ allIndex M I ↔ ∀ i,f i ∈ M:= by simp [allIndex,Submodule.mem_pi]
lemma stays0 {M:Submodule ℂ E}{L:Submodule ℂ F}{H':Submodule ℂ H}(A:Bil E F H)(u:I→E)(v:I→F)(h:∀ i,i∈ M→ ∀ j,j∈L→ A i j∈H')( he: u∈allIndex M I)(hv:v∈allIndex L I): P.Lift A u v∈ allIndex H' I:= (universe0 H').mpr (fun _=> H'.sum_mem (fun _ _=> h _ (he _ (Set.mem_univ _)) _ (hv _ (Set.mem_univ _))))
-- Guard-based commutative algebra
structure Actors (E:Type)[AddCommGroup E][Module ℂ E] where
   guard : Submodule ℂ E
   core : Bil E E E
   unit : E
   holds : unit∈guard
   close : ∀ u∈guard,∀ v∈guard,core u v∈guard
   identityK : ∀ u,core unit u=u
   identityR : ∀ u,core u unit=u
   turns : ∀ u∈guard,∀ v∈guard, core u v=core v u
   star_a : ∀ u v w,core (core u v) w=core u (core v w)
namespace Actors
variable (M:Actors E)
local infix:70 " ⋆ " => M.core
lemma lifted_pin (x: I→ E): P.Lift M.core ( P.refineV M.unit ) x=x:= by rw [P.tile]; simp_rw [M.identityK] -- no hv
lemma lifted_t {x y:I→E}(hp:x∈allIndex M.guard I)(hv:y∈allIndex M.guard I): P.Lift M.core x y=P.Lift M.core y x:= by funext i; rw [P.loan,P.loan,P.also (fun j k=> x j ⋆ y k)]; exact Finset.sum_congr rfl fun j _=> M.turns _ (hp _ ( Set.mem_univ _ )) _ (hv _ (Set.mem_univ _))
lemma lifted_a (x y z:I→E):P.Lift M.core ( P.Lift M.core x y) z=P.Lift M.core x (P.Lift M.core y z):= by funext i; simp_rw [P.loan,map_sum,LinearMap.sum_apply,M.star_a]; exact (P.trip E i (fun i j k=> x i ⋆ (y j ⋆ z k))).symm -- assoc simp nat

def stack : Actors (I→ E):={
   guard:= allIndex M.guard I
   core:= P.Lift M.core
   unit:= P.refineV M.unit
   holds:= (universe0 _).mpr fun i=>by unfold SplitP.refineV; split; exact M.holds; exact M.guard.zero_mem
   close:= fun i h j he=> stays0 P M.core i j M.close h he
   identityK:=fun i=> M.lifted_pin P i
   identityR:=fun i=> by rw [ P.tm ]; simp_rw [M.identityR]
   turns:=fun _ hx _ ht=> M.lifted_t P hx ht
   star_a:= fun u v w=> M.lifted_a P u v w }
end Actors
end YM.MS.Puff
