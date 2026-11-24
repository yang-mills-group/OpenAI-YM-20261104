import YM.OPE.Compatible.Karls.Elm
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
-- polynomial geometric sequences
variable {a b u v:ℝ}
def Rift (q:ℝ)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] : Module.End ℝ (ℕ→ E) where
   toFun f i:= f (i+1)-q • f i
   map_add' a b:=funext fun i=>by simp only [Pi.add_apply,smul_add]; abel
   map_smul' c a:=funext fun i=>by simp only [Pi.smul_apply,smul_sub, RingHom.id_apply];rw [smul_comm c q]
variable {p z:ℕ→E}
def Sky (q:ℝ)(n:ℕ)(p:ℕ→E):Prop:=(Rift q E^n) p=0
lemma Sky.first (hp:Sky q m (Rift q E p)):Sky q (m+1) p:=by unfold Sky; rw [pow_succ,Module.End.mul_apply];exact hp
lemma Sky.more (hp:Sky q k p)(h:k≤m):Sky q m p:=by obtain ⟨x,rfl⟩:=Nat.exists_eq_add_of_le h; unfold Sky; rw [Nat.add_comm,pow_add,Module.End.mul_apply,show (Rift q E^k) p=0 from hp,map_zero] -- obtain orientation
lemma Sky.sum (hp:Sky q k p)(hv:Sky q k z):Sky q k (p+z):=by unfold Sky; rw [map_add,show (Rift q E^k) p= _ from hp, show (Rift q E^k) z= _ from hv,add_zero]
lemma Sky.sub (hp:Sky q k p)(hv:Sky q k z):Sky q k (p-z):=by unfold Sky; rw [map_sub,show (Rift q E^k) p= _ from hp, show (Rift q E^k) z= _ from hv,sub_zero]
lemma Sky.real (h:Sky q k p)(s:ℝ):Sky q k (s • p):=by unfold Sky; rw [map_smul, show (Rift q E^k) p= _ from h, smul_zero]
lemma Sky.zero (q:ℝ)(k:ℕ): Sky q k (0:ℕ→E):=map_zero _
lemma Sky.geometric (h: Thick q p)(v:Rift q E p=0):p=0:=by
    have hv:Run (flint q) p 0:=by intro i; have hh: p (i+1)-q • p i=0:=congr_fun v i; exact (sub_eq_zero.mp hh).trans (add_zero _).symm
    obtain ⟨⟨t,h,hp,H,F⟩⟩:=h; have hh:= det h hp hv F; ext i; induction i with | zero=>exact hh| succ i ih=> rw [hv, ih]; simp
lemma Sky.blind (hp:Sky q k p)(ht:Thick q p):p=0:=by induction k generalizing p with
   | zero=> exact hp
   | succ k ih=>
       unfold Sky at hp; rw [pow_succ,Module.End.mul_apply] at hp; refine Sky.geometric ht (ih hp ?_); obtain ⟨⟨t,hv,hh,c,H⟩⟩:=ht; exact (Thick.hex ⟨_,H.forward.sub (H.tint q)⟩ hv hh)
open Quit.PriceZ
lemma skyStem (e:ℕ)(P:E→L[ℝ] E)(X:Dice E)(n m:ℕ)(h:n+m ≤ e) (p q:E)(hp:(Ux P a ^n) p=0)(hq:(Ux P b^m) q=0): Sky (a*b) e fun i=> X (tale P p i) (tale P q i):=by
   induction e generalizing n m p q with
   | zero=>
         have hh:p=0:=by rw [show n=0 from by omega,pow_zero] at hp; exact hp
         subst p; suffices hx:(fun i=> X (tale P 0 i) (tale P q i))=0 by rw [hx]; exact Sky.zero ..
         ext i; rw [tale,map_zero,map_zero];rfl
   | succ e ih=>
      cases n
      · have hz:p=0:=by rw [pow_zero] at hp;exact hp
        subst p; suffices hx:(fun i=> X (tale P 0 i) (tale P q i))=0 by rw [hx];exact Sky.zero ..
        ext i; rw [tale,map_zero,map_zero];rfl
      cases m
      · have hz:q=0:=by rw [pow_zero] at hq; exact hq
        subst q; unfold tale; simp_rw [map_zero]; exact Sky.zero ..
      rename_i j k
      let t:=Ux P a p; let v:=Ux P b q; have ht:(Ux P a ^ j) t=0:= by rw [pow_succ,byway] at hp; exact hp
      have hv:(Ux P b ^ k) v=0:=by rw [pow_succ,byway] at hq; exact hq
      apply Sky.first; have h₁:= (ih j k (by omega) t v ht hv); have h₂:=(ih (j+1) k (by omega) p v hp hv).real a; have h₃:=(ih j (k+1) (by omega) t q ht hq).real b
      convert! (h₁.sum h₂|>.sum h₃) using 1; ext i; have he(r:E)(a:ℝ): tale P r (i+1)=a • tale P r i+tale P (Ux P a r) i:=by unfold tale; rw [pow_succ,byway,shiftUx,map_sub,map_smul];abel
      change X (tale P _ _) (tale P _ _)-_= _; rw [he p a, he q b]; simp only[map_add,map_smul,Pi.add_apply, Pi.smul_apply,add_apply,smul_apply,smul_eq_mul]; unfold t v; ring
end YM.OPE.Hark
