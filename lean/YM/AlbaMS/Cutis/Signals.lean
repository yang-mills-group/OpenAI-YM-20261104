import YM.AlbaMS.Cutis.Starlight
/-!
# Coherent stencil comparisons through linear pass on shift-preserving words

A constant-direction derivative can be absolute, not necessarily a basis pick.
If all mixed shift words vanish after stronger projection pass, prove equality on
all readings. This avoids signs assuming momentum props no zero in gauged metric.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Finset Function
open scoped BigOperators Classical
variable {ι κ R : Type*} [CommRing R]{ρ:ι→Bool}{σ:κ→Bool}{P T : ι→κ→R}{L M : Coil ρ R}{s:Finset ι}

def drift (s:Finset ι)(P T:ι→κ→R)(x:κ): Module.End R (Coil ρ R):= drip s T x-drip s P x
lemma duel (h: Routes ρ σ P)(H:Routes ρ σ T)(x y:κ): drift s P T x (drip s P y L)= sting (σ y && σ x) (drip s P y (drift s P T x L)):=by
  have he : drip s T x (drip s P y L)=sting (σ y && σ x) (drip s P y (drip s T x L)):=by
    simp_rw [drip_apply, map_sum,map_smul, Finset.smul_sum, sting_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_
    by_cases hv:P i y=0; · simp [hv]
    by_cases hu:T j x=0; · simp [hu]
    rw [DD, h _ _ hv,H _ _ hu]; cases σ y<;>cases σ x<;> simp [smul_comm (P i y)]
  unfold drift; rw [LinearMap.sub_apply,he,drip_x P h,LinearMap.sub_apply,map_sub]; cases σ y<;>cases σ x<;> simp [sub_eq_add_neg, add_comm]

def roots (s : Finset ι)(P T:ι→κ→R): List κ→ Module.End R (Coil ρ R)
| []=>LinearMap.id
| x::l=> roots s P T l ∘ₗ drift s P T x
lemma roots_out (l : List κ)(x:κ): roots s P T (x::l) L=roots s P T l (drift s P T x L):=rfl
lemma bolts (h:Routes ρ σ P)(H:Routes ρ σ T)(l:List κ)(x:κ) : roots s P T l (drip s P x L)= sting (σ x && band σ l) (drip s P x (roots s P T l L)):= by
  induction l generalizing L with|nil=> cases σ x<;>rfl | cons i l ih=>
    rw [roots_out,duel h H, roots_out]; have he:= ih (L:=drift s P T i L); cases hu:σ i<;>cases hz:σ x<;> cases hb:band σ l<;> simp [hu,hz,hb] at he ⊢ <;> simp [he]

variable (P T s)
def Flair (h:Routes ρ σ P)(U:Coil ρ R) := ∀ x v, shot s P h (roots s P T v (drift s P T x U))=0
namespace Flair
variable {P T s}{h:Routes ρ σ P}
lemma low (u:Flair P T s h L)(x:κ): shot s P h (drift s P T x L)=0:=u x []
lemma rolled (u:Flair P T s h L)(t:κ): Flair P T s h (drift s P T t L):=fun x v=> u t (x::v)
lemma Aways (u:Flair P T s h L)(H: Routes ρ σ T)(x:κ) : Flair P T s h (drip s P x L):=by
  intro y v; rw [← roots_out,bolts h H]; cases σ x && band σ (y::v)<;> simp only [sting_true,sting_false,map_neg,← shot_D P h,roots_out,u y v,map_zero,neg_zero]
lemma add (u:Flair P T s h L)(v:Flair P T s h M): Flair P T s h (L+M):=by intro x w; simp only [map_add, u x w,v x w,add_zero]
lemma Terr (u:Flair P T s h L)(H:Routes ρ σ T)(x:κ): Flair P T s h (drip s T x L):= by rw [show drip s T x L=drip s P x L+drift s P T x L from (add_sub_cancel ..).symm]; exact (u.Aways H x).add (u.rolled x) -- add_sub wrong
lemma project (u:Flair P T s h L)(H:Routes ρ σ T) : shot s P h L=shot s T H L:= by
  ext l; induction l generalizing L with| nil=>rfl|cons x l ih=>
    rw [← D_read, ← D_read (F:=shot s T H _), shot_D, shot_D, ← ih (u.Terr H x)]; have hh:=u.low x; rw [drift,LinearMap.sub_apply,map_sub,sub_eq_zero] at hh; rw [hh]
end Flair
end YM.MSBar.Bric.Coil
