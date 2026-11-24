import YM.OPE.Compatible.Arch.Cred
import YM.MSbar.Tree.Resolvent
/-!
# Exact H one-form complex without scalar pin effect. Harmonics detected on full periodic cover and die on H.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra
open scoped Topology BigOperators ComplexConjugate Classical
variable {G:Gauge}{n:Side}
open RG Bid MSbar.Tree.Resolvent MSbar.Tree.Torus
namespace Streamer
abbrev Pack (j:ℕ)(n:Side) := TypeFace j × Site n -- obsolete
lemma gas_comm (n:Side): pre n * (grad n*(grad n)ᵀ)=grad n*(grad n)ᵀ*pre n:=by
     unfold MSbar.Tree.Resolvent.pre; rw [← realOf_mul',← realOf_mul,prom_mul,prom_adj]; simp only [grad,d_spectral,spectral_adj,spectral_mul]; congr 2; funext x; simp
def storm (u: form 1 n):Prop:=∀ i: Axis,(∑ j:Site n,u (j,coord i))=0
lemma pure_g (u:form 1 n)(hf: curl n*ᵥ u=0)(hs:storm u):∃ t:form 0 n,u= grad n*ᵥ t := by
      have he:= MSbar.Tree.Resolvent.reverse n; have hj : missing n*ᵥu=0:=by
           funext i; rcases i with ⟨i,a⟩; obtain ⟨k,rfl⟩:=axisEquiv.surjective a
           change ∑ j:Body 1 n,missing n (i,axisEquiv _) j*u j= _; rw [Fintype.sum_prod_type]; simp_rw [projected, ite_mul,zero_mul, show axisEquiv k=coord k from rfl]; simp [←Finset.mul_sum,hs k] -- wrong
      have hh:= congr_arg (fun A: Matrix (Body 1 n) (Body 1 n) ℝ=> A*ᵥu) he; rw [Matrix.sub_mulVec,Matrix.one_mulVec,hj,sub_zero,← Matrix.mulVec_mulVec] at hh
      rw [hessian,Matrix.add_mulVec,←Matrix.mulVec_mulVec,hf,Matrix.mulVec_zero,zero_add, Matrix.mulVec_mulVec,gas_comm] at hh
      simp only [← Matrix.mulVec_mulVec] at hh; exact ⟨_,hh.symm⟩
variable (H:Even n.val)
def hover {E:Type*}[AddGroup E](u:Limb H → E) : edgeV n→ E:= fun e=> if dir H e then -u (pathX H e) else u (pathX H e)
omit H in def Ell {E:Type*}[AddGroup E](u:edgeV n→ E) : Prop:= ∀ i:Kv,∀ e,u e=if (axisK i).flip e.2 then -u (ferry i e) else u (ferry i e)
lemma hoverEll {E:Type*}[AddGroup E](u:Limb H→E): Ell (hover H u):=by
     intro h i; unfold hover; rw [stood,path_ferry]; cases e:dir H i<;> cases a:(axisK h).flip i.2<;>simp
lemma hover_reap {E:Type*}[AddGroup E](u:Limb H→E)(p:Limb H):hover H u p.val=u p:=by simp [hover]
lemma hover_conduit (i:Keys G (Limb H)): put (hover H i)=coat H (put i):=by
      funext p; unfold hover put coat PertExtension.Chart.expLinks; dsimp only; by_cases he:dir H p <;> simp only [he, Bool.false_eq_true,↓reduceIte]; exact Work.F03.exp_neg_color _
abbrev loadV (i:form 1 n):edgeV n→ℝ:=fun j=> i (j.1,coord j.2)
include H
lemma h_storm (u:form 1 n)(h:Ell (loadV u)): storm u:=by
      intro i; obtain ⟨k,hk⟩:=pins_axis i
      have he(x:Site n): u (x,coord i) = -u (decks k x-step i,coord i):=by
           have hv := h k (x,i); simpa [loadV,ferry,Step.used,Step.rotate,posDir,hk] using hv
      let f:= (roam H k).trans (Equiv.subRight (step i:Site n)); let g(x:Site n):= u (x,coord i); have hx:(∑ x:Site n,g (f x))=∑ x:Site n,g x:= f.sum_comp g
      have ht(x):g (f x) = -g x:=(by unfold g; rw [he x]; exact (neg_neg _).symm)
      simp_rw [ht,Finset.sum_neg_distrib] at hx; change (∑ x:Site n,g x)=0; linarith
lemma h_grad (h : form 1 n)(hu:Ell (loadV h))(hb: curl n *ᵥ h=0):∃ t:Node H→ℝ,∀ x:edgeV n, loadV h x=t (crumb H (x.1+step x.2))-t (crumb H x.1):=by
      obtain ⟨s,Ht⟩:= pure_g _ hb (h_storm H h hu); let f(x:Site n):=s (x,Exterior.vac)
      have hy(x:Site n)(i:Axis):loadV h (x,i)=f (x+step i)-f x:=by rw [Ht];exact d_sites ..
      have he (k:Kv)(x:Site n)(i:Axis): f (decks k (x+step i))-f (decks k x)=loadV h (x,i):=by
           rw [←Step.vec_pos (R:=Per n),decks_walk]; let v:= (axisK k).flip i; have ha:=hu k (x,i)
           cases hx:(axisK k).flip i
           · simp only [hx, Bool.false_eq_true,if_false] at ha
             rw [ha, ferry,show (posDir i).rotate (axisK k)=posDir i from by simp [axisK,Step.rotate,posDir] at *; simp_all, Step.vec_pos] -- simpler
             exact (hy ..).symm
           simp only [hx, ↓reduceIte] at ha; let e:= decks k x-step i
           have hd : (posDir i).rotate (axisK k)=negDir i:=by simp [axisK,Step.rotate,posDir,negDir] at *; simp_all
           rw [ha,show ferry k (x,i)=(e,i) by unfold ferry;dsimp only;rw [hd];rfl, hy,hd,Step.vec_neg,show decks k x + -(step i : Site n)=e by simp only [e, sub_eq_add_neg],show e+step i=decks k x by simp [e],neg_sub]
      let d (x:Site n):= (∑ k:Kv,f (decks k x)) / 4
      have ht(u:Site n): d (crumb H u).val=d u:=by
           obtain ⟨k,hk⟩:= (sitesK H).joint u; let p:= crumb H u; change decks k p.val=u at hk; change d p.val=d u; rw [←hk]; unfold d; simp_rw [← decks_plus H]; exact congr_arg (fun x:ℝ=> x/4) (Equiv.sum_comp (Equiv.addRight k) _).symm
      refine ⟨fun x=> d x.val,?_⟩; rintro ⟨x,i⟩; simp only; rw [ht,ht]; unfold d; rw [← sub_div,← Finset.sum_sub_distrib]; simp only [he, Finset.sum_const,Finset.card_univ,kvCard,nsmul_eq_mul,Nat.cast_ofNat];ring
end Streamer
end YM.OPE.Cascade
