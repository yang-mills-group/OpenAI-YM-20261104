import YM.AlbaMS.Barr.Shops
import YM.AlbaMS.Pockets.Hanzi

/-!
# Nil-order coupling bookkeeping. Any Tag windows

Enforce common vacuum chart origins and couple v.Z nil. Need unit at MSize.
Proof volume normalization output-values. Do not assume independent-physical
things; conditions c_z only through all-order matching procedure. Invariant
primary η price belongs to geom.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function Filter IsNilpotent
open scoped BigOperators Classical
variable {ι W E R S : Type*}[AddCommMonoid W][Fintype ι][CommRing R][CommRing S]{T : Ladder ι W}
namespace Coil
variable {ρ:E→Bool}{k:E→E→R} (A : R→+*S) {F:Coil ρ R}{s : Finset E}{n m : ℕ}
variable [Algebra ℚ R] [Algebra ℚ S]
lemma blown_pe : Wind ρ A (pe k s n F)= pe (fun i j=>A (k i j)) s n (Wind ρ A F):= by
  induction n with|zero=> rw [pe_zero,pe_zero]|succ n ih=>
    apply proletariat (n:=n+1) (by omega); rw [show ((n+1:ℕ):S)= A ((n+1:ℕ):R) from (map_natCast _ _).symm, ← Wind_smul, pe_step, Wind_touch, ih, map_natCast,pe_step]
lemma blown (h:FinRank F): Wind ρ A (wither k s F)=wither (fun i j=>A (k i j)) s (Wind ρ A F):=by
  have H:Cap (Wind ρ A F) h.choose:= Cap.seep _ _ h.choose_spec
  rw [withers h.choose_spec (by omega : h.choose≤2*h.choose),withers H (by omega : h.choose≤2*h.choose),twig_apply,twig_apply,map_sum];exact Finset.sum_congr rfl fun i _=> blown_pe _
-- Tags head evaluation
end Coil
namespace Tags
open Ladder Coil
lemma inch (D : Ladder ι W) : D.sums D.ort={(D.ort,D.ort)}:=by
  ext i; rw [D.member]; constructor
  · intro h; have he:= D.raises' h; rw [D.d0,_root_.Eq.comm, Nat.add_eq_zero_iff] at he; have hv (x:ι)(h:D.d x=0): x=D.ort:=not_not.1 fun hn=> (D.lift hn).ne' h; exact Finset.mem_singleton.mpr (Prod.ext (hv _ he.1) (hv _ he.2))
  intro h; rw [Finset.mem_singleton] at h; rw [h]; simp

def core : Tags T R→+*R where
  __:=peek T.ort
  map_one':=by change gem T T.ort (1:R) T.ort=_; rw [gem_read,if_pos rfl]
  map_mul' x y:=by change (x*y) T.ort=_; rw [product_cell, inch, Finset.sum_singleton];rfl
@[simp] lemma center (c:R): core (inject T c)=c:= by change gem T T.ort c T.ort=c; rw [gem_read,if_pos rfl]
lemma derives {a:Tags T R}(h:core a=0): IsNilpotent a:=by
  let p:=fun _:Unit=>false; have ht : clip T T.ort (put p a)=0:=by unfold clip; rw [seep_put,show peek T.ort a=0 from h, put_zero]
  obtain ⟨m,he⟩:= Silent.nil ht
  refine ⟨m,?_⟩; have heq : ∀ n, put p a^n=put p (a^n):= fun n=>by change algebraMap (Tags T R) (Coil p (Tags T R)) a ^ n=algebraMap (Tags T R) (Coil p (Tags T R)) _; rw [map_pow];
  rw [heq] at he; exact DFunLike.congr_fun he []
lemma burnt (x:Tags T R)(h:core x=1): IsUnit x:= by
  nth_rw 1 [← sub_sub_self 1 x]; exact (derives (a:=1-x) (by rw [map_sub,map_one,h,sub_self])).isUnit_one_sub
end Tags
end YM.MSBar.Bric
namespace YM.MSBar.Barr
open Set Function Filter LinearMap Matrix IsNilpotent
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Coil Inlay Inlay.Net Tune Odom Lattice Nexus Loft Cutis Cutis.Winter
variable {K B E V : Type*}[Fintype K][AddCommMonoid B][Fintype E][Fintype V]{D:Ladder K B}(P:Tune (Tags D ℝ)){G:Gauge}{n:Side}
structure Idle (P : Tune (Tags D ℝ)) : Prop where
  base : P.Overlay (baseT P.a P.ha) Tags.core
namespace Idle
variable {Ω:Net E V}(F:Odom.Book Ω G)(h: Idle P)
include h
lemma nul : IsNilpotent P.z:= Tags.derives h.base.z.symm
lemma zero_look (x:ℝ): Tags.core (P.D x)=x:= (h.base.D x).symm
lemma lags : Wind _ Tags.core (F.fair P)=F.first P.a P.ha:=by
  ext l; change Tags.core (P.D (F.first _ _ _))=_; rw [h.zero_look]
lemma openQ : Wind _ Tags.core (F.charter P)=F.first P.a P.ha := by
  exact (show (Wind _ Tags.core) _=F.charter (baseT P.a P.ha) from h.base.fire).trans (F.charter_quiet P.ha)
lemma feel : IsNilpotent (F.stim P):= by
  apply Ladder.Silent.nil; change Wind _ Tags.core (F.stim P)=0; rw [Odom.Book.stim,map_sub,h.openQ,h.lags,sub_self] -- h args
-- generic probes of this or proportional orbit vacuum. useful in connected program
lemma paid (g: Leaf G E V→ Leaf G E V→ Tags D ℝ)(a : ℝ) : Fritz.bought g (P.D a • F.stim P):=by
  let X:=P.D a • F.stim P; have hr: FinRank X:=(F.stim_rank P (h.nul _)).smul _; have hc: Wind _ Tags.core X=0:=by unfold X Odom.Book.stim; rw [Wind_smul,map_sub,h.openQ,h.lags,sub_self,smul_zero];
  refine Tags.burnt _ ?_; change (Wind _ Tags.core (wither g Finset.univ (exp (-X)*1))) []=1; rw [mul_one,blown _ hr.neg.exponent,map_exp ((h.feel P F).smul (P.D a) |>.neg),map_neg,hc,neg_zero,exp_zero]; exact (DFunLike.congr_fun (wither_const (ρ:=ø) 1) []) -- wither of one
lemma funded (g: Leaf G E V→ Leaf G E V→ Tags D ℝ) : Fritz.bought g (F.stim P):= by have ht:=paid P F h g 1; simpa using ht
end Idle
end YM.MSBar.Barr
