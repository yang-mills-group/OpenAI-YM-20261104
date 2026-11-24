import YM.MS.KoszulAllocate
import YM.MS.LoopIdentity

/-! # Momentum bookkeeping for the master and Polchinski equations

Components with support summing to zero are represented this way on momentum
groups; over the continuous dual P all point formulas are kernel identities
of smooth forms on the indicated total, not evaluations of momentum distribution
deltas. Raw always total, physical evaluation restricted (below). Scaling
powers from integration measures not included by setting junk values off-support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Set Finset Koszul
variable {A P R I : Type*} [AddCommGroup P] [CommRing R]
abbrev Mode (A P : Type*) := A × P
abbrev Row (A P R : Type*) := Raw (Mode A P) R
abbrev field (p : Sector A) : Sector (Mode A P) := fun x=> p x.1
variable {p : Sector A}

def net (w : Legs (Mode A P)) := (w.map Prod.snd).sum
@[simp] lemma net_cons (x : Mode A P) l : net (x::l)=x.2+net l:= by simp [net]
@[simp] lemma net_append (w v : Legs (Mode A P)) : net (w++v)=net w + net v:= by simp [net]
lemma split_net {l k w : Legs (Mode A P)} (h:Split l k w) : net l+net k=net w:= split_sum _ h
abbrev Conserved (F : Row A P R) := ∀ w, net w≠ 0→ F w=0
/-- Sym and Pure and modewise equality as needed will be used on visible lists only. -/
abbrev Agrees (F G:Row A P R) := ∀ w, net w=0→ F w=G w
open Classical in
def translate (F : Row A P R) : Row A P R := fun w=> if net w=0 then F w else 0
@[simp] lemma trans_on (F : Row A P R) (w) (h: net w=0) : translate F w=F w:=by simp [translate,h]
lemma trans_off (F : Row A P R) : Conserved (translate F):=fun w h=>by simp [translate,h]
lemma agree_trans {F G:Row A P R} : Agrees F G ↔ translate F=translate G:= by
   classical
   refine ⟨fun h=>?_, fun h w he=>?_⟩
   · ext w; by_cases ht: net w=0; simp [*,h w ht]; simp [translate,ht]
   rw [← trans_on F w he,← trans_on G w he,h]
lemma trans_pure (F : Row A P R) (b : Bool) : Koszul.Pure (field p) b (translate F) ↔ ∀ w, net w=0→ degree (field p) w≠ b→ F w=0 := by
   unfold Koszul.Pure; constructor
   · intro h w he hv; simpa [he] using h w hv
   intro h w he; by_cases hv: net w=0; simp [*,h w hv he]; simp [translate,hv]
lemma trans_symm (F : Row A P R) : Koszul.Symm (field p) (translate F) ↔ ∀ l i j r, net (l++i::j::r) = 0→ F (l++i::j::r) = cross (p i.1) (p j.1)* F (l++j::i::r):= by
   have H l (i j : Mode A P) r: net (l++i::j::r)=net (l++j::i::r):= by simp [add_left_comm]
   refine ⟨fun h l i j r he=>?_, fun h l i j r=> ?_⟩
   · rw [← trans_on F _ he,h,trans_on _ _ ((H ..).symm.trans he)]
   unfold field; by_cases hv: net (l++i::j::r)=0
   · rw [trans_on _ _ hv,trans_on _ _ ((H ..).symm.trans hv)]; exact h l i j r hv
   rw [trans_off _ _ hv, trans_off _ _ (fun h=> hv ((H ..).trans h)), mul_zero]

variable [Fintype A]
abbrev Flux (A P R:Type*) := A → A → P → R
namespace Flux
-- Equation uses this density oriented q from args built a@q then c@-q. K includes any factor 1/2.
def closed (K : Flux A P R) (p : Sector A) (b : Bool) := ∀ a e q,K a e q ≠ 0 → ((p e).xor (p a))=b
-- full loop at fixed q
def trc (K : Flux A P R) (q:P) : Op (Mode A P) R := ∑ a:A, ∑ b:A, K a b q • diffPair (a,q) (b,-q)
@[simp] lemma at_trc (K : Flux A P R) q (u : Row A P R) w : trc K q u w=∑ a:A,∑ b:A, K a b q * u ((a,q)::(b,-q)::w) := by
  simp only [trc, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,smul_eq_mul,diffPair_apply,at_D]
-- connected tree pairing, root first input anchored by momentum total-zero. Include both orientations per line.
def attaches (p : Sector A) (K : Flux A P R) (F H : Row A P R) (l k : Legs (Mode A P)) : R :=
 let q := -net l
 ∑ i:A, ∑ j:A, (K i j q * ((cross (p j) (degree (field p) l) * F ((i,q)::l))*H ((j,-q)::k)) + K i j (-q)*((cross (p i) ((p j).xor (degree (field p) l)) * F ((j,q)::l))*H ((i,-q)::k)))
-- Check second formula from link_pair second term: D w (sign_p(a) F) = sign p(a)(F at w::l), yes.

def tree (p : Sector A) (K:Flux A P R) (F H : Row A P R) (w : Legs (Mode A P)) : R := scatter (field p) w (attaches p K F H)

lemma conserved_trc (K : Flux A P R) q {F : Row A P R} (h : Conserved F) : Conserved (trc K q F) := by
   intro w hw; rw [at_trc]; apply Finset.sum_eq_zero; intro i _; refine Finset.sum_eq_zero fun j _=>?_ ; rw [h _,mul_zero]; simpa using hw
lemma agrees_trc (K : Flux A P R) q {F H : Row A P R} (h : Agrees F H) : Agrees (trc K q F) (trc K q H) := by
   intro w hw; rw [at_trc,at_trc]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ; rw [h _ (by simp [hw])]
lemma conserved_tree (K : Flux A P R) p {H : Row A P R} (h : Conserved H) (F : Row A P R) : Conserved (tree p K F H) := by
   intro w hw; let r:=attaches p K F H
   have hz : scatter (field p) w r = scatter (field p) w (fun _ _=>(0:R)) := by
       refine scatter_congr _ _ _ _ fun l k h' => ?_
       unfold r attaches; dsimp only; apply Finset.sum_eq_zero; intro i _; refine Finset.sum_eq_zero fun j _=> ?_
       simp only [h ((j,- -net l)::k) (by simpa [split_net h'] using hw), h ((i,- -net l)::k) (by simpa [split_net h'] using hw), mul_zero, add_zero]
   change scatter _ w r=_; rw [hz]; exact map_zero (allocate ..)
lemma agrees_tree (K L : Row A P R) {F H : Row A P R} (X : Flux A P R) p (h : Agrees K F) (h' : Agrees L H) : Agrees (tree p X K L) (tree p X F H) := by
   intro w hw; refine scatter_congr _ _ _ _ fun l k he=> ?_
   unfold attaches; dsimp only; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_
   rw [h _ (by simp), h _ (by simp), h' _ (by simp [split_net he,hw]), h' _ (by simp [split_net he,hw])]
end Flux
end YM.MS.Plane
