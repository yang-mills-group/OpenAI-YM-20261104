import YangMills.WilsonProof.NativeSupport.YM.MS.WardSquares
import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Variable

/-!
# Canonical BV loop (position Hessian)

Classical master test via ordinary nilpotence of an odd vector.
    Works unscaled initially. Pair coefficients signs from q parity.
    Only real point convention later; no Levi quotient yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset Cylinder
variable {R : Type*}[CommRing R] {A I J : Type*} {p : Sector A} {F W H:Raw A R} {u : Bool}
structure Bonded (p : Sector A)(I:Type*) where
    plain : I ↪ A
    dual : I ↪ A
    diff i j: plain i≠ dual j
    wave i: p (plain i) = !(p (dual i))
namespace Bonded
variable (B:Bonded p I)
lemma op (i:I) : (p (B.plain i) ^^ p (B.dual i))=true:= by rw [B.wave]; simp
lemma nob (i:I) : (cross (p (B.plain i)) (p (B.dual i)):R)=1:= by rw [B.wave]; cases h:p (B.dual i) <;> simp
local notation "C" => cross (R:=R)
local infixl:70 " ⋄ "=>product p

variable [Fintype I]
def fee (i:I):R:= cross (p (B.plain i)) true
def BV : Op A R:= loop B.fee (⇑B.dual) (⇑B.plain) Finset.univ
lemma costs : Balanced p true (B.fee (R:=R)) (⇑B.dual) (⇑B.plain) Finset.univ:=fun i _ _=> B.op i
omit [Fintype I] in
lemma orth (i:I) : (B.fee i:R) • ((B.fee i:R) • F)=F:= by simp [fee,smul_smul,cross_cross]
-- Hamiltonian vector & master.
def glory (s:I→ Raw A R): Op A R:= ∑ i:I,(product p (s i)).comp (D (B.plain i))
def hung (s:I→ Raw A R) : Raw A R:= ∑ i:I,(B.fee i:R) • product p (atLetter (B.dual i)) (s i)
lemma reveals (s:I→Raw A R) (F:Raw A R): B.glory s F=∑ i:I, s i ⋄ D (B.plain i) F:= by simp only [glory,LinearMap.sum_apply,LinearMap.comp_apply]
structure Lifted (s:I→ Raw A R): Prop where
    sym i: Symm p (s i)
    flip i: Pure p (p (B.dual i)) (s i)
    qonly i j: D (B.dual i) (s j)=0
namespace Lifted
variable {B} {s:I→Raw A R}(h:B.Lifted s)
include h
lemma acted_e : Pure p false (B.hung s):= by
   refine Pure.sum _ fun i _=> Pure.smul _ ?_; have hv := (speaks_p (B.dual i)).prod (h.flip i); simpa using hv
lemma acted_s : Symm p (B.hung s):= Symm.sum _ (fun i _=> ((speaks_s (B.dual i)).times (h.sym i)).smul _)
lemma acted (i:I): D (B.dual i) (B.hung s)=(B.fee i:R) • s i:= by
   classical
   simp only [hung,map_sum,map_smul,D_product,h.qonly,map_zero,add_zero]
   rw [Finset.sum_eq_single i,hear,coin_product,one_smul]; swap; exact fun h=> (h (Finset.mem_univ _)).elim
   intro j hj hi; rw [unheard _ (fun H=> hi (B.dual.injective H.symm)),map_zero,LinearMap.zero_apply,smul_zero]
lemma force_lap : B.BV (B.hung s)=∑ i:I, D (B.plain i) (s i):= by simp_rw [BV,loop,LinearMap.sum_apply, LinearMap.smul_apply, diffPair_apply,h.acted,map_smul,B.orth]
omit h in
lemma acts_antifield (i:I): B.glory s (atLetter (B.dual i))=0:= by simp only [B.reveals,unheard _ (B.diff _ i),map_zero,Finset.sum_const_zero]
-- s is odd. Need gallery sign
lemma acts_graded (hF:Pure p u F): B.glory s (F ⋄ H)= B.glory s F ⋄ H+C true u • (F ⋄ B.glory s H):= by
   have ht (i:I) : C (p (B.plain i)) u*C (p (B.dual i)) u=C true u:=by rw [← cross_left,B.op]
   simp_rw [B.reveals,map_sum,LinearMap.sum_apply,← times_assoc,Finset.smul_sum, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _=> ?_); rw [D_product,hF.signs,map_add,← times_assoc (s i),map_smul]; simp only [LinearMap.smul_apply,map_smul]; rw [← times_assoc (s i) F _,(h.flip i).times_comm hF,map_smul,LinearMap.smul_apply,smul_smul,ht]
lemma acted_0 (hm:∀ i,B.glory s (s i)=0): B.glory s (B.hung s)=0:= by
    simp only [hung,map_sum,map_smul]; apply Finset.sum_eq_zero; intro i _; change (B.fee i:R) • B.glory s (atLetter _ ⋄ s i)=_; simp [h.acts_graded (speaks_p _),hm,acts_antifield]
end Lifted
lemma flat_zero (he:∀ i, D (B.dual i) F=0): B.BV F=0:= by simp only [BV,loop,LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply,he,map_zero,smul_zero,Finset.sum_const_zero]
lemma by_lap (he:Pure p false F): link B.BV true p F W= ∑ i:I,(B.fee i:R) • ( D (B.dual i) F ⋄ D (B.plain i) W+ D (B.plain i) F ⋄ D (B.dual i) W):= by simp_rw [BV,loop,link_sum,link_scale, link_pair_left (B.dual _) (B.plain _) (B.op _) _ he,B.nob,one_smul] -- nob simpl
omit [Fintype I] in
lemma even_swap (h:Pure p false F)(i:I): D (B.dual i) F ⋄ D (B.plain i) F=D (B.plain i) F ⋄ D (B.dual i) F:= by rw [(h.drop (B.dual i)).times_comm (h.drop (B.plain i)),cross_comm (false ^^ p (B.dual i))]; simp only [Bool.false_xor,B.nob,one_smul]
section coupling
variable {B} {s:I→ Raw A R}(h:B.Lifted s)
namespace Lifted
include h
lemma unstar (hF:Pure p false F) (hf:∀ i,D (B.dual i) F=0) (hw:∀ i,D (B.dual i) W=0): link B.BV true p (F+B.hung s) W=B.glory s W:= by
    simp only [B.by_lap (hF.add h.acted_e), map_add,h.acted,hf,hw,map_zero,add_zero,zero_add,map_smul,LinearMap.smul_apply,B.orth,B.reveals]
lemma inv_cl (hF:Pure p false F)(hf:∀ i,D (B.dual i) F=0)(hk:B.glory s F=0)(h':∀ i,B.glory s (s i)=0): link B.BV true p (F+B.hung s) (F+B.hung s)=0:= by
    rw [B.by_lap (hF.add h.acted_e)]; simp_rw [← B.even_swap (hF.add h.acted_e)]; simp_rw [show ∀ i,D (B.dual i) (F+B.hung s)=(B.fee i:R) • s i by simp [hf,h.acted],smul_add]; simp only [map_smul,LinearMap.smul_apply,B.orth,Finset.sum_add_distrib]; rw [← B.reveals]; rw [map_add,hk,h.acted_0 h']; simp
end Lifted
end coupling
end Bonded
end YM.MS.Koszul
