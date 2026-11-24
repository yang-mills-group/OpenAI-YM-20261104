import YM.MS.Color.Group
/-!
# Color rotation commutes with Q on all kernels (including with support). The
 infinitesimal bracket/gauge-proof identities instead use the true group mode.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Color
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open Landau
open Complex (I)
open scoped Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {P D : Type} {f : P→Momentum D} [Fintype D] [DecidableEq D]
-- use hook simple sum only over same color; rank.
lemma hook_send (F: Score G D P) (i : Branch G D) (q:P) : ∑ j: Branch G D,(send f).table i j q • Koszul.D (j,q) F =∑ j: Atom D,bare i.1 j (f q) • Koszul.D ((j,i.2),q) F:= by
   simp [Fintype.sum_prod_type,send,choir,ite_smul]
lemma hook_at_color (i : Branch G D) (k:G.El) q (F: Score G D P) :
   (send f).move.hook (i,q) (repeatC k F)= ∑ l:CI G,wc k i.2 l • repeatC k ((send f).move.hook (setLeg (i,q) l) F):= by
   simp_rw [Charge.hook_rule (F:=repeatC k F),hook_send,c_prefix,Finset.smul_sum,setLeg,Charge.hook_rule ..,hook_send, map_sum,map_smul,Finset.smul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>smul_comm .. -- expected errors
lemma commute (u:G.El) (F : Score G D P): repeatC u ((send f).raise F)=(send f).raise (repeatC u F):= by
   ext w; induction w generalizing F with
   | nil=>simp [Charge.raise]
   | cons a w ih=>
       rcases a with ⟨a,q⟩; rw [D_eval _ (repeatC u ((send f).raise F)),c_prefix, D_eval _ ((send f).raise (repeatC u F))]; unfold Charge.raise at ih ⊢
       rw [Shift.deriving',hook_at_color,c_prefix]; simp_rw [Shift.deriving',map_add,map_sum,map_smul, smul_add, Finset.smul_sum, Finset.sum_add_distrib, Pi.add_apply, Finset.sum_apply,Pi.smul_apply, ih]; congr! 1; exact Finset.sum_congr rfl fun i _=> smul_comm ..
end YM.MS.Color
