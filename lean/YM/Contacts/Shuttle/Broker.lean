import YM.Contacts.Shuttle.Spring
/-!
# Momentum extraction at a fixed charge

Epoch later may sum charges/rebranch. Uses tested-polynomial proofs across
our own physical account to justify cancellations didn't lose Ward terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Larch
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{s:ℝ≥0}{b c:ℝ}{h k n i:ℕ}{m:Side}
namespace Tide
abbrev Cohort (G:Gauge):= Pulse.Rack (Node (Dyes G))
def rows (F:Cohort G)(k h:ℕ):Ship G k→ℝ := fun x=>∑ i∈Finset.range (h+1), Tensor.diagonal (sheet i (F i) (lens G k)) x
structure Felt (F:Cohort G):Prop where
   poetic i : Poem (F i)
   alone i : ∃ a:Dyes G,∃ s:ℝ≥0,0<s ∧ ∃ C:ℝ, Rest (terrain s (Dyes G)) (0,a) (F i) C -- simple G ensures a exists.
variable {F:Cohort G}
lemma Felt.told (h:Felt F)(i:ℕ): Summable (F i):= by obtain ⟨a,s,hs,b,H⟩:= h.alone i; exact H.summ
private lemma bm {f:Field (Fin n) (Node X)}{P: Node X → E→L[ℝ] ℝ}{x:X}(H:Rest (terrain s X) (0,x) f b)(hs:0<s)(hP:Ice P (fun y=> blast y^k) c)(hc:0≤c) : Summable (blanket n f P):= Summable.of_norm (blanket_spend H hs hc hP).2.1
lemma Felt.board (h:Felt F)(i k:ℕ) : Summable (blanket i (F i) (lens G k)):= by
    obtain ⟨a,s,hs,b,H⟩:= h.alone i; exact bm H hs (glaze G k) (by positivity)
lemma Felt.lists (h:Felt F)(k i:ℕ): Tensor.Sym (sheet i (F i) (lens G k)):= by
   intro u v; simp_rw [sheet_read (h.board i k)]; unfold say; rw [← (Equiv.arrowCongr v.symm (Equiv.refl _)).tsum_eq _]; apply tsum_congr; intro p; rw [show Equiv.arrowCongr v.symm (Equiv.refl (Node (Dyes G))) p=p ∘ v from rfl,h.poetic i v]; exact congr_arg (F i p * ·) (Equiv.prod_comp v (fun j=> (lens G k (p j)) (u j)))
open PertExtension.Series Radial Ion
lemma rows_diff (F:Cohort G)(k h:ℕ) : ContDiff ℝ ω (rows F k h):= ContDiff.sum (fun _ _=> diag_smooth ..)
lemma Felt.plans (hf:Felt F) (d:ℕ) (hi:i ≤ k) : Tensor.coeff (rows F d k) i 0=sheet i (F i) (lens G d):= by
   refine Tensor.ext_diag _ _ (coeff_symm (rows_diff F d k|>.contDiffAt.of_le le_top)) (hf.lists d i) (funext fun x=>?_) -- import?
   change Radial.jet _ i x=_; unfold rows; rw [Ion.loan_sum _ (fun j _=> ContDiffAt.analyticAt (Tensor.diag_smooth ..|>.contDiffAt)),Finset.sum_eq_single i]; all_goals first | (rw [Milling.radiant (Tensor.diag_smooth ..|>.contDiffAt.analyticAt) i i (fun x t=> Tensor.homogeneous _ x t),if_pos rfl]) | skip
   · intro j hj hk; rw [Milling.radiant (Tensor.diag_smooth ..|>.contDiffAt.analyticAt) j i (fun x t=>Tensor.homogeneous _ x t),if_neg hk.symm]
   · simp only [Finset.mem_range, Nat.lt_succ_of_le hi,not_true]; tauto
structure Ticket (P: Link G m→ℝ)(F:Cohort G) (k:ℕ): Prop where
   clear : AnalyticAt ℝ P 0
   points i (hi:i≤k) x: Radial.jet P i x=House.design (packing (lower m) (F i)) x
structure Tags (F:Cohort G) : Prop extends Felt F where
   oath (m:Side)(k:ℕ): ∃ f:Config G m→ℝ, Continuous f ∧ GaugeInvariant f ∧ Ticket (f ∘ input G m) F k
lemma Ticket.points_tensor {m:Side}{P:Link G m→ℝ} (h:Ticket P F k)(H:Felt F) (hi:i≤k)(x:Fin i→Link G m): Tensor.coeff P i 0 x=say (F i) (fun j=> x j ∘ lower m):= by
   rw [Lumen.recital_exact P _ (Shuttle.poetic _ (H.poetic i) _) h.clear (h.points i hi)]; change recording (packing _ (F i)) x=_; rw [← say_fold (p:=lower m) (H.told _) x,recording_apply]; unfold say; rw [tsum_fintype]; exact sum_congr rfl (fun i _=> mul_comm ..)
lemma request (F:Cohort G)(k:ℕ)(f:Tide.Ship G n): -- trivial identity used notation below? remove
    rows F n k f=rows F n k f:= rfl
end Tide
end YM.Contacts.Shuttle
