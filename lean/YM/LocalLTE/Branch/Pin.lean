import YM.LocalLTE.Branch.Pay
/-! Pinned address decisions independent of old indexing. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Magnet
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens Quotes Residual WilsonStartup Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Ovens.Pipes Rack
variable {G:Gauge} {n:Side} {X X':Listing G n} {T:BudgetPoint} {Q:ℕ→Prop} {f:ℕ→ Config G n→ℝ}
lemma coupon (p:BudgetPoint)(A: RegularAddress n) (i j:PlaqAxes): projection (G:=G) A 0 i j=0:=by
  have hr:p.Regular A.support (0:Config G n→ℝ):= unspent ..
  have hp:= projection_sub (G:=G) A hr hr i j; simp only [sub_zero] at hp; exact hp.trans (sub_self _)
lemma reclaim (p:BudgetPoint)(A:RegularAddress n): rebate (G:=G) A 0=0:=by
  have h:p.Regular A.support (0:Config G n→ℝ):=unspent ..; have hp:=(Residual.label_sub A _ 0 _ p h h).1; simpa only [sub_zero,sub_self] using hp
variable (p:BudgetPoint)(h:∀ i,Q i→X.reg i=X'.reg i) (hf:∀ i,¬Q i→ f i=0)
include h hf p
lemma moderate : delta (X.read (seed f))=delta (X'.read (seed f)):= by
  unfold Averaging.delta Averaging.total; refine tsum_congr fun i=>?_ ; by_cases hi:Q i
  · unfold censusAt; rw [(show (X.read (seed f)).reg i=X'.reg i from h _ hi)]; rfl
  unfold censusAt Listing.read seed; dsimp only; rw [hf _ hi, coupon p,coupon p]; split <;> simp
omit h hf p in
lemma paired {e e':ℕ↪ℕ} {a:ℕ→ Config G n→ℝ} (h:∀ i,a i≠0→ e i=e' i):stuff e a=stuff e' a:= by
  funext i; have ht {e e':ℕ ↪ℕ} (h:∀ i,a i≠0→ e i=e' i) (hv:stuff e a i≠0) : stuff e a i=stuff e' a i:= by
    by_cases hi : i∈range e; swap; · exact False.elim (hv (blank _ _ hi))
    obtain ⟨i,rfl⟩:=hi; rw [stuffed] at hv ⊢; rw [h _ hv, stuffed]
  by_cases hi:stuff e a i=0; swap; · exact ht h hi
  by_cases hk:stuff e' a i=0; · exact hi.trans hk.symm
  exact (ht (fun i hi=> (h _ hi).symm) hk).symm

lemma pinnable (R:PathData G)(c:Clip)(α:ℝ): advanced X R c p f α=advanced X' R c p f α:=by
  let Y:=shelves X R p; let Y':= shelves X' R p; let g :=seed f; let D:=delta (X'.read g)
  let F:= fill X R c p g α D; let F':= fill X' R c p g α D
  have hx (i : EKey n) : archive X R c (seed f) α D i=archive X' R c (seed f) α D i ∧
      (archive X R c (seed f) α D i≠0→ incoming X R p i=incoming X' R p i):= by
    rcases i with i|(j|j)
    · change rebate (X.reg i) (f i) = rebate (X'.reg i) (f i) ∧ (rebate (X.reg i) (f i)≠0 → enlarges (X.reg i)=enlarges (X'.reg i))
      by_cases he:Q i
      · have hx:=(h i he); exact ⟨congr_arg (fun v=>rebate v (f i)) hx,fun _=>congr_arg _ hx⟩
      have hk (j:RegularAddress n):rebate j (f i)=0:= by rw [hf i he]; exact reclaim p j
      exact ⟨(hk _).trans (hk _).symm,fun hx=>False.elim (hx (hk _))⟩
    all_goals dsimp only [archive,incoming,Sum.elim_inr,Sum.elim_inl]; exact ⟨rfl,fun _=>rfl⟩
  have hh:F.regular=F'.regular := funext (fun i=> (hx (numbering _ i)).1)
  unfold advanced branch; rw [Magnet.moderate p h hf]; change stuff _ F.regular=stuff _ F'.regular; rw [← hh]
  apply Magnet.paired; intro i hi; change (regularKeys n).symm (Y.reg i, Sum.inl i)=(regularKeys n).symm (Y'.reg i, Sum.inl i) ; rw [(show Y.reg i=Y'.reg i from (hx (numbering (EKey n) i)).2 hi)]
end YM.AnalyticBridge.VerifiedReset.Collection.Magnet
