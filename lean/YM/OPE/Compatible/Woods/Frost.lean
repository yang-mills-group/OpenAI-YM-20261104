import YM.OPE.Compatible.Woods.Sleet
/-!
# Conditional fluctuation frame still local at limiting K. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Next.Free FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G: Gauge}{ι:Type*}{c f L:Side}{j: ℕ}{P:Patch}{C:KernelChoices}{η A s a T x:ℝ}
lemma rowMeets {α β:Type*}{H:ι→ℕ→ Row α β}{A:Row α β}{ht:ι} {m:ℕ→ℝ} (hp:Tendsto m atTop (𝓝 0))(h:∀ v w i j,i≤j→(H v i-H w j).strip s (m i))(hs:0<s)(hx:H ht 0=A)(hg:Whole A): ∃ W: Row α β, Whole W ∧ ∀ v i,(H v i-W).strip s (m i):=by
     choose S g hS using fun i j=> OPE.Flume.Sack.finalSeq (f:=fun k=> H ht k i j) (u:=envelopeW s) (fun n m q=> h ht ht n m q i j) hp (fun x=> Real.one_le_exp (mul_nonneg hs.le (by positivity)))
     have hr v k : (H v k-S).strip s (m k) := fun i j=> OPE.Flume.Sack.closes (f:=fun n=> H v k i j - H ht n i j) ((eventually_ge_atTop k).mono (fun n hn=> h v ht k n hn i j)) tendsto_const_nhds (p:=H v k i j-S i j) (fun a=> (tendsto_const_nhds (x:= H v k i j a)).sub (g i j a)) (fun a=> Real.exp_nonneg _)
     refine ⟨S,?_,hr⟩
     have hK: Whole (A-S):=by rw [← hx]; exact ⟨s,_,hs,hr ht 0⟩
     rw [show S = A-(A-S) by abel]; exact hg.minus hK
namespace Medal
open Frequency
variable (B: Medal P G C P.J)(H:Payer C P η A a T)
abbrev frame (D: Train P.J)(n:ℕ):= B.V (folder P D n)
include H
lemma stillV : ∃ t X:ℝ,∃ K:Row (Slip G P.L) (Slip G P.L), 0<t ∧ t≤B.width ∧ Whole K ∧ ∀ D n,(B.frame D n-K).strip t (X*(1/2:ℝ)^n):=by -- H omitted
   let t:=min η B.width; have ht:0<t:= lt_min H.height B.toll
   obtain ⟨b,hb⟩:= sanction H
   let k : ℝ := B.visits*b
   have hi (D E:Train P.J)(n m:ℕ)(hn:n ≤ m): (B.frame D n-B.frame E m).strip t (k*(1/2:ℝ)^n):=by
       rw [show k*(1/2:ℝ)^n=B.visits*(b*(1/2:ℝ)^n) by simp only [k,mul_assoc]]
       apply B.approach _ _ P.order_cut ht (min_le_right ..); apply strip_mono _ (min_le_left ..) le_rfl
       intro i j; have hh:= hb D E n m hn i j; simp only [Width,Pi.sub_apply] at *; simpa only [norm_sub_rev (Op C (folder P D n) i j _) (Op C (folder P E m) i j _)] using hh
   obtain ⟨X,hX,hv⟩:=rowMeets (show Tendsto (fun n:ℕ=> k*(1/2:ℝ)^n) atTop (𝓝 0) from by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ)≤ 1/2 by norm_num) (by norm_num)).const_mul k) hi ht (ht:=.top P.J) rfl (B.whole _); exact ⟨t,_,X,ht,min_le_right ..,hX,hv⟩
-- products
end Medal
end YM.OPE.Woody
