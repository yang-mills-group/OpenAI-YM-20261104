import YM.Contacts.Loom.Wade
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
namespace Patch
open Capture
variable {d D g:ℕ→ℝ} {n:ℕ} [∀ i,FiniteDimensional ℝ (E i)] [∀ i,MeasurableSpace (V i)][∀ i,BorelSpace (V i)]
variable {U W:Trunk E V}{μ: ∀ i,Measure (V i)} [∀ i,IsProbabilityMeasure (μ i)]
variable {x:Frame α E} {R:ℕ→ Trunk E V}
-- warm and cool combine counts.
variable (hS:Shell N μ D) (h: Word N (E:=E) (fun (i:ℕ) (v:stepIn E V d D i)=>arm v) k n p (wish U) (fun i=>wish (R i)))
    (hw:Board d U)(hr:∀ i≤n,Board d (R i))(hR:∀ i≤n,∃ z:ℝ,Joint N k z d (R i))
local notation "q" => (Frame.Port E d)
lemma shift {F G: Lamp E}(he:∀ᶠ i in atTop,∀ x∈Frame.Bank E d i,F i x=G i x) (hg:Direct N k p d G) : Direct N k p d F:= hg.reveal ((he).mono fun i hi x=> (show ∀ᶠ a in 𝓝 (Frame.Port E d i x),a∈ Frame.Bank E d i from isOpen_ball.mem_nhds x.2).mono fun a ha=> hi a ha) le_rfl le_rfl
lemma smoothValue (hr:∀ i≤n,Fits μ d (R i) (coast D V)): ∀ᶠ i in atTop,∀ x∈Frame.Bank E d i, IntegrableOn (fun y=> green R n i y x) (coast D V i) (μ i) ∧ stay μ D (green R n) i x= (∑ j∈range (n+1), stay μ D (R j) i x):= by
   filter_upwards [(eventually_all_finset (range (n+1))).mpr (fun j hj=>hr j (Nat.le_of_lt_succ (mem_range.mp hj)))] with i hi x hx
   let f (j:ℕ)(v:V i):= R j i v x; have he (j)(hj:j∈Finset.range (n+1)): IntegrableOn (f j) (coast D V i) (μ i):= hi j hj x hx
   have hh : (fun y=>green R n i y x)=fun y=> (∑ j∈Finset.range (n+1), f j y):= funext fun y=>by simp only [green,f,Finset.sum_apply]
   constructor; · rw [hh]; exact integrable_finsetSum _ he
   unfold stay; rw [hh, MeasureTheory.integral_finsetSum _ he]
include h hw hr hR hS
private theorem home (he:i≤n): Direct N k (p*i) d (weight μ (R i)) ∧ Direct N k (p*(n+1)) d (stay μ D (R i)-weight μ (R i)) ∧ Fits μ d (R i) (coast D V) ∧ Fits μ d (R i) (fun i=> (coast D V i)ᶜ):= by
   obtain ⟨hb,hp⟩:= warmer (μ:=μ) (hr i he) (h.entries i he); obtain ⟨r,h'⟩:=hR i he; obtain ⟨ht,hH⟩:= cool hS (hr i he) h' (p*(n+1));
   let v:= gone μ D (R i); let W:= weight μ (R i); let Y:= stay μ D (R i)
   have he':∀ᶠ k in atTop,∀ x∈Frame.Bank E d k,W k x=Y k x+v k x := (hp.and hH).mono (fun i hi x hx => (MeasureTheory.integral_add_compl (s:=(coast D V i)) measurableSet_closedBall (by rw [← integrableOn_univ,← Set.union_compl_self (coast D V i)]; exact (hi.1 x hx).union (hi.2 x hx)) ).symm)
   refine ⟨shift (G:=Y+v) he' (Arms.sum hb (Arms.lo ht ?_ le_rfl)), shift (G:=-v) (he'.mono fun i hi x hx=> ?_) ht.opp, hp, hH⟩; -- shift he type not pair. edit
   · exact mul_le_mul_of_nonpos_left ( (by have hz:(i:ℝ)≤ n:= Nat.cast_le.mpr he; linarith): (i:ℝ) ≤ (n+1:ℝ)) h.quiet.le
   simp only [Pi.sub_apply,Pi.neg_apply]; change Y i x-W i x=-(v i x); rw [hi x hx]; ring

lemma collects : Word N (Frame.Port E d) k n p (leaf (stay μ D U)) (fun i=> leaf (weight μ (R i))) := by
   refine ⟨h.quiet,fun i hi=>(home hS h hw hr hR hi).1, ?_⟩
   have hR(i) (hi:i≤n):= (home hS h hw hr hR hi).2
   have hh:= smoothValue (fun i hi=> (hR i hi).2.1); let v:=green R n; have hx:Narrow N k (p*(n+1)) d D (U-v):= by
     refine Arms.cheaper ?_ h.grade; funext i j k; simp only [green,Finset.sum_apply,Pi.sub_apply]; change _-_=(U i (leg j) k-green R n i (leg j) k); unfold green; simp only [wish,Finset.sum_apply]
   have hp:=warmer (U:=U) (μ:=μ) hw h.rising; have he : Board d (U-v):= hw.sub (Board.fin _ _ (fun i hi=> hr i (Nat.le_of_lt_succ (mem_range.mp hi))))
   let X: Lamp E:= stay μ D (U-v) + ∑ i∈Finset.range (n+1),(stay μ D (R i)-weight μ (R i))
   have hX : Direct N k (p*((n:ℝ)+1)) d X:= by
      have hf := Budget.rush (k:=k) (s:=Finset.range (n+1)) _ (fun i hi=> (hR i (Nat.le_of_lt_succ (mem_range.mp hi))).1); refine Arms.cheaper ?_ ((warmer (μ:=μ) he hx).1.sum hf); funext i j x; simp only [X,leaf,Pi.add_apply,Pi.sub_apply,Finset.sum_apply]
   let Y:=stay μ D U-green (fun i=> weight μ (R i)) n
   have hz: Direct N k (p*((n:ℝ)+1)) d Y:= by
     refine shift ((hp.2.and hh).mono fun i hi x hx=> ?_) hX; have hK: stay μ D (U-v) i x=stay μ D U i x-stay μ D v i x:= MeasureTheory.integral_sub (hi.1 x hx) (hi.2 x hx|>.1); simp only [X,Y,green,Pi.sub_apply,Pi.add_apply,Finset.sum_apply,sum_sub_distrib]; rw [hK]; change _-_ = (_-stay μ D (green R n) i x) + _; rw [(hi.2 x hx).2]; abel
   refine Arms.cheaper ?_ hz; funext i j x; unfold Y green leaf; simp only [Pi.sub_apply,Finset.sum_apply]
end Patch
end
end YM.Contacts.Loom
