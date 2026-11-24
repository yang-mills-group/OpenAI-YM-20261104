import YM.OPE.Compatible.Estuary.Ample
/-!
# Tape cost of fog difference on volume. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n c f L:Side}{P:Patch}{I J:Type}{m k r:ℕ}{σ C:ℝ}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
lemma pokeBill [Fintype J] (hs:0<σ)(_hC:0 ≤ C)(m r:ℕ) :∃ D:ℝ, 0 ≤ D∧∀ (A:Cross L I J),A.strip σ C→∀ (p:Script I r) z,soot m p z→ soot m (payVolume A p) (D*z):=by
    let u(i:Site L):= regionB J σ C (size (lift i)) r m*((r+1:ℕ):ℝ)^m; refine ⟨∑ i,u i, Finset.sum_nonneg (fun i _=> mul_nonneg (region_nn _ _ _ _ _ hs) (by positivity)),fun A h p z hp=>?_⟩
    have hg(i:Site L):= silt_cost (counterflow h hs p (lift i) hp); rw [sum_mul]; refine Sack.finGather _ _ _ (fun i _=> (hg i).tips (le_of_eq (by unfold u; ring))) (fun x=> zero_le_one.trans (payer m x)) -- `..`
-- project α
abbrev fane (G:Gauge): Row (Shade G) (Blend G):= transRows (toLeft (unitRow _) (0:Row G.ColorIndex (Shade G)))
lemma faneP (G:Gauge):Whole (fane G):=(toLeft_cash (unitRow (Shade G)) (0:Row G.ColorIndex (Shade G)) (⟨1,1,one_pos,fun x y=> Work.F08.strip_unit ..⟩) ⟨1,0,one_pos,fun i j=>by simp [Width,SumBudget]⟩).flipped
lemma fane_at (x:deck (Blend G) n): (fane G).acts n *ᵥ x=lac G n x:=by
     ext i; rw [acts_trans,splitMargin]; simp_rw [Matrix.transpose_apply];
     have hh(j:Tab G.ColorIndex n): (toLeft (unitRow _) (0:Row G.ColorIndex (Shade G))).acts n (starJ j) i=0:=by
        rw [toLeft_reap]; change (∑' u:Cover, if i.1=j.1+wrap n u then (0:ℝ) else 0)=0;simp
     simp_rw [hh,zero_mul,sum_const_zero,add_zero,toLeft_read,acts_unit, Matrix.one_apply]; simp
variable (G:Gauge)
lemma faneFund (m r:ℕ):∃ z:ℝ,0 ≤ z∧∀ (p:Script (Shade G) r) c, soot m p c→ soot m (raft (fane G) p) (z*c):=by
    obtain ⟨σ,C,hσ,h⟩:=payact _ (faneP G); obtain ⟨z,hz,H⟩:=pokeBill hσ (le_max_right C 0) m r (L:=1) (J:=Blend G) (I:= Shade G); exact ⟨z,hz,H (marry (fane G)) (strip_mono h le_rfl (le_max_left ..))⟩
variable {G}
lemma flow_at {R:Bid.Dir G n→ℝ}(p:Script (Shade G) r)(h:ContDiffAt ℝ ω R 0)(hp: Voice p (spool G n).toContinuousLinearMap R)(he:Summable p):∀ i: Fin r→ deck (Blend G) n, iteratedFDeriv ℝ r (R∘solidY G n) 0 i= library n (raft (fane G) p) i:=by
    intro i; let x:= solidY G n; rw [raftReads _ (faneP G) _ he]; have hg := congr_arg (fun v: Tensor.T _ ℝ r=>v i) (jets_linear x (h.of_le le_top)); apply hg.trans; change iteratedFDeriv ℝ r R 0 (x ∘ i)=library n p _ ; rw [← hp]; apply congr_arg; funext j; rw [fane_at];exact (spool G n).apply_symm_apply _
end Script
end YM.OPE.Flume
