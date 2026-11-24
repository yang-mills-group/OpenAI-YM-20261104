import YM.OPE.Compatible.Ibis.Storm
/-! # evaluation costs independent of stencil support and volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d t:ℕ}{n:Side}{ε v s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea
section
variable (V:Train i)(h:4 ≤ i)
abbrev Θscrew (K: KernelChoices)(h:4 ≤ i):ℝ:= (terra_money K h).choose+1
abbrev Θspin (K:KernelChoices)(h:4 ≤ i)(t:ℕ):ℝ:=Real.sqrt (Θscrew K h)*ampleP t
lemma spokeV (i': Tab (Shade G) n):Borealis.Galea.Cane (quart (Vessel K V G n h) (Chart.tangent G (Body 1 n))) (fun v=>(spool G n v) i') (Θspin K h):=by
         let A:=Vessel K V G n h; let Y:= (spool G n).toContinuousLinearMap; obtain ⟨hv,hX⟩:= breathQ K V G n h; intro k hk; let k':=Θscrew K h; let f:=Ferry Y i'; have he : A.wick f f ≤ k':=(Real.le_norm_self _).trans (hX i'); exact Lal A (Chart.tangent G (Body 1 n)) f (Real.sqrt_nonneg _) (he.trans_eq (Real.sq_sqrt hv).symm) hk -- arguments
lemma spoke_pos (K:KernelChoices)(h:4 ≤ i)(l:ℕ):0 ≤ Θspin K h l := mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left ..))
variable (x:Site n)
lemma ParcelT (p:Script (Shade G) d)(hp:Sack (Page.figure m) p s):Borealis.Galea.Cane (quart (Vessel K V G n h) (Chart.tangent G (Body 1 n))) (fun i=>Script.value x p (spool G n i)) (s • hikeP (Θspin K h) d):=by
        let Y:= spool G n; let S:=Θspin K h; let μ:= (quart (Vessel K V G n h) (Chart.tangent G (Body 1 n))); haveI :IsProbabilityMeasure μ:=inferInstanceAs (IsProbabilityMeasure (quart (Vessel K V G n h) (Chart.tangent G (Body 1 n))))
        let w(j:Page (Shade G) d)(i):=render x j fun _=>spool G n i; let P:= hikeP S d; have ht {d:ℕ}(j:ℕ)(hv:0 < j):0 ≤hikeP S d j:=by
             induction d generalizing j with| zero=> exact zero_le_one| succ d ih=> exact mul_nonneg (spoke_pos K h (2*j)) (ih _ (by omega:0 < 2*j))
        have hf(j:Page (Shade G) d) :Borealis.Galea.Cane μ (w j) P:=by
             let f(t:Fin d)(i):=(Y i) (x+wrap n (j t).1,(j t).2); have he:∀ t,Borealis.Galea.Cane μ (f t) S:= fun _=>spokeV V h _; convert! dotP Finset.univ f (fun i _=>he i) using 1; ext1 i; rw[Finset.prod_apply]; rfl; unfold P; congr; simp
        let g(p':Page (Shade G) d):= (p p') • w p'; let f(W: Finset (Page (Shade G) d)):=∑ i∈W,g i; have hh(j:ℕ)(hj:0 < j)(a): Fault μ j (f a) (s*P j):=by
              have hv:=Fault.sum a g (fun i=> ‖p i‖*P j) (fun i _=> (Borealis.Galea.Cane.scal (hf i) (p i)) j hj) hj; apply hv.mono le_rfl; rw [← sum_mul]; let B:=Sack.mass hp (payer m); exact mul_le_mul_of_nonneg_right ((Summable.sum_le_tsum a (fun _ _=>norm_nonneg _) B.2.1).trans B.2.2) (ht j hj)
        intro j hj; let q(i):=Script.value x p (Y i)
        have hp' :Summable p:= hp.water (payer m); have hQ :Continuous q:=by
             rw [show q= (Tensor.diagonal (orchestra p x)) ∘ Y from ?_]; exact ((lyricCost _).cost.smooth.continuous).comp Y.continuous
             funext i; exact (instruments p hp' x (fun _=> Y i)).tsum_eq
        haveI : Countable (Page (Shade G) d):=inferInstanceAs (Countable (Fin d→ (Cover × Shade G)))
        refine ⟨mul_nonneg hp.coins (ht j hj), hQ.aestronglyMeasurable,Lp.eLpNorm_le_of_ae_tendsto (u:=atTop) (Eventually.of_forall (fun i=> (hh j hj i).passes)) (fun i=> (hh j hj i).strong) (Eventually.of_forall fun i=>?_ )⟩
        have hT: HasSum (fun u=> g u i) (q i):=(instruments p hp' x (fun _=>Y i)).summable.hasSum; have ht':Tendsto (fun s:Finset (Page (Shade G) d)=>∑ j∈s,g j i) atTop (𝓝 (q i)):=hT; simp_rw [f,Finset.sum_apply] -- goal;
        exact ht'
lemma leavesK (p:Seat k m (Shade G)): Borealis.Galea.Cane (quart (Vessel K V G n h) (Chart.tangent G (Body 1 n))) (LightP x (m:=m) p) (∑ i∈range (k+1),‖p‖ • hikeP (Θspin K h) i):=by
        let f:=lilies m k _ p; let g(i:ℕ)(j):=Script.value x (f i) (spool G n j)
        exact (funext (show ∀ j,(∑ i∈range (k+1),g i) j=LightP x (m:=m) p j from fun i=>Finset.sum_apply ..)) ▸ Borealis.Galea.Cane.sum _ g _ (fun j _=>ParcelT V h x (f j) ((sproutV m k p).2 j)) -- direction
end
end YM.OPE.Ibis
