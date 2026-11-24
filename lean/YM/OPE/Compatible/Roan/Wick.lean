import YM.OPE.Compatible.Roan.Eye
/-! # Sum in cluster region clock.Phase enact -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m n:ℕ}{t C s u z ℓ v a c e r R β:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T} {q:Sender L} (p:Site L.f)
noncomputable abbrev burst (s x:ℝ):= Real.exp (-s*x)
noncomputable abbrev wigP (s:ℝ)(j:Site L.f)(v:RodZ L n):= burst s (Dtn p j)*burst s (Inrange L j v)
lemma wake (s:ℝ)(j:Site L.f)(v:RodZ L n):0 ≤ wigP (L:=L) p s j v := mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
open Next.SectorChange Progress.StationaryScenes AnalyticNext.QuarticMatch Radius Estimate AnalyticNext.QuarticMatch.Local
noncomputable abbrev ΛSite(s:ℝ):= Premium.overall s
noncomputable abbrev ΛGram (G:Gauge)(s:ℝ):= creep G s+farm G s
lemma τgo (v:Site L.f) (i:ℕ) (ht:0<t): ∑ j:RodZ L i, burst t (Inrange L v j) ≤ ΛGram G t ^i:=by
          let f(x:Drive L):=burst t (Dtn v (Wct L x)); have hl: ∑ j:RodZ L i,(∏ k:Fin i,f (j k))= (∑ j:Drive L,f j)^i:=by convert! Eq.symm (Fintype.prod_sum (fun (_:Fin i)(j:Drive L)=>f j)) using 1; simp
          have he: (∑ j:Drive L,f j)≤ ΛGram G t:= galore L.Z L.ForestQ ht _; unfold burst Inrange; simp_rw [mul_sum,Real.exp_sum]; rw [hl]; exact pow_le_pow_left₀ (sum_nonneg fun _ _=>Real.exp_nonneg _) he _
noncomputable abbrev tokenCost(G:Gauge)(n:ℕ)(t:ℝ):= ΛSite t*ΛGram G t ^n
lemma κBudget (n:ℕ)(ht:0<t): ∑ j:Site L.f,∑ i:RodZ L n,wigP (L:=L) p t j i ≤ tokenCost G n t:=by
          have he : ∑ j:Site L.f,burst t (Dtn p j) ≤ ΛSite t:=by unfold burst Dtn; simp_rw [neg_mul, Real.exp_neg,separation_comm p]; simpa [Green.wt] using Premium.lives 1 ht p
          have hv:0≤ ΛGram G t ^ n:=(sum_nonneg fun i _=> Real.exp_nonneg _).trans (τgo (L:=L) p n ht); unfold wigP; simp_rw [←mul_sum]; apply le_trans _ (mul_le_mul_of_nonneg_right he hv); rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_left (τgo j _ ht) (Real.exp_nonneg _)
lemma Temple (f:Site L.f→RodZ L n→ℝ)(hv:∀ j x,‖f j x‖ ≤ r* wigP (L:=L) p t j x)(ht:0<t)(he:0 ≤r): ‖∑ j,∑ x,f j x‖ ≤ r*tokenCost G n t:=by
          apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_left (κBudget p n ht) he); rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; rw [Finset.mul_sum]; apply (norm_sum_le ..).trans; exact sum_le_sum fun j _=> hv ..
lemma Prime (f:Site L.f→RodZ L n→Site L.f→RodZ L m→ℝ) (hv:∀ j x q y,‖f j x q y‖ ≤ (r*wigP (L:=L) p t j x)*wigP (L:=L) p t q y)(ht:0<t)(he:0 ≤r):
       ‖∑ j,∑ x,∑ q,∑ y,f j x q y‖≤ (r*tokenCost G m t)*tokenCost G n t:=by
            refine Temple p (n:=n) (r:=r*tokenCost G m t) _ (fun j x=>?_ ) ht (mul_nonneg he ?_); · exact (Temple p _ (hv j x) ht (mul_nonneg he (wake p t j x))).trans_eq (by ring)
            exact (sum_nonneg (fun j _=>sum_nonneg (fun i _=>wake p t _ _))).trans (κBudget p m ht)
end
end YM.OPE.Borealis.Galea
