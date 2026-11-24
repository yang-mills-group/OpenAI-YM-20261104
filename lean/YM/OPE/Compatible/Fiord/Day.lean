import YM.OPE.Compatible.Fiord.Well
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
open Merchant Merchant.Aloof Merchant.Sleeve Variance
open Wool
local notation "μ!"=> Chart.tangent G (Body 1 n)
local notation "Ψ"=> Vessel K V G n h
variable (μ:Measure (Bid.Dir G n)) [μ.IsAddHaarMeasure]
open Merchant.Sleeve
set_option quotPrecheck false
local notation "L_t"=> Vessel K V G n h
local notation "Q!"=> quart (L_t) μ
noncomputable def Yrent (K:KernelChoices)(G:Gauge)(h:4 ≤ i):ℝ:= Real.exp 1+Squad 0 1* ∑ _a:Axis,∑ _j:G.ColorIndex,2*Real.exp (Θscrew K h/2)
lemma αCrop : Integrable (ΨCap G n) Q! ∧ (∫ x, ΨCap G n x ∂ Q!) ≤ Yrent K G h:=by
       let L:= L_t; let ν:= quart L μ; let f(y:Site n)(p:Axis)(k:G.ColorIndex):= YnT G n (y,p) k; let P(y:Site n)(x:Bid.Dir G n):= ∑ p:Axis,∑ k:G.ColorIndex,StemUp (f y p k) x; let F(x:Bid.Dir G n):=∑ i:Site n,knotter 0 1 i*P i x; have hP(i:Site n): Integrable (P i) ν:= integrable_finsetSum _ fun a _=> integrable_finsetSum _ fun j _=> (Cinders.stem _ _ _).1; have hf:Integrable F ν:= integrable_finsetSum _ (fun i _=> (hP i).const_mul _); haveI : IsProbabilityMeasure ν:=inferInstanceAs (IsProbabilityMeasure (quart L μ)); refine ⟨(integrable_const _).add hf,?_⟩; let q:= Real.exp 1; change (∫ x,q+F x ∂ν) ≤ _; rw [integral_add (integrable_const (μ:=ν) q) hf, integral_const, probReal_univ,one_smul]; let a:= 2*Real.exp (Θscrew K h/2); let t:=∑ _i:Axis,∑ _j:G.ColorIndex,a; change q+ _≤ q+ Squad 0 1*t; apply add_le_add le_rfl; unfold F; rw [integral_finsetSum univ (fun i _=> (hP i).const_mul _)]; simp_rw[integral_const_mul]
       apply le_trans (sum_le_sum (g:=fun j=> knotter 0 1 j*t) (fun i _=>?_)); swap
       · apply mul_le_mul_of_nonneg_left _ (knotPos .. |>.le); unfold P; rw [integral_finsetSum univ (fun p _=> integrable_finsetSum _ (fun j _=>(Cinders.stem L μ _).1))]; refine sum_le_sum fun p _=>?_ ; rw [integral_finsetSum univ (fun i _=>(Cinders.stem L μ _).1)]; refine sum_le_sum fun j _=>?_; rw [show (∫ x,StemUp _ _ ∂ν)= _ from (Cinders.stem L μ (f i p j)).2]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right ((Real.le_norm_self _).trans ((breathQ K V G n h).2 (i,p,j))) (by norm_num))) (by norm_num)
       rw [← Finset.sum_mul]; refine mul_le_mul_of_nonneg_right (knot_sum _ _ zero_lt_one) (sum_nonneg fun i _=> sum_nonneg fun j _=> (mul_nonneg zero_le_two (Real.exp_nonneg _)))
-- point growth.R used Lp budget
lemma ΩcropExp : Integrable (Real.exp ∘ (Ycrop (G:=G) (n:=n))) Q!∧ (∫ x,Real.exp (Ycrop x) ∂ Q!) ≤ Yrent K G h:=by
       let f:Bid.Dir G n→ℝ:=Real.exp∘ Ycrop; have hv: Measurable f:= Real.continuous_exp.measurable.comp ((skinV (G:=G) n).div_const _); obtain ⟨hP,H⟩:=αCrop (K:=K) V h μ; have he: Integrable f Q!:=hP.mono' hv.aestronglyMeasurable (Eventually.of_forall fun x=>(Real.norm_of_nonneg (Real.exp_nonneg _)).trans_le (μcap x)); exact ⟨he,(integral_mono he hP μcap).trans H⟩
end
end YM.OPE.Ibis
