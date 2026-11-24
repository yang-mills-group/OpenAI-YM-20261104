import YM.OPE.Compatible.Fiord.Eye
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
noncomputable abbrev YnT (G:Gauge)(n:Side)(e:Edge (Site n))(a:G.ColorIndex): Module.Dual ℝ (Bid.Dir G n) := Ferry (spool G n).toContinuousLinearMap (e.1,e.2,a)
lemma oHψ (x:Bid.Dir G n)(e:Edge (Site n))(a:G.ColorIndex): YnT G n e a x=(Phone G).coord a (x (arkE e)):=by rw [phone_eq];rfl
noncomputable def LockA (G:Gauge):ℝ:=1+∑ i:G.ColorIndex, ‖Phone G i‖
lemma LockOne : 1 ≤ LockA G:=le_add_of_nonneg_right (sum_nonneg fun _ _=>norm_nonneg _)
lemma overlook (x:Bid.Dir G n)(c:ℝ)(hc:0 ≤ c)(h:∀ e:Edge (Site n),∀ a:G.ColorIndex, ‖YnT G n e a x‖ ≤ costume e.1*c): Roster x ≤ LockA G*c:=by
       refine receiveE x _ (mul_nonneg (zero_le_one.trans LockOne) hc) ?_ ; intro i; obtain ⟨i,h'⟩:=arkSur i; rw [← h']; nth_rw 1 [← (Phone G).sum_repr (x (arkE i))]; apply (norm_sum_le ..).trans; let f(a:G.ColorIndex):= ‖Phone G a‖; apply le_trans (b:=∑ a:G.ColorIndex,(costume i.1*c)*f a) (sum_le_sum fun j _=>?_) _
       · rw [← mul_sum]; let T:=costume i.1; change T*c*_ ≤ T*(LockA G*c); rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (Wool.tensile _|>.le); rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hc
       rw[norm_smul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); have ht:=h i j; rw [oHψ] at ht; exact ht
noncomputable def Ycrop (x:Bid.Dir G n):ℝ:= Roster x/(2*LockA G)
lemma Ycrop_pos (x:Bid.Dir G n):0 ≤ Ycrop x:= div_nonneg (ros _) (mul_nonneg zero_le_two (zero_le_one.trans LockOne))
lemma Ycrop_pop (x:Bid.Dir G n)(he:1 < Ycrop x): ∃ (e:Edge (Site n))(i:G.ColorIndex),Ycrop x +↑(pdist e.1) ≤ ‖YnT G n e i x‖:=by
       let a:= Ycrop x; let b:= LockA G; have h:0 < b:= zero_lt_one.trans_le LockOne; have hz: Roster x=2*b*a:=(mul_div_cancel₀ _ (mul_pos two_pos h).ne'|>.symm) -- #check
       by_contra q; push Not at q; have Q:Roster x ≤ b*a:=overlook x a (Ycrop_pos x) (fun e i=>?_); swap; · refine le_trans (le_of_lt (q e i)) ?_; change a+_ ≤ (1+(pdist e.1:ℝ))*a; nlinarith [mul_le_mul_of_nonneg_left he.le (Nat.cast_nonneg (α:=ℝ) (pdist e.1))]
       change 1<a at he; nlinarith
noncomputable def ΨCap (G:Gauge)(n:Side)(x:Bid.Dir G n):ℝ:= Real.exp 1+ ∑ i:Site n,knotter 0 1 i*∑ a:Axis,∑ j:G.ColorIndex, StemUp (YnT G n (i,a) j) x
lemma μcap (x:Bid.Dir G n): Real.exp (Ycrop x) ≤ ΨCap G n x:=by
        let f(y:Site n)(a:Axis)(j:G.ColorIndex):= StemUp (YnT G n (y,a) j) x; let g(y:Site n):=∑ a:Axis,∑ j:G.ColorIndex,f y a j; have he(y:Site n)(a:Axis)(j:G.ColorIndex) : 0 ≤ f y a j:=add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _); unfold ΨCap; by_cases hp:Ycrop x ≤ 1; · refine (Real.exp_monotone hp).trans (le_add_of_nonneg_right (sum_nonneg fun i _=>mul_nonneg (knotPos ..|>.le) (sum_nonneg fun a _=>sum_nonneg fun j _=>he i a j)))
        obtain ⟨⟨i,a⟩,u,hx⟩:=Ycrop_pop x (not_le.mp hp); let d:ℝ:=pdist i; have hK:knotter 0 1 i=Real.exp (-d):=by simp [knotter,d]
        apply le_trans _ (le_add_of_nonneg_left (Real.exp_nonneg _)); refine le_trans ?_ (single_le_sum (f:=fun i=>knotter 0 1 i*g i) (fun i _=>mul_nonneg (knotPos ..|>.le) (sum_nonneg fun a _=>sum_nonneg fun j _=>he i a j)) (mem_univ i)); rw[hK,show Real.exp (Ycrop x)=Real.exp (-d)*Real.exp (Ycrop x+d) from ?_]; swap;· rw [←Real.exp_add];ring_nf
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _); exact ((Real.exp_monotone hx).trans (bound_p ..)).trans ((single_le_sum (s:=univ) (f:=f i a) (fun j _=>he i a j) (mem_univ u)).trans (single_le_sum (f:=fun a=>∑ j,f i a j) (fun a _=>sum_nonneg fun j _=>he i a j) (mem_univ a)))
end
end YM.OPE.Ibis
