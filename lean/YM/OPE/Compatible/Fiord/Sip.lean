import YM.OPE.Compatible.Fiord.Day
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
local notation "H!"=> Yrent K G h
local notation "W!"=> (2*LockA G)
noncomputable def Jamt(K:KernelChoices)(G:Gauge)(h:4≤ i) (j:ℕ):ℝ:= (2* LockA G)*(1+ ↑(Nat.factorial j)* Yrent K G h)
lemma JPaid (hk:0<k): Fault Q! k (fun x=>Roster x) (Jamt K G h k):=by
       obtain ⟨hC,H⟩:= ΩcropExp (K:=K) V h μ; let g:= Ycrop (G:=G) (n:=n); let F:= Real.exp∘g; let v:ℝ:= k.factorial; let a:= H!; have he:0<v:= Nat.cast_pos.mpr k.factorial_pos; have hh:0≤a:=le_trans (integral_nonneg fun _=>(Real.exp_nonneg _)) H; let R:=1+v*a; have hr:1≤R:=le_add_of_nonneg_right (mul_nonneg he.le hh); let p(x):=‖g x‖^k; let Y:Bid.Dir G n→ℝ:=fun x=>v*F x; have hz: AEStronglyMeasurable g Q!:= ((skinV (G:=G) n).div_const _).aestronglyMeasurable
       have hp(x:Bid.Dir G n): p x ≤ Y x:=by
            unfold p Y; rw [Real.norm_of_nonneg (Ycrop_pos x),mul_comm v]; exact (div_le_iff₀ he).1 (Real.pow_div_factorial_le_exp _ (Ycrop_pos x) k)
       have hu := hC.const_mul v; have hP: Integrable p Q!:= hu.mono' (hz.norm.pow k) (Eventually.of_forall fun x=> (Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)).trans_le (hp x)); have hv: Fault Q! k g R:= Fault.ofInt (zero_le_one.trans hr) hk hz hP ?_; swap;· refine (integral_mono (f:=p) (g:=Y) hP hu hp).trans ?_; unfold Y; rw [integral_const_mul]; exact ((mul_le_mul_of_nonneg_left H he.le).trans (le_add_of_nonneg_left zero_le_one)).trans (le_self_pow₀ hr hk.ne') -- h inference
       let D:=2*LockA G; have hd: D>0:= mul_pos (by norm_num) (zero_lt_one.trans_le LockOne); have hh:= hv.scaling D; rw [Real.norm_of_nonneg hd.le] at hh; rw[show (fun x:Bid.Dir G n=>Roster x)=D • g from funext fun i=> (mul_div_cancel₀ _ hd.ne').symm]; exact hh
lemma overΩ (z:ℝ) : (Q!).real {x:Bid.Dir G n| (W!)*z< Roster x} ≤ (H!)*Real.exp (-z):=by
       obtain ⟨hC,H⟩:= ΩcropExp (K:=K) V h μ; let p:= Ycrop (G:=G) (n:=n); let W:= 2*LockA G; let D: Set (Bid.Dir G n):={x|W*z<Roster x}; have he:MeasurableSet D:=measurableSet_lt measurable_const (skinV _); have ht(x:Bid.Dir G n):D.indicator (fun _=>Real.exp z) x ≤ Real.exp (p x):=by
           by_cases hv:x∈D; rw[indicator_of_mem hv]; exact Real.exp_monotone ((le_div_iff₀ (mul_pos (by norm_num) (zero_lt_one.trans_le LockOne): 0<W)).mpr ((mul_comm ..).trans_le (le_of_lt hv))); rw[indicator_of_notMem hv]; exact Real.exp_nonneg _
       rw [Real.exp_neg, ← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]; have hh:=(integral_mono (μ:=Q!) ((integrable_const (Real.exp z)).indicator he) hC ht).trans H; change (∫ x:Bid.Dir G n,D.indicator _ x ∂Q!)≤ _ at hh; rw [integral_indicator he,setIntegral_const] at hh; exact hh
end
end YM.OPE.Ibis
