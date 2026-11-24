import YM.OPE.Compatible.Nut.Sky
/-! # Lens calibration along counters -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
namespace Zest
section
open Pressure ConnectedActivityE6 Shell Channel
variable {E F:Type*}{Z B u x a:I→ℝ}{l:Filter I}{y:I→E}{w:I→ℝ}[Norm E]
lemma fScale (hx: Tendsto Z l atTop)(hc:Tendsto (fun i=>B i/Z i) l (𝓝 1))(ht:RateLE l B y t): RateLE l Z y t:=by
       intro x hx'; obtain ⟨v,hv,hX⟩:=exists_between hx'; have hz:= hc.const_mul v; rw [mul_one] at hz; filter_upwards [ht v hv,hz.eventually (gt_mem_nhds hX),hx.eventually_gt_atTop 0] with i hi h ht; have h' : v*(B i/Z i)< x:=h; rw[←mul_div_assoc,div_lt_iff₀ ht] at h'; exact hi.trans (Real.exp_monotone h'.le)
lemma foTest (hx:Tendsto Z l atTop)(he:RateIs l (Counters Z) B 1)(hv:Wax B l y s): Wax Z l y s:=fScale (carth hx) he.rate hv
lemma σTilt (hz: Tendsto Z l atTop) (hv:RateIs l (Counters Z) B 1)(hK:Tendsto B l atTop)(hx: Receipt B l y): Receipt Z l y:=by
        let T':= carth hz; obtain ⟨k,hk⟩:=hx.fitsQ (carth hK); refine ((sans hz).product (Score.steady (2:ℝ) T')).power k T'|>.under ?_; filter_upwards [hk,(carth hK).eventually_ge_atTop 0, T'.eventually_gt_atTop 0,hv.rate.eventually (gt_mem_nhds (show (1:ℝ)<2 by norm_num))] with i hi hv h hK; have ht: Counters B i /(Counters Z i)< 2:= hK; exact hi.trans (pow_le_pow_left₀ hv ((div_lt_iff₀ h).1 ht|>.le.trans_eq (mul_comm ..)) _)
lemma fScale2 (hx:Tendsto Z l atTop)(hc:Tendsto B l atTop)(h:Tendsto (fun i=>B i/Z i) l (𝓝 1))(ht:RateIs l B x s): RateIs l Z x s:=by refine ⟨ht.pos, ?_⟩; have hQ:= ht.rate.mul h; rw [mul_one] at hQ; refine hQ.congr' ?_; filter_upwards [hc.eventually_gt_atTop 0,hx.eventually_gt_atTop 0] with i hp he; field_simp
lemma Ωζ (_hx:Tendsto Z l atTop)(hc:Tendsto B l atTop)(he: RateIs l (Counters Z) B 1) (hb:Wax Z l y t): Wax B l y t:=by
       refine fScale (carth hc) ?_ hb; have hx := he.rate.inv₀ one_ne_zero; rw [inv_one] at hx; exact hx.congr fun i=> by rw[inv_div];rfl
end
end Zest
end YM.OPE.Lass
