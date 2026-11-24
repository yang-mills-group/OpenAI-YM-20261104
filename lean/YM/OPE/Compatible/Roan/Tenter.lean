import YM.OPE.Compatible.Roan.Apt
/-! # tax economics clock root. pulmonary book. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "Kφ!"=> (L.ForestQ).Free
variable {N:ChartRatio G}(hN:LocalRatio N)(H:StackP N r R t)
open Dew AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate
noncomputable def Jh (i:(forest L.Z.ratio L.H).Free): L.DirA→L[ℝ] G.Color:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Kφ!=>G.Color) i) ∘L ContinuousLinearMap.snd ℝ (Bid.Dir G L.c) (AxisChart G Fθ)
def Pht (j:Site L.f):Seats Fθ:=Finset.univ.filter fun i=>i.val.1=j
noncomputable def reel (N:ChartRatio G)(j:Site L.f):L.DirA→ℝ:=∑ i∈ Pht L j,rake N ∘ Jh L i
noncomputable def turnt (N:ChartRatio G) (x:L.DirA):= taxY L.ForestQ N x.2
lemma paidF (N:ChartRatio G) (x:L.DirA): turnt L N x=∑ j:Site L.f,reel L N j x :=by unfold reel; simp_rw [Finset.sum_apply,Function.comp_apply]; change (∑ i:Kφ!,rake N (Jh L i x))=_; unfold Pht; exact (Finset.sum_fiberwise_of_maps_to (fun i (_:i∈(Finset.univ:Finset Kφ!))=> Finset.mem_univ i.val.1) ..).symm -- args
lemma scoreP (j:Site L.f) : (Pht L j).card ≤ 4 :=by
        let p:= Pht L j; rw[← Fintype.card_coe]; -- order? card_attach yields attach.card Coe(attach) extra
        refine le_trans (Fintype.card_le_of_injective (fun i:(p:Type)=>i.val.val.2) (fun i q hp=>?_)) ?_
        · exact Subtype.ext (Subtype.ext (Prod.ext (((mem_filter.mp i.property).2).trans ((mem_filter.mp q.property).2).symm) hp))
        rw [Fintype.card_fin]
include H hN
lemma teeP (s:ℝ) : Pile L.Z Fθ r (4*t) s 3 (turnt L N) (reel L N):=by
        have he(i:Kφ!)(x:L.DirA)(hx:‖x‖<r): Jh L i x∈ ball (0:G.Color) r:= mem_ball_zero_iff.mpr (((norm_le_pi_norm x.2 i).trans (le_max_right ..)).trans_lt hx); have ht(i:Kφ!)(x:L.DirA)(hx:‖x‖<r): ContDiffAt ℝ ω (rake N) (Jh L i x):= fade_fee hN _ (ball_subset_ball (H.sweep.small.le.trans ((min_le_left ..).trans (half_le_self hN.patch.le))) (he i x hx)); have hp(i:Kφ!)(x:L.DirA)(hx:‖x‖<r): ContDiffAt ℝ ω (rake N ∘ Jh L i) x:=(ht i x hx).comp x (Jh L i).contDiff.contDiffAt; refine ⟨fun {_} hx=> paidF L N _,fun i x hx=>?_ ,fun p x hx i hK=>?_⟩
        · rw [reel,show ∑ y∈Pht L i,_=_ from (show ∑ y∈Pht L i,rake N ∘ Jh L y= fun z=>∑ y∈Pht L i,rake N (Jh L y z) from funext fun _=>Finset.sum_apply ..)]; exact ContDiffAt.sum (fun k hk=>hp k x hx)
        intro d c h; unfold reel; rw [iteratedFDeriv_sum_apply (u:=Pht L p) (fun i hi=>(hp i x hx).of_le le_top), _root_.sum_apply]; apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun i=> t*∏ j,c j) (fun j hj=>?_)).trans ?_
        · have hh(k):‖Jh L j (d k)‖ ≤ c k:=by
             have ht:= (h k).2.2 j; have he:j.val.1=p:= (mem_filter.mp hj).2; simpa only [he,Progress.StationaryScenes.Green.wt,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using! ht
          rw [lin_rate_at (rake N) _ _ (ht j x hx)]; apply (ContinuousMultilinearMap.le_opNorm ..).trans; exact mul_le_mul (H.pays.2 _ (he j x hx) i hK) (prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=>hh i)) (prod_nonneg fun _ _=> norm_nonneg _) H.pays.1
        rw[sum_const,nsmul_eq_mul,mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast scoreP L p) (mul_nonneg H.pays.1 (prod_nonneg fun i _=>(h i).1))
end
end YM.OPE.Borealis.Galea
