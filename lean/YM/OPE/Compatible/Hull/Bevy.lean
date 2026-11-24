import YM.OPE.Compatible.Hull.Tim
import YM.OPE.Compatible.Spades.Lores
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
open Work.F08
section
lemma Omb (K:KernelChoices)(hz:4 ≤ i)(t:Shade G)(v:Shade G)(x:Cover){η:ℝ}(h:0<η):∀ᶠ n:Side in Filter.comap PNat.val atTop,∀ y:Train i,‖(rentV G y hz K n).val t v x - (atlasF G y hz K).val t v x‖≤ η:=by
     let L:= Filter.comap PNat.val atTop; have hx:∀ᶠ n:Side in L,∀ y:Train i, ‖(pointAt G y hz K n).val t v x-(atlasF G y hz K).val t v x‖ ≤ η/2:=by
          by_cases ht: t.2=v.2
          · have hv:=windward K _ (Exterior.coord t.1) (Exterior.coord v.1) x (half_pos h) hz; filter_upwards [hv] with n hn z; simpa only[pointAt,atlasF,if_pos ht] using hn z
          filter_upwards with n z; simp only [pointAt,atlasF,if_neg ht,sub_zero,norm_zero]; positivity
     have hv : Tendsto (fun n:Side=> ((n.val:ℝ)^4)⁻¹) L (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α:=ℝ) (by decide : 4≠0)).comp (tendsto_natCast_atTop_atTop.comp (show Tendsto PNat.val L atTop from tendsto_comap)))
     filter_upwards [hx,hv.eventually (ge_mem_nhds (half_pos h))] with n hn hy z; let T:= if t=v then ((n.val:ℝ)^4)⁻¹ else 0; have hp:‖T‖≤η/2:=by unfold T; split; rw[Real.norm_of_nonneg (by positivity)]; exact hy; rw [norm_zero]; exact (half_pos h).le
     unfold rentV; rw[add_sub_right_comm]; exact ((norm_add_le ..).trans (add_le_add (hn _) hp)).trans_eq (add_halves ..)
lemma Solv (K:KernelChoices)(hz:4 ≤ i)(t:ℝ)(a:ℝ)(b k m:ℕ) (G:Gauge)(ha:0 < a):∀ᶠ n:Side in Filter.comap PNat.val atTop,∀ y:Train i,∀ p∈ Hoard G b k m,
       ‖boostS (rentV G y hz K n) t m k p-boostS (atlasF G y hz K) t m k p‖ ≤ a*‖p‖:=by
            let c:= (terra_money K hz).choose+1; let U(i:ℕ):= t^i/(i.factorial:ℝ); let d(i:ℕ):= spanKΩ c k i
            let C:= ∑ i∈range (k+1),‖U i‖*‖d i‖; let g:= a/(C+1); have he:0≤C:=sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _); have hv:0<g:= div_pos ha (by positivity); let l:= Filter.comap PNat.val atTop; let V(y:Train i)(n:Side):= rentV G y hz K n; let W(y:Train i):=atlasF G y hz K; have ht:∀ᶠ n in l,∀ x: ↑(Taxon G b),∀ i j,∀ y,‖(V y n).val i j x.val-(W y).val i j x.val‖≤ g:= eventually_all.mpr fun x=>eventually_all.mpr fun i=>eventually_all.mpr fun j=>Omb K _ i j x.val hv -- names
            filter_upwards [ht] with N h V' p hh; let A:=V V' N; let B:= W V'; let f:=(lapD A m k).toLinearMap; let v:=(lapD B m k).toLinearMap; rw[boostS,Hflow,boostS,Hflow,← sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> ‖U i‖*‖d i‖* (g*‖p‖)) (fun i _=>?_)).trans ?_); · let P:=(f^i) p; let X:=(v^i) p; change ‖U i • P-U i • X‖≤_; rw [← smul_sub,norm_smul]; rw[_root_.mul_assoc ‖U i‖]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (flareNorm A B (a:=c) rfl.le (by exact le_add_of_nonneg_right (zero_le_one:0≤(1:ℝ))) hv.le (fun i hi j k=>h ⟨i,hi⟩ j k V') _ hh i).trans; rw [← _root_.mul_assoc]; gcongr; exact Real.le_norm_self (d i)
            rw [← sum_mul]; change C*(g*‖p‖)≤ _; rw [← _root_.mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold g; rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).2; linarith
end
end YM.OPE.Spells
