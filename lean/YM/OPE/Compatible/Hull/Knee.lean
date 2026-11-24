import YM.OPE.Compatible.Hull.Vast
import YM.OPE.Compatible.Hull.Nook
import YM.OPE.Compatible.Hull.Spoon
import YM.OPE.Compatible.Hull.Bud
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
open Source Labels Source.Drops
section
open Beamer
variable {H:Hol G}{θ:ℝ}(P:Pad G)(f:Config G n→ℂ)(t:ℝ) (U:BudgetPoint)(h:2*(b+1)<n.val)(Q:Acceptance o U (k+6) f b θ)(A:ℂ→L[ℝ]ℝ)
variable {d:ℕ} (W:Snap G d)
lemma Alt (hv:2*(4*b+1)<n.val)(u:Snap G d)(z:ℝ)(w:ℝ): Exposure b (board (expandAt o (south H o u w z)))= burstQ H b (w • Spindle.flash u z):=by
       let V:= H.links d (expand d (w • u)) z; have hV: V= Hig H (w • Spindle.flash u z):=by rw [show w • Spindle.flash _ _= _ from (flash_smul ..).symm]; exact Drops.scales .. -- direction
       let U:= expandAt o (south H o u w z); have hh: Agrees (Lattice.box (4*b)) U V:= content hv H _ d z; have hx(x:Cover)(hx:x∈Lattice.box b): incG U x= incG V x:= travel_local _ _ _ _ (fun i hi hk=> hh _ (Tumb x hx _ hi) (Tumb _ hx _ hk)); unfold burstQ; rw[←hV]; apply congr_arg (strideG G b); ext1 i; rw [show InLine b (board U) i=G.curvature _ from CurU .., show InLine b (board V) i=G.curvature _ from CurU ..]; apply congr_arg; change incG U _*U _*(incG U _)⁻¹= incG V _*V _*(incG V _)⁻¹; rw [hx _ i.property.1,hx _ i.property.2,hh i.val (voles (by omega) i).1 (voles (by omega) i).2]
lemma lateU (l:Edge (Site n))(w:ℝ):Tendsto (fun z=> G.chord (south H o W w z l)) (𝓝 0) (𝓝 0):=by
       let x:Edge Cover:=(Lattice.lift (l.1-o),l.2); have hp(z:ℝ):south H o W w z l= Hig H (Spindle.flash (w • W) z) x:=congr_fun (Drops.scales H _ z) x; simp_rw [hp]; let u:= fun v:Snap G d=> Hig H v x; have hv : Tendsto u (𝓝 0) (𝓝 1):=by
         apply ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.tendsto_nhds_iff).2
         rw [← (show u 0=1 from (Work.G02.linkGerm H d x).2.1)]; exact (Work.G02.linkGerm H d x).1.continuousAt.tendsto
       have hz : Tendsto (Spindle.flash (w • W)) (𝓝 0) (𝓝 0):=by simpa using! (flashDiff (n:=1) (w • W)).contDiffAt.continuousAt.tendsto (x:=0)
       exact (show Tendsto G.chord (𝓝 1) (𝓝 0) from by simpa using G.continuous_chord.tendsto 1).comp (hv.comp hz)
noncomputable def JargonR (t:ℝ)(U:BudgetPoint)(H:Hol G)(W:Snap G d)(b:ℕ):ℝ→Scoop G b:= (Θrank t U.threshold)⁻¹ • sprintD H b U.threshold W
include Q
lemma Sol (ht:t≠0)(hx:2*(4*b+1)<n.val):
       (fun i:ℝ=>A (f (south H o W U.threshold i)))=ᶠ[𝓝 0] Artifact o P h U f A t ∘ JargonR t U H W b:=by
           let w:=U.threshold; let L i:= south H o W w i; have hh: ∃ s:ℝ, 0<s ∧ Belts b*s≤P.B∧ sizeQ b*(w⁻¹*(Belts b*s))^2≤ P.r^2/2:=by
                have hs: Tendsto (fun s:ℝ=> Belts b*s) (𝓝[>] (0:ℝ)) (𝓝 0):=by simpa only[mul_zero] using! tendsto_const_nhds.mul (tendsto_nhdsWithin_of_tendsto_nhds (s:=Set.Ioi _) (tendsto_id (x:=𝓝 (0:ℝ))))
                have hv: Tendsto (fun s:ℝ=> sizeQ b*(w⁻¹*(Belts b*s))^2) (𝓝[>] (0:ℝ)) (𝓝 0):=by simpa using (tendsto_const_nhds (x:=sizeQ b)).mul (((tendsto_const_nhds (x:=w⁻¹)).mul hs).pow 2)
                exact ((show ∀ᶠ i in 𝓝[>] (0:ℝ),0 < i from self_mem_nhdsWithin).and ((hs.eventually (ge_mem_nhds P.hB)).and (hv.eventually (ge_mem_nhds (div_pos (pow_pos P.pos _) (by norm_num)))))).exists
           obtain ⟨s,hs,hb,hz⟩:=hh; have hE(i:Dim o (4*b)): ∀ᶠ z in 𝓝 (0:ℝ), G.chord (L z i.val) ≤ s := (lateU (H:=H) o W i.val w).eventually (ge_mem_nhds hs); filter_upwards [eventually_all.mpr hE] with r hr; have hv:= chanting o P h U f A _ Q (L r) ht s hs.le hr hb hz; change A (f (L r))=_; rw [←hv]; apply congr_arg; rw [Exposure,_root_.map_smul,_root_.map_smul]; -- adjust
           change t⁻¹ • Exposure b (board (expandAt o (south H o W w r)))= _; rw [Alt o hx W r w]; change _ = (Θrank t w)⁻¹ • (w⁻¹ • burstQ H b (w • Spindle.flash W r)); rw [smul_smul]; refine congr_arg (fun x:ℝ=>x • burstQ H b (w • Spindle.flash W r)) ?_; unfold Θrank; rw [_root_.mul_inv_rev,_root_.inv_inv,mul_right_comm,mul_inv_cancel₀ (show w ≠0 from U.threshold_pos.ne'),one_mul]
end
end YM.OPE.Spells
