import YM.OPE.Compatible.Blaze.Dais
/-! # Quadratic score interchange -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Woody Virgin Work.F08 Coin
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open YM.AnalyticNext.QuarticMatch.Joint
variable {N c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis) (S:StepData c f) (h:Odd S.ratio.count.val)
local notation "Fr"=> forest S.ratio h
local notation "X"=> Bid.Dir G c
local notation "Y"=> AxisChart G (forest S.ratio h)
def Zig : X × Y→L[ℝ] X × Y:= ContinuousLinearMap.prodMap (streak a G c) (plank a S.ratio h)
lemma Zag (i:X×Y): Zig a S h (Zig a S h i)=i:=Prod.ext (sigma_twice _ i.1) (bloom2 _ _ _ i.2)
-- ratio in Hop
lemma accord (V:PathData G)(b:Clip) (t:S.Choices) (hp: S.patch.Branches S.kernel G): pane Fr t b V ∘ (Zig a S h)=ᶠ[𝓝 0] pane Fr t b V:=by
     let A:= fun x:X × Y=> fieldF Fr x.2; have hm:Tendsto A (𝓝 0) (𝓝 1):=by
          let T := fun x:AxisChart G Fr=>input G f (Stationary.pad Fr x); have hp: Tendsto (T ∘ Prod.snd) (𝓝 (0:X×Y)) (𝓝 1):=by
                have hE :Continuous T:=by apply continuous_pi; intro i; unfold T; simp_rw [input_color]; fun_prop
                simpa only [T,map_zero, Prod.snd_zero,Function.comp_apply,input_zero] using! (hE.comp continuous_snd).tendsto (0:X×Y)
          simpa only [A,T, fieldF, spoolP] using! hp
     filter_upwards [hm.eventually (Work.F04.prediction_germ hp (S.withinChoice (Wm a) 0 t) t)] with i hi; let X' := Wm a; change mainTerm _ _ (fieldF Fr (plank a S.ratio h i.2))+noiseTaylor _ (represent (shifts X' 0 i.1)) (fieldF Fr (plank a S.ratio h i.2)) _=_; rw [EPath, rep_shifts, main_pull]; unfold noiseTaylor; rw [← show S.ratio.embed 0=0 from S.ratio.root.map_zero]; rw [S.prediction_channel hp,show S.prediction (fieldF Fr i.2) _=_ from hi]; exact congr_arg (mainTerm b V (fieldF Fr i.2) + ·) (energy_channel ..)
lemma Ziggle : ribz S h (G:=G) ∘L Zig a S h= streak a G f ∘L ribz S h:=by
     let L₁:=ribz S h (G:=G) ∘L Zig a S h; let L₂:=streak a G f ∘L ribz S h; have he:(L₁: X × Y →_) =ᶠ[𝓝 0] L₂:= by
          have hg:Tendsto L₁ (𝓝 0) (𝓝 0):= by simpa only[map_zero] using L₁.continuous.tendsto 0
          have ht:Tendsto L₂ (𝓝 0) (𝓝 0):= by simpa only[map_zero] using L₂.continuous.tendsto 0
          filter_upwards [hg.eventually rec_end,ht.eventually rec_end] with x hx hy; apply hx.symm.trans; refine Eq.trans (congr_arg records ?_) hy; change represent (ribz S h (Zig a S h x))=represent (streak a G f (ribz S h x)); rw [ frameReal, streak, rep_shifts, frameReal]; exact EPath ..
     simpa only [ContinuousLinearMap.fderiv] using he.fderiv_eq (𝕜:=ℝ)
variable {K:Sponsor G}{T:Seasons K}{i:ℕ}{v u r':ℝ}{A:Alps K T i v}{b:ℝ}
variable (U:Boxes G S.patch S.kernel) (t:S.Choices){Z:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio h)} (L':FibreRep S h U t A g b)(H:licensed S h U A.clip A.live Z A.sky g)
attribute [local instance] Gauge.frobInner
include H L'
open Radial
lemma lamp_fee : L'.L.f ∘ (Zig a S h)=ᶠ[𝓝 0] L'.L.f:=by
     let Y':= Zig a S h (G:=G); have ht:Tendsto Y' (𝓝 0) (𝓝 0):= by simpa only [map_zero] using Y'.continuous.tendsto 0
     filter_upwards [accord a S h A.live A.clip t H.1.cover,L'.meter,ht.eventually L'.meter] with i hi hj hk; exact hk.trans ((congr_arg (·-pane Fr t A.clip A.live 0) hi).trans hj.symm)
lemma lamp_coin (x:X×Y)(j:ℕ)(_hj:j ≤ 4): jet L'.L.f j (Zig a S h x)=jet L'.L.f j x:=by
     let V:=Zig a S h (G:=G); have he:ContDiffAt ℝ ω (pane Fr t A.clip A.live) 0:=(viewer t H.2.1).origin
     have ht : ContDiffAt ℝ ω L'.L.f 0:= (he.sub (contDiffAt_const (c:=pane Fr t A.clip A.live 0))).congr_of_eventuallyEq L'.meter
     unfold jet; conv_rhs => rw [← ((lamp_fee a S h U t L' H).iteratedFDeriv ℝ j).eq_of_nhds, jets_linear _ (ht.of_le le_top)]
     rfl
omit H L' in
lemma poolV (p:LocalRatio P): let V:=plank a S.ratio h (G:=G);taxY Fr P ∘ V=ᶠ[𝓝 0] taxY Fr P:=by
    intro V; filter_upwards [Metric.ball_mem_nhds (0:Y) p.patch] with x hx; rw [ball_pi _ p.patch] at hx; change (∑ i:(forest S.ratio h).Free, rake P (plank a S.ratio h x i))=∑ i:(forest S.ratio h).Free,rake P (x i); rw [← Equiv.sum_comp (atlasW a S.ratio h) (g:= fun i=>rake P (x i))]; apply Finset.sum_congr rfl; intro i _; rw [bloom];split; exact congr_arg Real.log (Next.SectorChange.ratio_even p (hx _ (Set.mem_univ _))).symm; rfl
omit H L' in
lemma ringJ (p:LocalRatio P): Chart.jacobian P∘ (plank a S.ratio h (G:=G))=ᶠ[𝓝 0] Chart.jacobian P:=by
    let V:=plank a S.ratio h (G:=G); let c:=jackpot P (forest S.ratio h).Free; have ht:= parW (I:=(forest S.ratio h).Free) P p; filter_upwards [poolV a S h p,ht,(show Tendsto V (𝓝 0) (𝓝 0) from (by simpa using V.continuous.tendsto 0)).eventually ht] with x hx hz hv; change (Chart.jacobian P) (V x) = _; rw [hv,hz]; apply congr_arg Real.exp; exact congr_arg (fun i=>i+c) (show taxY Fr P (V x) = taxY Fr P x from hx)
lemma ωsign : L'.L.w ∘ Zig a S h=ᶠ[𝓝 0] L'.L.w:=by
    let Q':= Zig a S h (G:=G); let E:= plank a S.ratio h (G:=G); have hu:Tendsto Q' (𝓝 0) (𝓝 0):= by simpa only [map_zero] using Q'.continuous.tendsto 0
    filter_upwards [L'.serves,hu.eventually L'.serves,accord a S h A.live A.clip t H.1.cover] with x hx hh hy; change L'.L.w (Q' x)=L'.L.w x; rw [hx,hh]; apply congr_arg Real.exp; refine congr_arg₂ (·-·) (congr_arg ((-b)* ·) hy) ?_; change springF Fr A.live (plank a S.ratio h x.2)= _; unfold springF; rw [EPath,loopChannel]
lemma toll_v (p:LocalRatio P): (L'.L.wSign P) ∘ Zig a S h =ᶠ[𝓝 0] L'.L.wSign P:=by
     let U' := ContinuousLinearMap.snd ℝ X Y; have hy:Tendsto U' (𝓝 0) (𝓝 0):= by simpa only [map_zero] using U'.continuous.tendsto 0
     filter_upwards [ωsign a S h U t L' H,hy.eventually (ringJ a S h p)] with x hx hv; change (L'.L.w (Zig a S h x))*Chart.jacobian P _=_; exact congrArg₂ (fun (i j:ℝ)=>i*j) hx hv
end YM.OPE.Quit
