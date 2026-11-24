import YM.OPE.Compatible.Sward.Cap
import YM.OPE.Compatible.Roost.Mood
import YM.OPE.Compatible.Lob.Top
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
open Flock Shift
open WithLp Exterior
open Tree Woody Stationary
variable {G:Gauge}{Q:Sponsor G}{T:Seasons Q}{v v' b η:ℝ}{R:ChartRatio G}
variable (h0:LocalRatio R)(P: Flight i j)(Y:Alps Q T i v) (D: Alps Q T j v') (B':Medal P.patch G Q.K i)(W:Aware d τ)(H:Mag i j)(he:Y.gear=P.wing)
variable (p:Tracts G d τ)
section
variable (hu:D.gear=P.land)(hs:G.Simple)(r:ℝ) (t: Era (boxF P Q H B' Y.gear) Y)
include hu h0 he hs
open Quit.PriceZ
set_option maxHeartbeats 200000 in
lemma castor (p:Tracts G d τ)(hp:ratios p k):
     let U:= boxF P Q H B' Y.gear
     let M:= (Fallix G W Q Y.gear H.1 p).val
     let V:= actor Y U R r (RollD.mk hs h0 t) W M
     TrueRay (L:=Q.K) P.land H.2.1 V k:=by
          intro U M V l; let f:= actor Y U R r ⟨hs,h0,t⟩ W; let Z':=FoldV W p (atlasF G Y.gear H.1 Q.K); let Y':=atlasF G P.land H.2.1 Q.K; let Sρ:=Drift.spread G d τ
          have hp0(q:Tower (Shade G) d τ): settled (m:=τ l) (f q l):=by
               have hh:= rainbow (d:=d) P.patch Q.K U Y R (Sρ q) r; rw[← (show Sρ (f q)=sculpt _ _ U _ _ _ _ _ from offered r Y U R ⟨hs,h0,t⟩ q W)] at hh; exact hh l
          apply kuff _ (turfy Y' _ _ (hp0 M)) (b:=fun _=>d+3*l.val); intro c
          obtain ⟨X,hX⟩:= Fonter P Y D B' H he hu hs r c; let g:=X.jet; let T':=fun a:ℕ=> g a*P.L; let Yα(i:ℕ):= FoldV W p (pointAt G Y.gear H.1 Q.K (T' i)); let Qω(i:ℕ):= f (Yα i)
          have hα:Tendsto Yα atTop (𝓝 M):=by rw [← (show FoldV W p _= M from chartX W p Y.gear H.1 (P:=Q))]; exact tideF W p atTop _ _ (farN G T' Y.gear _ Q.K (show Tendsto (fun i=> (T' i).val) atTop atTop from tendsto_atTop_mono (fun i=> Nat.le_mul_of_pos_right (g i).val P.L.pos) X.tip))
          have hv:Tendsto Qω atTop (𝓝 V):= (f.continuous.tendsto M).comp hα
          obtain ⟨A,hA,ht⟩:= liquidity P.patch Q.K (d:=d) U Y R hs h0 (m:=49) (j:=5) le_rfl r; let N(i):= A*‖Yα i‖
          refine lucid Q.K P.land H.2.1 (m:=τ l) (fun i=>Qω i l) (V l) g N X.yarn atTop X.tip (hα.norm.const_mul _) (tendsto_pi_nhds.mp hv l) (n₀:=glideZ d) (Eventually.of_forall ?_)
          intro i'; let x:=g i'; let y:= T' i'; let S:=subStud P.patch Q.K x; let Z:= X.traceX i'; let a:=X.paths i'; let g':=X.stems i'; let q:=Sρ (Yα i'); let A' := TracePay S P.patch.odd_side U Y g' a R d q r 0 Z
          have hpA:= X.accord i'; have ht':MoldH (Vessel Q.K P.land G x H.2.1) (Chart.tangent G (Body 1 x)) k A':=by
               have hh:=hpA; rw [hX i'] at hh; exact loyal h0 P Y B' W H he p x y rfl r 0 g' a hh Z hp
          have hT:=InkG (S.ratio.embed 0) (Yα i'); have hsT: CardM A' d:=pict Z.L R ((inkM q d (S.ratio.embed 0)) ∘ ribz S P.patch.odd_side) (shinesL _ _ hT) h0
          refine ⟨hp0 _,mul_nonneg hA (norm_nonneg _),skry A' l, ht' l,hsT l,fun u=>?_⟩
          rw [show LightP (0:Site x) (m:=τ l) _= _ from (levelT _ (f (Yα i')) l).symm]; unfold skry; rw [show Drift.spread _ _ _ _= sculpt P.patch Q.K U Y R r q d from offered r _ _ _ _ _ _, norm_sub_rev]; apply (ht (X.jet i') (X.light i') _ hpA g' Z 0 _ _ (resin (Yα i') (fun i=>by have h:= W.credit i;omega))).2 u l
end
end YM.OPE.Silt.Phere
