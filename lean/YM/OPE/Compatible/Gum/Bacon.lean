import YM.OPE.Compatible.Gum.Vision
/-!
# All trace accounts, ordinary torque identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- accounting index and oriented trans
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
open Flume.Script Shell
local notation "T!"=> Flume.Script.Tile G S.ratio.count
open Planned.PrimaryIntegral295.Carrier
open AnalyticNext.QuarticMatch.Joint
lemma loopChannel (s:Signed) (b:Site c) (R:PathData G) (U:Config G c): Precision.loop R (pull s b U)=Precision.loop R U:= by
  unfold Precision.loop Patch.average; apply congr_arg; conv_rhs=> rw [← Equiv.sum_comp (Equiv.mulLeft s)]
  refine Finset.sum_congr rfl fun i _=> ?_; dsimp only; rw [pull_pull,translate_by, uncut_translate]; rfl
include ht
lemma twirlTX (v:Kv): taxY X! P ∘ twirlF S he H v =ᶠ[𝓝 0] taxY X! P:=by
     filter_upwards [Metric.ball_mem_nhds (0:Z!) ht.patch] with x hx; rw [ball_pi _ ht.patch] at hx; change (∑ i:(forest S.ratio he).Free, _)=∑ i:(forest S.ratio he).Free,rake P (x i); rw [← (fernV S he H v).sum_comp (g:= fun i=>(rake P (x i)))] -- occ
     refine Finset.sum_congr rfl fun i _=>?_; rw [spinF0]; split
     next h=> exact congr_arg Real.log (Next.SectorChange.ratio_even ht (hx (trainV S he H v i) (Set.mem_univ _))).symm
     next h=>rfl
include H S G g L U h A t
lemma twirlHero (b:ℝ)(v:Kv): HaloC S he t b A P ∘ DoubleX S he H v=ᶠ[𝓝 0] HaloC S he t b A P:=by
     let F:=f; let W:=DoubleX S he H v (G:=G); let Z:= twirlF S he H v (G:=G); filter_upwards [priceDX S he H (G:=G) (p:=A.clip) (R:=A.live) h.1.cover v t, (continuous_snd.tendsto (0:S!)).eventually (twirlTX S he H ht v)] with i hi hz; unfold HaloC; rw [Function.comp_apply]; rw [show pane X! t A.clip A.live (DoubleX _ _ _ _ i) = _ from hi,show (DoubleX S he H v i).2=Z i.2 from rfl,show taxY X! P (Z i.2)= _ from hz]; unfold springF; rw [show fieldF X! (Z i.2)= _ from pullFZ S he H v i.2, loopChannel]
lemma halock (b:ℝ): Litlock S he H (tide2 S.patch S.kernel A.live A.clip P b):=by
      let Q:=tide2 S.patch S.kernel A.live A.clip P b; have ht':folk Q:=(tide_feed S (A:=A) b P).1; let Z:=dance S he G;let F:= HaloC S he t b A P; intro k v; let W:= DoubleX S he H k (G:=G); have heX: F ∘ W=ᶠ[𝓝 0] F:= twirlHero S he H U t h ht b _; have hy:ContDiffAt ℝ ω F 0:= (bandC S he t ht b (viewer t h.2.1).origin (0:S!)).1
      let y:= listV Q c; let T:= y.compContinuousLinearMap (fun (_:Fin 2)=>Z); have hp: Q.Idem:=stampV _ (folk_whole (folkS (folkF (folkF (folkS (folkS (penne_unit _ _ _ _ A.pays _) _) _) (folkS (Boxes.folk_collar S.patch A.pays) _)) (Boxes.folk_cap S.patch P)) _))
      have hv(v:Fin 2→ S!): T v= library c Q (Z ∘ v):= muses _ (folk_whole ht') _; erw [← hv (W ∘ v),← hv]
      have hh : (T.compContinuousLinearMap (fun _ : Fin 2=> W))=T:=by
            have hh : Tensor.Sym T:= fun v i=> pointed hp (folk_whole ht') _ (Z ∘ v) i
            apply Tensor.ext_diag _ _ (fun v i=> hh (W ∘ v) i) hh; funext i
            have hi: jet F 2 (W i)=jet F 2 i:=by
                conv_rhs=> unfold jet; rw [← (heX.iteratedFDeriv ℝ _).eq_of_nhds, jets_linear W (hy.of_le le_top)]
                rfl
            rw [show Tensor.diagonal _ i= T (fun _ : Fin 2=> W i) from rfl]
            exact (hv _).trans ((beam2 S he U t h ht _ b).trans ((congr_arg (fun z:ℝ=>4*z) hi).trans ((hv (fun _=> i)).trans (beam2 S he U t h ht i b)).symm))
      exact DFunLike.congr_fun hh v
omit ht
lemma voteLock (n:ℕ)(r:ℝ): Litlock S he H (r • (show Script T! n from voteV S.patch S.kernel A.live A.clip n)):=by
     intro k x; rw [libScale,libScale]; apply congr_arg; let Z:=DoubleX S he H k (G:=G); have he' :=priceDX S he H (p:=A.clip) (R:=A.live) h.1.cover k t; have hh:= vote_here S he h.1.cover t A.clip A.live A.pays n (Z ∘ x); refine hh.trans (Eq.trans ?_ (vote_here S he h.1.cover t A.clip A.live A.pays n x).symm); refine Eq.trans ?_ (DFunLike.congr_fun ((he'.iteratedFDeriv ℝ n).eq_of_nhds) x); rw [jets_linear _ ((viewer t h.2.1).origin.of_le le_top)];rfl
end YM.OPE.Cascade.Rill
