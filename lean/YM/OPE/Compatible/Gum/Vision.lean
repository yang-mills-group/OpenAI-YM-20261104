import YM.OPE.Compatible.Gum.First
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
-- records scripts on Vanishing(h) weights. symmetric by default
open AnalyticNext.QuarticMatch.Joint Page
local notation "M!"=> pane X! t A.clip A.live
def tide3 (P: Patch)(K:KernelChoices)(R:PathData G)(c:Clip): Script (Script.Tile G P.L) 3:=(-6:ℝ)⁻¹ • voteV P K R c 3
def tide4 (P: Patch)(K:KernelChoices)(R:PathData G)(c:Clip): Script (Script.Tile G P.L) 4:=(-24:ℝ)⁻¹ • voteV P K R c 4
-- stitch for library_symm; craft D'. sign positive Haar. Halo scaled by 4 to represent 4*.
def tide2 (P:Patch)(K:KernelChoices)(R:PathData G)(c:Clip)(O: ChartRatio G)(b:ℝ): Script (Script.Tile G P.L) 2:= stitch ((2:ℝ)⁻¹ • (((-b) • voteV P K R c 2+ (-1:ℝ) • collarY P R)+ collarH P O))
include t S A U h G
omit t U h in
lemma tide_feed (b:ℝ)(O:ChartRatio G):
    folk (tide2 S.patch S.kernel A.live A.clip O b)∧ folk (tide3 S.patch S.kernel A.live A.clip)∧ folk (tide4 S.patch S.kernel A.live A.clip):=by
       have ht(n): folk (voteV S.patch S.kernel A.live A.clip n):=folkS (penne_unit _ _ _ _ A.pays _) _; exact ⟨folkst _ (folkS (folkF (folkF (folkS (ht 2) _) (folkS (Boxes.folk_collar _ A.pays) _)) (Boxes.folk_cap S.patch O)) _), folkS (ht 3) _, folkS (ht 4) _⟩
lemma tide_here (n:ℕ)(p:S!):library c (voteV S.patch S.kernel A.live A.clip n) (fun _:Fin n=>dance S he G p)=iteratedFDeriv ℝ n M! 0 (fun _:Fin n=> p):= vote_here S he h.1.cover t A.clip A.live A.pays n (fun _=>p)
include ht
lemma beam2 (p:S!)(b:ℝ): library c (tide2 S.patch S.kernel A.live A.clip P b) (fun _=>dance S he G p)=4*jet (HaloC S he t b A P) 2 p:=by
       let T:=dance S he G; let v:=T p; have hp:=tide_here S he U t h 2 p; have hf(i):folk (voteV S.patch S.kernel A.live A.clip i):=folkS (penne_unit _ _ _ _ A.pays _) _
       obtain ⟨hs,hx⟩:= marchY S he (R:=A.live) ht A.pays p; unfold tide2; let W: Fin 2→ vertP S.ratio he G:=![p,p]; let V:= collarY S.patch A.live
       rw [show library c (stitch _) (fun _=>_)= _ from (regaled _ (folk_whole (folkS (folkF (folkF (folkS (hf 2) (-b)) (folkS (Boxes.folk_collar S.patch A.pays) (-1:ℝ))) (Boxes.folk_cap S.patch P)) ((2:ℝ)⁻¹))) v)]; unfold narrate
       have hu := folkS (hf 2) (-b); have he':=folkS (Boxes.folk_collar S.patch A.pays) (-1:ℝ); erw [libScale,libAdd _ _ (folk_whole (folkF hu he')) (folk_whole (Boxes.folk_cap S.patch P)), libAdd _ _ (folk_whole hu) (folk_whole he')]; erw [libScale (voteV S.patch S.kernel A.live A.clip 2),libScale V, hp]; simp_rw [show (fun _ :Fin 2=>v)=![dance S he G p,dance S he G p] from funext fun i=>by fin_cases i<;>rfl]; erw [hs,hx, show jet (HaloC S he t b A P) 2 p= _ from (bandC S he t ht b (viewer t h.2.1).origin p).2,njet,njet,njet,show (fun _ : Fin 2=>p)=![p,p] from funext fun i=>by fin_cases i<;>rfl];ring
omit ht
lemma beam3 (p:S!): library c (tide3 S.patch S.kernel A.live A.clip) (fun _=>dance S he G p)= -jet M! 3 p:=by rw [tide3,libScale _ (fun _:Fin 3=>_),tide_here S he U t h 3 p]; unfold jet;norm_num [Nat.factorial]
lemma beam4 (p:S!): library c (tide4 S.patch S.kernel A.live A.clip) (fun _=>dance S he G p)= -jet M! 4 p:=by rw [tide4,libScale _ (fun _:Fin 4=>_),tide_here S he U t h 4 p]; unfold jet;norm_num [Nat.factorial]
end YM.OPE.Cascade.Rill
