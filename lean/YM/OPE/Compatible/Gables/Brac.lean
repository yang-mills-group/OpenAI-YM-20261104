import YM.OPE.Compatible.Gables.Runs
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
variable (t:S.Choices) (h:ReadyV S he U A D L g)
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
local notation "U!"=> FUND S he U
local notation "CAX" => actLight S he H G
open JetS ScriptJ Shell Char Libra.Shift
local notation "PL"=> Shift.crossT Wμ C
local notation "PY"=> (Y.L W!)
local notation "H!"=> Chart.tangent G X.Free
open Terp
local notation "TK"=>Keys G (Limb H)
local notation "ZK"=>Keys G X.Stable
local notation "Zμ"=>Chart.tangent G X.Stable
def fillBoot (G:Gauge): Keys G (Limb H)→L[ℝ] deck (Shade G) c:= (spool G c).toContinuousLinearMap ∘L cloak H
lemma caseBill (p: Keys G (Limb H))(i: Flume.Script.Tab (Shade G) c):Ferry (fillBoot H G) i p= flightPart H i.2.2 p (i.1,coord i.2.1):=rfl
lemma worldCap (K:KernelChoices)(D:ℕ)(hD:4≤D) : ∃ B:ℝ,0≤ B∧∀ v:Train D,∀ (c:Side)(H:Even c.val)(G:Gauge), Sustains (boost H v hD K) (fillBoot H G) B:=by
      obtain ⟨b,hb,L⟩:= terra_money K hD; refine ⟨4*b,by positivity,fun v c H G=>?_⟩
      refine ⟨by positivity,?_⟩; intro i; let p:= (i.1,i.2.1); let k:=i.2.2; have ht:Oriel _ (fillBoot H G) i i= boostJet H hD v K k k p p:=rfl; rw [ht, pages,if_pos rfl]; apply (norm_sum_le ..).trans; apply (Finset.sum_le_sum (g:=fun _=>b) (fun j _=>?_)).trans_eq; rw [Finset.sum_const,Finset.card_univ,kvCard,nsmul_eq_mul,Nat.cast_ofNat]; unfold Terp.letter; split; · rw [norm_neg]; exact L v c _ _
      exact L v c _ _
-- estimate ∥p∥ on raster via ∥spool∥
lemma balance0 (p:TK)(x:Limb H)(i:G.ColorIndex): (fillBoot H G p) (x.val.1,x.val.2,i)= p x i:=by change (cloak H p (x.val.1, coord x.val.2)) i=p x i; rw [cloak_at,Prod.mk.eta,Streamer.hover_reap]
lemma paidBoot (x:TK):‖x‖ ≤ Real.sqrt (Fintype.card G.ColorIndex) *‖fillBoot H G x‖:=by
     let p:= ‖fillBoot H G x‖; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; let a:= x i; let k:= Fintype.card G.ColorIndex
     apply le_of_sq_le_sq (show ‖a‖^2≤ (Real.sqrt (k:ℝ)*p)^2 from ?_) (by positivity)
     rw [← real_inner_self_eq_norm_sq,PiLp.inner_apply,mul_pow,Real.sq_sqrt (by positivity)]; apply (Finset.sum_le_sum (g:=fun _=>p^2) (fun j _=>?_)).trans_eq; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
     change inner ℝ (a j) (a j) ≤_; rw [real_inner_self_eq_norm_sq]; rw [show a j=(fillBoot H G x) (i.val.1,i.val.2,j) from (balance0 H x i j).symm]; gcongr; exact norm_le_pi_norm ..
def zoneR (p:P!→ℝ)(b:ℝ)(k:ℕ):Prop := BeamS p b (fun x=>1+‖x‖) k
-- requires budgets after n before marks
lemma pondPay (h:4 ≤ d) (hS:G.Simple)(p: P!→ℝ)(z:ℝ)(hz:0≤z)(s:ℕ)(hq:zoneR H X p z s)(b':ℝ)(hv:Sustains (boost H D.gear h K.K) (fillBoot H G) b'):
     ‖(penon (V.L X)).average H! p‖ ≤ (c.val:ℝ)^4 * quotaB (Shade G) b' s * (z*(1+(1+2*(c.val:ℝ)^4)*Real.sqrt (Fintype.card G.ColorIndex))^s):=by
           rw [repeatQ H X V hS h]; swap; · exact hq.1
           let u:=(1+2*(c.val:ℝ)^4)*Real.sqrt (Fintype.card G.ColorIndex); have hu:0 ≤ u:=by unfold u;positivity
           let x':deck (Shade G) c:=0; let F:= fillBoot H G; let U:= aimQ H X G; let K':=boost H D.gear h K.K (G:=G); let m:=Chart.tangent G (Limb H)
           have hp:BeamS (p ∘ U) (z*(1+u)^s) (clockY x' F) s:=by
                refine ⟨hq.1.compLinear U,fun i=>?_⟩; refine (hq.2 (U i)).trans ?_; change z*(1+‖U i‖)^s ≤ _; suffices hp :1+ ‖U i‖≤(1+u)*clockY x' F i by rw [mul_assoc, ←mul_pow]; gcongr
                unfold clockY x';rw [norm_zero,add_zero]; have ht: ‖U i‖ ≤ u*‖F i‖:= (boulev H X i).trans ((mul_le_mul_of_nonneg_left (paidBoot H i) (by positivity)).trans_eq (by unfold u F; ring)); linarith [norm_nonneg (F i)]
           simpa only [x',norm_zero,add_zero,one_pow,mul_one] using! Mile m K' (fillBoot H G) hv x' _ _ (by positivity) s hp
end YM.OPE.Cascade.Rill
