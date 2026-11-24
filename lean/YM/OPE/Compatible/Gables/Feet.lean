import YM.OPE.Compatible.Gables.Pay
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
include X
def weep (G:Gauge): Keys G (Limb H)≃ₗ[ℝ] Keys G (Limb H):= by
     let A: Keys G (Limb H)→ₗ[ℝ] Keys G (Limb H):= (X.dtex G).toLinearMap; have hp:Injective A:= X.dtexInj; exact LinearEquiv.ofBijective A ⟨hp,LinearMap.surjective_of_injective hp⟩
def Vale (G:Gauge): Keys G (Limb H)≃ₗ[ℝ](Keys G X.Free× Keys G X.Stable):=(weep H X G).symm.trans (compass H X G).symm
lemma prism (hG:G.Simple)(hp:4≤ d)(x:TK): (Terp.boost H D.gear hp K.K).P x x = (united (penon (V.L X)) (fond H X G)).P ((Vale H X G) x) ((Vale H X G) x):=by
      obtain ⟨B⟩:= Lit.buy H D hp hG b; let W:=compass H X G; let v:= Vale H X G x; let A':=X.skews G; let y:=W v;let M:=boost H D.gear hp K.K (G:=G); let P:=ballow X B hp; let Q:= united (penon (V.L X)) (fond H X G);
      have hz:(X.dtex G) y=x:=by change (weep H X G) (W (W.symm ((weep H X G).symm x)))=x; simp
      have hv: (penon P).P y y= Q.P v v:= jointW X B V v hp; have hh: jet P.f 2 y=M.P x x/2:=by
          unfold jet; change _* iteratedFDeriv ℝ 2 (B.s.f∘A'.gradient) 0 _=_; rw [slopeJet A'.gradient A'.gradC A'.grad0 _ B.s.F]; change jet B.s.f 2 (X.dtex G y)= _; rw [hz]
          conv_lhs=> unfold jet; rw [(B.uplift.iteratedFDeriv ℝ _).eq_of_nhds]
          exact Lit.lip H D x hp
      rw [penon_shape,hv] at hh;change M.P x x= Q.P v v; linarith only [hh]
def aimQ (G:Gauge):Keys G (Limb H)→ₗ[ℝ] Keys G X.Free:= (LinearMap.fst ..).comp (Vale H X G).toLinearMap
lemma repeatQ (hG:G.Simple)(hp:4≤ d)(x: P!→ℝ)(h: Bond x):
   (penon (V.L X)).average H! x=(boost H D.gear hp K.K).average (Chart.tangent G (Limb H)) (x ∘ aimQ H X G):=by
     let ν:= Measure.prod H! Zμ; let τμ:= Chart.tangent G (Limb H); let U:=penon (V.L X); let Q:= united U (fond H X G); let A':=Vale H X G; let L: P! × ZK→ₗ[ℝ] P!:= LinearMap.fst ..; have hh:Bond (x ∘ L):= h.compLinear L; haveI: ν.IsAddHaarMeasure:= Pilot.twoHaar (E:=P!) (F:=ZK) H! Zμ -- instance
     calc
          _= Q.average ν (x ∘ L):=( (harvested H! Zμ _ _ (x ∘ L) hh).trans (congr_arg _ (show (fun i:P!=> (fond H X G).average Zμ (fun j:ZK=> (x ∘ L) (i,j))) = x from funext fun k=>singleConst Zμ (fond H X G) (x k))) ).symm
          _=_:=by
              let z:=L; let g:= boost H D.gear hp K.K (G:=G); let p:ScriptJ (P!×ZK):=ScriptJ.low (x ∘ L); have hv := ease p (ScriptJ.lower hh) A'.symm Q g (fun i=> (by rw [prism H X V hG hp,A'.apply_symm_apply])) ν τμ; exact congr_arg JetS.s hv
end YM.OPE.Cascade.Rill
