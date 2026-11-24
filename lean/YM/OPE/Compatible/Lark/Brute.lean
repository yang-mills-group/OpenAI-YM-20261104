import YM.OPE.Compatible.Lark.Shale
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
open Page
local notation "K!"=> countingBasis X! G
def HingeT (G:Gauge)(i: Active G X!): Site c:= (squad S.ratio he G i).1
abbrev ZoneP (m:ℕ)(A:Matrix Q! Q! ℝ)(D:ℝ):= PaidT (HingeT S he G) (HingeT S he G) m A D
variable {j k:ℕ}{B V':ℝ}
include he S G U L h A t g
lemma Pyramid (x:Bid.Dir G c)(hh: soot k (voteV S.patch S.kernel A.live A.clip 4) B)(hs:soot k (U.Fly A.live A.clip) V'):
    let H:= fieldT (cabin g) x
    let Q:= fieldU (cabin g) x x
    let P:=pane X! t A.clip A.live
    let a:= (c.val:ℝ)
    let b:= (3:ℝ)^k * ‖dance S he G H‖^2
    ZoneP S he k (ROACH P K! H H) (a^4*b*B) ∧ ZoneP S he k (HATCH P K! Q) (a^4*b*V'):=by
       intro H Q P a b; let X:=dance S he G; let T(i:Q!):= starJ (I:=Shade G) (squad S.ratio he G i); let u x:=(X ((0:Bid.Dir G c),K! x)); let A':=voteV S.patch S.kernel A.live A.clip 4; let D:= U.Fly A.live A.clip; have h0:0≤ b:=by unfold b; positivity
       have hp:= dawn S he U t h A.pays; have hA:Summable (voteV S.patch S.kernel A.live A.clip 3):=folk_whole (folkS (penne_unit _ _ _ _ A.pays 3) _)
       have ht(i:Q!): u i=deltaH (T i):=hp.token _
       have hz (y:Script (Flume.Script.Tile G S.patch.L) 4)(i j:Q!)(V:ℝ)(hk:soot k y V):Dux k ((T i).1) ((T j).1)*‖library c y ![u i,u j,X H,X H]‖ ≤ a^4*b*V:=by
            rw [ht,ht]; refine (lib_pay y (T i) (T j) ![X H,X H] hk).trans_eq ?_; rw [Fin.prod_univ_two]; unfold b; change (c.val:ℝ)^4*((3:ℝ)^k*V* (‖X H‖*‖X H‖)) = _; unfold a X;ring
       have hp3:= vote_here S he h.1.cover t A.clip A.live A.pays 4; constructor
       · have he' := (tsum_nonneg hh.1).trans hh.2.2; refine ⟨by positivity,fun i j=>?_⟩; change Dux k (T i).1 (T j).1* ‖iteratedFDeriv ℝ 4 P 0 _‖≤ _; let x₀:=((0:Bid.Dir G c),K! i); let x₁:= ((0:Bid.Dir G c),K! j); let p:= (Equiv.swap (0:Fin 4) 2).trans (Equiv.swap 1 3); let v:=![x₀,x₁,H,H]; rw [show iteratedFDeriv ℝ 4 P 0 _= _ from (show iteratedFDeriv ℝ 4 P 0 ![H,H,x₀,x₁]=iteratedFDeriv ℝ 4 P 0 v from (by rw [show ![H,H,x₀,x₁]=v∘p from funext fun i=>by fin_cases i<;>rfl]; exact Analysis.sym_Jet (hp.h.origin.of_le le_top) ..)), ← hp3]; erw [show dance S he G∘ v=![u i,u j,X H,X H] from funext fun i=>by fin_cases i<;>rfl]; exact hz A' i j B hh
       have he' := (tsum_nonneg hs.1).trans hs.2.2; refine ⟨by positivity, fun i j=>?_⟩; change Dux k (T i).1 (T j).1* ‖iteratedFDeriv ℝ 3 P 0 _‖≤ _; rw [← hp.cots x ((0:Bid.Dir G c),K! i) ((0:Bid.Dir G c),K! j) U.rocket1 hA, norm_neg]; exact hz D i j _ hs
lemma pyre (x:Bid.Dir G c)(hh: soot k (voteV S.patch S.kernel A.live A.clip 3) B):
    let H:=fieldT (cabin g) x
    let P:=pane X! t A.clip A.live
    ZoneP S he k (HATCH P K! H) ((c.val:ℝ)^4* (3:ℝ)^k * ‖dance S he G H‖ *B):=by
       intro H P; let T(i:Q!):= starJ (I:=Shade G) (squad S.ratio he G i); let A':=voteV S.patch S.kernel A.live A.clip 3; let X:= dance S he G; have h₁:0 ≤ B:=(tsum_nonneg hh.1).trans hh.2.2; have hp:= dawn S he U t h A.pays
       refine ⟨by positivity,fun i j=>?_⟩; let u:=((0:Bid.Dir G c),K! i); let v:=((0:Bid.Dir G c),K! j); change Dux _ (T i).1 (T j).1* ‖iteratedFDeriv ℝ 3 P 0 ![H,u,v]‖ ≤ _; let p:=(Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 0 1); have he': iteratedFDeriv ℝ 3 P 0 ![H,u,v]= library c A' ![deltaH (T i),deltaH (T j),X H]:=by
             rw [show ![H,u,v]=![u,v,H]∘ p from ?_, show iteratedFDeriv ℝ 3 P 0 _= _ from (show iteratedFDeriv ℝ 3 P 0 (![u,v,H]∘ p)=_ from Analysis.sym_Jet (hp.h.origin.of_le le_top) ..),← hp.mark]; apply congr_arg; ext1 a; fin_cases a<;>first|rfl | exact hp.token i | exact hp.token j
             funext i;fin_cases i<;>rfl
       rw [he']; exact (lib_pay A' (T i) (T j) ![X H] hh).trans_eq (by simp only [Fin.prod_univ_one]; change _*((3:ℝ)^k * B*‖dance S he G H‖)=_; ring)
lemma payD (s:ℝ)(ha:U.dot.strip s B)(hp:0≤B)(hK:0<s)(k:ℕ): ZoneP S he k ((FUND S he U)⁻¹) (Planned.PrimaryIntegral295.Carrier.widthCost s k*B):= ⟨mul_nonneg (zero_le_one.trans (Planned.PrimaryIntegral295.Carrier.widthCost_ge hK k)) hp,fun i j=> by rw [← (dawn S he U t h A.pays).tariff]; exact pay_field U.dot ha hK ..⟩
end YM.OPE.Cascade.Rill
