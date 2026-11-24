import YM.OPE.Compatible.Lark.Worm
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
local notation "M!"=>pane X! t A.clip A.live
local notation "U!"=> FUND S he U
local notation "K!"=> countingBasis X! G
def skipH (G:Gauge):= SUMp S he H G-1
-- full H cover heat = zero-seam full + sign sums.
include S he H G K U h L t g A C hc
lemma coilTrace (hs:G.Simple)(i: Keys G (Limb H))(v:S!):
    let p:=fieldT (cabin g) (cloak H i)
    let B':= τ21 (πV S he t A 4) p (InV S he H G)
    let Q:= τ2 (πV S he t A 3) p (InV S he H G)
    let D:=HATCH M! K! p
    let L:= ROACH M! K! p p
    let x:= U!⁻¹
    let y:= x * HATCH M! K! v+x* L-x*D*x*D
    C.average Wμ B' - C.average Wμ (Q^2)/2 + C.average Wμ (τ2 (πV S he t A 3) v (InV S he H G))/2 = heatPay M! K! x p p v/8+(skipH S he H G*y).trace/16:=by
         intro p B' Q D W x y; let u:=witV S he H G; let P:= mount C u; let A':=HATCH M! K! v; let V:= SUMp S he H G; have hh:P=V*x:= tradedCov S he H U t h hc
         have hx : D.transpose=D:=(dawn S he U t h A.pays).hatq p |> fun ht=>Matrix.ext fun i j=>ht i j -- var impl
         let Z:= (8:ℝ)⁻¹ • D; have ht: Z.transpose=Z:= by unfold Z;rw [Matrix.transpose_smul,hx]
         have hp: ∀ q:Kv,DoubleX S he H q p=p:=fun q=>knowV S he H U h t q i
         have ha : Q=Flock.ripple u Z:= massiveH S he H t p; have hv := τFlat S he H U t h hc hs i; change C.average Wμ Q=0 at hv
         have ha1 : C.average Wμ (Q^2)= (1/8:ℝ)* (V*(x*D*x*D)).trace :=by -- variance 2/64*4
              rw [ha] at *; rw [pow_two,swimmer Wμ C u Z Z ht,hv]; change 0*0+2*(Z*P*Z*P).trace=_; rw [hh]; unfold Z; simp only [Matrix.smul_mul,Matrix.mul_smul]; rw [sluice S he H U t h p hp]; simp only [Matrix.trace_smul,smul_eq_mul]
              have hz : (V*(x*D*x*D)).trace=(V*(D*x*D*x)).trace:=by
                   have he' :V * x=x*V:=by unfold V SUMp; rw [Finset.sum_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>leanKi S he H U t h i
                   calc
                     _= (x*(V*(D*x*D))).trace:=by congr 1; simp_rw [Matrix.mul_assoc];rw [← Matrix.mul_assoc V x, he',Matrix.mul_assoc]
                     _= (V*(D*x*D*x)).trace:= (Matrix.trace_mul_comm ..).trans (by rw [Matrix.mul_assoc V])
              rw [hz]; change 0*0+2*( (8:ℝ)⁻¹ * ((8:ℝ)⁻¹*(4* (V*(D*x*D*x)).trace)))=_;ring
         have h1 : C.average Wμ B'= (V*x*W).trace/16:=by
              rw [show B'=Flock.ripple u _ from massiveR S he H t p,paddle, show mount C u= _ from hh, Matrix.smul_mul,Matrix.trace_smul, smul_eq_mul,Matrix.trace_mul_comm]; ring
         have h2: C.average Wμ (τ2 (πV S he t A 3) v (InV S he H G))=(V*x*A').trace/8:=by rw [massiveH S he H t v,paddle, show mount C u= _ from hh,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,Matrix.trace_mul_comm]; ring -- inferred
         rw [h1,h2,ha1]; change _= heatPay M! K! x p p v /8+ ((V-1)*y).trace /16
         rw [Matrix.sub_mul,one_mul,trace_sub, show V*x*W=V*(x*W) from Matrix.mul_assoc .., show V*x*A'= V*(x*A') from Matrix.mul_assoc ..]; unfold y heatPay; change _= 1/2 * ((x*A').trace+(x*W).trace-(x*D*x*D).trace)/8+_; simp only [Matrix.mul_sub,Matrix.mul_add,Matrix.trace_sub,Matrix.trace_add]; unfold x A' W D V;ring
end YM.OPE.Cascade.Rill
