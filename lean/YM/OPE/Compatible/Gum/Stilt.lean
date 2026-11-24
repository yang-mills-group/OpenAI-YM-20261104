import YM.OPE.Compatible.Cum.Unfit
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
abbrev actLight (G:Gauge):Keys G Qµ→L[ℝ] deck (Flume.Script.Tile G S.ratio.count) c:= dance S he G∘L InV S he H G
abbrev pileV (G:Gauge)(p: Active G X!): Flume.Script.Tab (Flume.Script.Tile G S.ratio.count) c:= starJ (squad S.ratio he G p)
def Piax (G:Gauge)(B:Boxes G S.patch S.kernel) := ROOT (I:=Shade G) B.dot -- G shadow K
lemma pile_or (p:Flume.Script.Tab T! c): (∃ q:Flume.Script.Tab (Shade G) c,p=starI q) ∨ ∃ q:Q!,p=pileV S he G q:=by
     rcases p with ⟨a,i|i⟩; exact Or.inl ⟨(a,i),rfl⟩
     obtain ⟨q,hq⟩:= (squad S.ratio he G).surjective (a,i); exact Or.inr ⟨q,congr_arg (starJ (I:= Shade G)) hq.symm⟩
lemma pileF (p: Q!): Ferry (actLight S he H G) (pileV S he G p)=witV S he H G p:=LinearMap.ext fun i=> (petalV S.ratio he (InV S he H G i) p)
lemma abstains (p:Flume.Script.Tab (Shade G) c): Ferry (actLight S he H G) (starI p)=0:=LinearMap.ext fun i=>by change (spool G c) 0 p=0; simp
lemma leanAt (i j:Q!)(k:Kv)(M:Funds (Active G X!)): ‖(leanI S he H G k*M) i j‖=‖M (Varp S he H G k i) j‖:=by
      rw [show (leanI S he H G k*M) i j=(leanI S he H G k *ᵥ fun a:Q!=> M a j) i from Matrix.mul_apply .., leanK];split; exact norm_neg _; rfl
include S he U L h A t g
lemma planeR (i j:Q!): (Piax S G U).acts c (pileV S he G i) (pileV S he G j)=(FUND S he U)⁻¹ i j:=by unfold Piax pileV; erw [ROOT_right]; exact (dawn S he U t h A.pays).tariff i j
include H C hc
lemma camIs (i j: Q!): Oriel C (actLight S he H G) (pileV S he G i) (pileV S he G j)=(SUMp S he H G*(FUND S he U)⁻¹) i j:=by
    simp only [Oriel,mount,Matrix.of_apply];simp_rw [pileF];exact congr_fun (congr_fun (tradedCov S he H U t h hc) i) j
omit A t g h U L hc in
lemma cam_nil (i: Flume.Script.Tab (Shade G) c)(j:Flume.Script.Tab T! c): Oriel C (actLight S he H G) (starI i) j=0∧Oriel C (actLight S he H G) j (starI i)=0:=by
     simp only [Oriel,mount,Matrix.of_apply]; simp_rw [abstains];simp [Law.wick]
end YM.OPE.Cascade.Rill
