import YM.OPE.Compatible.Lark.Graze
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
section math
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][Fintype I]
lemma carrySum (P:R2 E)(b:Module.Basis I ℝ F)(L:F→L[ℝ] E)(x y:F):
    (cash b x) ⬝ᵥ ((Matrix.of fun i j=> P ![L (b i),L (b j)])*ᵥ cash b y)=P ![L x,L y]:=by
      let Q:= (Coin.with2 P).compl₁₂ L.toLinearMap L.toLinearMap; have hh: Matrix.of (fun i j=> P ![L (b i),L (b j)])=LinearMap.toMatrix₂ b b Q:= Matrix.ext fun i j=> (LinearMap.toMatrix₂_apply b b Q i j).symm
      rw [hh]; have hp:= dotProduct_toMatrix₂_mulVec b b Q (cash b x) (cash b y); unfold cash at hp; rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply] at hp; exact hp
end math
lemma touchy (p:S!)(x y: Z!):
    let A':= pane X! t A.clip A.live
    let T:= countingBasis X! G
    cash T x ⬝ᵥ (HATCH A' T p*ᵥ cash T y)=iteratedFDeriv ℝ 3 A' 0 ![p,(0,x),(0,y)]:=by
      intro A T; exact carrySum (carg (iteratedFDeriv ℝ 3 A 0) p) T (ContinuousLinearMap.inr ℝ _ _) x y
lemma touch4 (p:S!)(x y: Z!):
    let A':= pane X! t A.clip A.live
    let T:= countingBasis X! G
    cash T x ⬝ᵥ (ROACH A' T p p*ᵥ cash T y)=iteratedFDeriv ℝ 4 A' 0 ![p,p,(0,x),(0,y)]:=by
      intro A T; exact carrySum (carg (bang (iteratedFDeriv ℝ 4 A 0) p) p) T (ContinuousLinearMap.inr ℝ _ _) x y
lemma ripe (m:Funds Q!)(x:J!):Flock.ripple (witV S he H G) m x = cash (countingBasis X! G) (EchoV S he H G x) ⬝ᵥ (m*ᵥ cash (countingBasis X! G) (EchoV S he H G x)):=by
    let T:= countingBasis X! G; let P:=cash T (EchoV S he H G x); unfold Flock.ripple; simp only [Finset.sum_apply,Pi.mul_apply, Pi.smul_apply,smul_eq_mul]; unfold dotProduct; refine Finset.sum_congr rfl fun i _=>?_ ; change _ = P i*(∑ j: Q!,m i j *P j); rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _=>by change m i j *(P i*P j)= _; ring
lemma massiveH (p:S!): τ2 (πV S he t A 3) p (InV S he H G)=Flock.ripple (witV S he H G) ((8:ℝ)⁻¹ • HATCH (pane X! t A.clip A.live) (countingBasis X! G) p):=by
     funext i; let M:= pane X! t A.clip A.live; let T:= countingBasis X! G; let q:=EchoV S he H G i; rw [ripe, Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]; change ((4:ℝ)⁻¹*(iteratedFDeriv ℝ 3 M 0) ![p,(0,q),(0,q)])/2=(8:ℝ)⁻¹ *(cash T q ⬝ᵥ (HATCH M T p *ᵥ cash T q)); rw [touchy]; unfold M;ring
lemma massiveR (p:S!): τ21 (πV S he t A 4) p (InV S he H G)=Flock.ripple (witV S he H G) ((16:ℝ)⁻¹ • ROACH (pane X! t A.clip A.live) (countingBasis X! G) p p):=by
     funext i; let M:= pane X! t A.clip A.live; let T:= countingBasis X! G; let q:=EchoV S he H G i; rw [ripe, Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]; change ((4:ℝ)⁻¹*(iteratedFDeriv ℝ 4 M 0) ![p,p,(0,q),(0,q)])/4=(16:ℝ)⁻¹ *(cash T q ⬝ᵥ (ROACH M T p p *ᵥ cash T q)); rw [touch4]; unfold M;ring
include S he G U A L g t h H
lemma hatComm (q:Kv)(x:S!)(hp:DoubleX S he H q x=x):
    HATCH (pane X! t A.clip A.live) (countingBasis X! G) x * leanI S he H G q=leanI S he H G q * HATCH (pane X! t A.clip A.live) (countingBasis X! G) x:=by
       let D:=leanI S he H G q; let M:=pane X! t A.clip A.live; let T:= countingBasis X! G; let Y:= HATCH M T x; let F:=twirlF S he H q (G:=G); let Q:= DoubleX S he H q (G:=G); have hb(i:Z!) : ((0:Bid.Dir G c),F i)=Q (0,i):=Prod.ext (map_zero (AnalyticNext.QuarticMatch.Joint.shifts (G:=G) (axisK q) (offset q c))).symm rfl
       have hf:Dᵀ*Y*D=Y:= damage_eq T fun i j=>by
            rw [both_cost]; unfold D; unfold leanI; rw [bill_at,bill_at, touchy,touchy, hb, hb]; nth_rw 1 [←hp]; exact bills_y S he H _ h.1.cover t _ _ _ (viewer t h.2.1).origin
       symm; change D*Y=Y*D; rw [show Dᵀ=D from leanEq ..] at hf; exact (show D*Y=D*Y*(D*D) from by rw [show D*D=1 from leanUnit ..,mul_one]).trans (by rw [← Matrix.mul_assoc,hf])
lemma sluice (x:S!)(hp:∀ k:Kv,DoubleX S he H k x=x):
    let Q:= HATCH (pane X! t A.clip A.live) (countingBasis X! G) x
    let E:= (FUND S he U)⁻¹
    let D:= SUMp S he H G
    Q*(D*E)*Q*(D*E)=(4:ℝ)•(D*(Q*E*Q*E)):=by
       intro Q E D; have he₁:D*Q=Q*D:=by unfold D SUMp; rw [Finset.mul_sum,Finset.sum_mul]; exact Finset.sum_congr rfl fun i _=>(hatComm S he H U t h _ x (hp i)).symm
       have he₂:E*D=D*E:=by unfold D SUMp;rw [Finset.mul_sum,Finset.sum_mul]; exact Finset.sum_congr rfl fun i _=>(leanKi S he H U t h _).symm
       have hV: Q*E*D=D*(Q*E):=by rw [Matrix.mul_assoc,he₂,← Matrix.mul_assoc,← he₁,Matrix.mul_assoc]
       calc
            _ = D*(Q*E)*(D*(Q*E)):=by rw [← Matrix.mul_assoc Q D E,← he₁]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc D Q E, he₁,Matrix.mul_assoc]
            _ = (D*D)*(Q*E*Q*E):=by rw [← Matrix.mul_assoc (D*(Q*E)),show D*(Q*E)*D= D*D*(Q*E) from ?_]; simp [Matrix.mul_assoc]; rw [Matrix.mul_assoc D (Q*E), hV]; exact (Matrix.mul_assoc ..).symm
            _ =_:=by rw [show D * D= _ from sumH ..,Matrix.smul_mul] -- matrix name
end YM.OPE.Cascade.Rill
