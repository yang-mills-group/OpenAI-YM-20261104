import YM.OPE.Compatible.Wells.Pal
/-!
# Marginal plans. True relative density jets, *before* normalization
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U: Scaffold φ (Counters β) n (Mnd i S A) r)
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock Stranded
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open ScriptJ
local notation "TC"=> Merchant.Chamber G r
local notation "X!"=>cEye A U D x
open Variance
local notation "m!"=> (ΓWeight (G:=G) (Punched A U _) (cEye A U D x _) (KPole A _) (LPole A _))
include hN
omit hN in private lemma combine (a b:ℝ):a+b=-(-a-b):=by ring
omit hN in private lemma wheelAgrees {E:Type}(i:E)(L:ScriptJ E)(f:Token)
    (low:(L i).l = -f.l)(high:(L i).h = -f.h):
    wheel L i = flareTok f.l f.h:=by
  dsimp only [wheel]
  rw [low,high,neg_neg,neg_neg]
  exact JetS.eta _ _ rfl rfl (by change f.h+(-f.l)^2/2 = f.h+f.l^2/2; ring)

omit hN in private lemma bookWheel {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
    (f g:E→ℝ)(v:E):wheel (BookW f g) v = flareTok (-jet f 3 v-jet g 1 v) (-jet f 4 v-jet g 2 v):=by
  let fees:Token:=⟨0,-jet f 3 v-jet g 1 v,-jet f 4 v-jet g 2 v⟩
  exact wheelAgrees v (BookW f g) fees (combine _ _) (combine _ _)

omit hN in private lemma wheelCompose {E Z:Type}(b:ScriptJ E)(u:Z→E)(x:Z):wheel (b∘u) x=wheel b (u x):=rfl

omit hN in private lemma chartWheel {n:Side}(hp:Board n (r+1))(u:Bid.Dir G n)(f g:Bid.Dir G n→ℝ)(y:Merchant.Chamber G r):
    let v:=turn (sailT G hp) u y
    wheel (ΓLog hp u f g) y=flareTok (-jet f 3 v-jet g 1 v) (-jet f 4 v-jet g 2 v):=by
  intro v
  exact (wheelCompose (BookW f g) (turn (sailT G hp) u) y).trans (bookWheel f g v)

omit hN in lemma Γwheel (j:I)(y:Merchant.Chamber G r): wheel (ΓLog (Punched A U j) (cEye A U D x j) (KPole A j) (LPole A j)) y= let p:= PolV A j (liftedM A U D x j y); flareTok p.l p.h:=by
  dsimp only [liftedM,Yfar,Stair,PolV]
  with_reducible_and_instances exact chartWheel (Punched A U j) (cEye A U D x j) (KPole A j) (LPole A j) y

omit hN in private lemma plainInv {t:ℝ}(ht:0<t): JetS.plainJ t⁻¹ * JetS.plainJ t=1:=by
  apply JetS.eta <;> first | exact inv_mul_cancel₀ ht.ne' | (simp only [JetS.ml_l,JetS.ml_h,JetS.plain_l,JetS.plain_h,zero_mul,mul_zero,add_zero];rfl)

omit hN in private lemma phaseProduct (f p:Token)(s t:ℝ)(ht:0<t):
    flareTok (f.l-p.l) (f.h-p.h+s) =
      (flareTok (-p.l) (-p.h)*JetS.plainJ t⁻¹*(JetS.plainJ t*flareTok 0 s))*flareTok f.l f.h:=by
  rw [mul_assoc (flareTok (-p.l) (-p.h)),←mul_assoc (JetS.plainJ t⁻¹),plainInv ht,one_mul]
  rw [blazeTok,blazeTok]
  congr 1 <;> ring

omit hN in private noncomputable def phaseToken (j:I):Token:=
  let u:=cEye A U D x j
  let t:=Chart.jacobian N (U:=↥(fieldP r)) 0
  let p:=PolV A j u
  flareTok (-p.l) (-p.h)*JetS.plainJ t⁻¹

omit hN in private lemma originalReading (j:I)(y:Merchant.Chamber G r):
    let f:=PolV A j (liftedM A U D x j y)
    let u:=cEye A U D x j
    let p:=PolV A j u
    Tact A U D x N j y = flareTok (f.l-p.l) (f.h-p.h+jet (feeX N) 2 (y+PinT G u)):=rfl

omit hN in private lemma attachPhase (f p:Token)(s t:ℝ)(j w:Token)(tp:0<t)
    (jac:j=JetS.plainJ t*flareTok 0 s)(used:w=flareTok f.l f.h):
    flareTok (f.l-p.l) (f.h-p.h+s) = (flareTok (-p.l) (-p.h)*JetS.plainJ t⁻¹*j)*w:=by
  rw [jac,used]
  exact phaseProduct f p s t tp

omit hN in private lemma paidJac {n:Side}(u:Bid.Dir G n)(y:Merchant.Chamber G r)
    (P:ChartRatio G)(hr:LocalRatio P):
    let t:=Chart.jacobian P (U:=↥(fieldP r)) 0
    0<t ∧ ΓJac P u y = JetS.plainJ t * flareTok 0 (jet (feeX P) 2 (y+PinT G u)):=by
  intro t
  let τ:=R_τ (r:=r) u y
  have he:τ=y+PinT G u:=add_comm (PinT (r:=r) G u) y
  have j:=jacRank hr τ
  exact ⟨j.1,j.2.trans (congrArg (fun b=>JetS.plainJ t*flareTok 0 (jet (feeX P) 2 b)) he)⟩

private lemma phaseReading (j:I)(y:Merchant.Chamber G r):
    Tact A U D x N j y =
      ΓWeight (Punched A U j) (cEye A U D x j) (KPole A j) (LPole A j) N (phaseToken A U D (N:=N) x j) y:=by
  let u:=cEye A U D x j
  let t:=Chart.jacobian N (U:=↥(fieldP r)) 0
  let f:=PolV A j (liftedM A U D x j y)
  let p:=PolV A j u
  let s:=jet (feeX N) 2 (y+PinT G u)
  let w:=wheel (ΓLog (Punched A U j) u (KPole A j) (LPole A j)) y
  have jac:=paidJac u y N hN
  have bill:=attachPhase f p s t (ΓJac N u y) w jac.1 jac.2 (Γwheel A U D x j y)
  exact (originalReading A U D (N:=N) x j y).trans bill

lemma ΓPhase (j:I):∃ z:Token,Tact A U D x N j=ΓWeight (Punched A U j) (cEye A U D x j) (KPole A j) (LPole A j) N z:=by
  exact ⟨phaseToken A U D (N:=N) x j,funext (phaseReading A U D hN x j)⟩

variable (j:I)
lemma Kgrade : ScriptJ.B (Tact A U D x N j):=by obtain ⟨z,h⟩:= ΓPhase A U D hN x j; rw [h]; exact WeightB (Punched A U j) _ _ _ z
end YM.OPE.Owl.HillZ
