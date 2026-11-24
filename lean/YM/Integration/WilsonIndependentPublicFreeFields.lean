import YM.Integration.WilsonIndependentPublicSpringKernel

/-! Finite held link means and Gaussian lines at every true signed block incidence. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonIndependentPublicFreeFields
open Lattice RG WilsonCoeffUV FreeResolvent RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open Laurent Bloch Exterior Stationary Work.F08 Matrix Metric Precision Next.Free Tree
open WilsonIndependentPublicFreeTrain (Matches)
variable {G:Gauge}{K:KernelChoices}{Ω:Type}{M:Ω→ℕ}{n:Page M→Side}

private theorem emitted (A:Levels G)(N m:ℕ)(hm:m<N)(P:Patch)(K:KernelChoices)
    (patch:P=loose A m)(kernel:K=A.clock.kernel)(B:Precision.Bed){σ α δ:ℝ}{clip:Clip}
    (bank:Hall B σ α δ clip)(Z:P.Branches K G)(pred:PoleRows P)
    (keys:HEq pred (predictionA A N m)){η σ':ℝ}(price:pred.strip σ' η)(clear:0≤σ')(pos:0≤η)
    (c:Side)(kin:Precision.K (B.metric.acts (c*P.L))=Precision.K ((freeForms A N (m+1)).acts (c*P.L))) :
    let S:=avenue P K c
    let split:=unitSplit G S 1
    HEq ((conditional A N m).acts c)
      (repackM split split (ledgerRow (blockQ G P.L) (blockQ G P.L) (hearth P K G B bank Z) c)) ∧
    HEq ((feedA A N m).acts c)
      (repackM split (Equiv.refl _) (ledgerRow (blockQ G P.L) (linksQ G) (projectionQ P K pred G) c)) :=by
  subst P K
  have row : pred=predictionA A N m:=eq_of_heq keys
  subst pred
  intro S split
  obtain ⟨unit,_,wick⟩:=cond_laws A m N
  constructor
  · apply heq_of_eq
    rw [WilsonIndependentPublicSpringKernel.heat _ _ _ _ bank Z c _ kin (unit c _ rfl)]
    exact wick c _ rfl
  · apply heq_of_eq
    rw [projRates _ _ _ G c price clear pos,←show repeatF S=stemF (loose A m) c from WilsonIndependentPublicSpringKernel.forest S]
    exact feed_period A N m hm c _ rfl

variable {A:Levels G}{C:Circuit M n}{K:KernelChoices}{s:ℕ}{w:Ω}
def Reads (A:Levels G)(C:Circuit M n)(K:KernelChoices)(s:ℕ)(w:Ω)(Y:Program K)(Z:∀ p:Patch,p.Branches K G)
    (f:Flap M)(c:Side):Prop :=
    let m:=s+(M w-(f.offset+1))
    let N:=s+M w
    let P:=C.pactP f
    let split:=unitSplit G (avenue P K c) 1
    HEq ((conditional A N m).acts c)
      (repackM split split (ledgerRow (blockQ G P.L) (blockQ G P.L) (C.pulses Y G Z f) c)) ∧
    HEq ((feedA A N m).acts c)
      (repackM split (Equiv.refl _) (ledgerRow (blockQ G P.L) (linksQ G) (C.sails Y G f) c))

theorem original (R:Matches A C K s w)(Y:Program K)(Z:∀ p:Patch,p.Branches K G)
    (f:Flap M)(hf:f.volW=w)(c:Side) : Reads A C K s w Y Z f c :=by
  unfold Reads
  intro m N P split
  have fit:f.offset<M w:=hf ▸ f.ok
  have step:m+1=s+(M w-f.offset):=by dsimp [m];omega
  have fare:=C.predicted Y f
  apply emitted A N m (by dsimp [m,N];omega) P K (R.patches f hf).symm R.kinetic.symm _
    (C.honored Y f.prev).card (Z _) (C.tells Y f) (WilsonIndependentPublicFreeTrain.predictor R Y f hf).symm
    fare.rows (C.honored Y f.prev).card.pos.le fare.costV
  rw [step]
  exact WilsonIndependentPublicFreeTrain.action R Y f.prev hf _

end YM.Integration.WilsonIndependentPublicFreeFields
