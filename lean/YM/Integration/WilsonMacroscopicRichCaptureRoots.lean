import YM.FullVolume.Cross
import YM.OPE.Therm.Law
import YM.Integration.WilsonMacroscopicForwardTransfer
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCaptureRoots
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox OPE OPE.Therm
open PhysicalNext.Repeat.Legato
open WilsonMacroscopicForwardTransfer (exterior weighted)
open private cancel from YM.Integration.WilsonMacroscopicForwardTransfer
open scoped Classical Topology BigOperators
variable {G:Gauge}

private theorem steps (H:History G)(N p:ℕ){u b k:ℕ}(ub:u≤b)(bk:b≤k)(X:Config G (H.S.side k p) → ℂ):
    pushTo H N p ub (pushTo H N p bk X)=pushTo H N p (ub.trans bk) X:=by
  induction k,bk using Nat.le_induction with
  | base=>simp only [pushTo_self]
  | succ k bk ih=>
    rw [pushTo_next H N p bk X,pushTo_next H N p (ub.trans bk) X];exact ih _

/-- The exact full rooted Wilson conditional can be passed through the coarser capture before the fixed physical reference, on the original positive denominators, pointwise including the identity links. -/
theorem through (R:Run G){N p u b k:ℕ}(ub:u≤b)(bk:b≤k)(kN:k≤N)(X:Config G (R.family.side k p) → ℂ):
    exterior (C:=R.family) (N:=N) ub (exterior (N:=N) bk X)=exterior (N:=N) (ub.trans bk) X:=by
  funext U
  let D:ℂ:=dose (H:=R.family.path) (p:=p) u U N
  let read Z:=pushTo R.family.path N p ub Z U/D
  have middle:weighted (N:=N) (exterior (C:=R.family) (N:=N) bk X)=pushTo R.family.path N p bk (weighted (N:=N) X):=cancel R.makes bk kN X
  have below:=congrArg read middle
  have start:=congrArg (fun Y:Config G (R.family.side u p)→ℂ=>Y U/D) (steps R.family.path N p ub bk (weighted (N:=N) X))
  exact below.trans start

def preimage (R:Run G){u b:ℕ}(ub:u≤b)(per:ℕ)(roots:Finset (Site (R.family.side u per))):Finset (Site (R.family.side b per)):=
  Finset.univ.filter fun x=>(R.family.S.toDepth ub per).parent x∈roots

/-- All genuine b-roots above an accepted u-root, with their held signed coefficients and a correlated fixed-reference test. This takes the entire finite sum inside the first conditional, before re-aggregating on the very same original positive path. -/
theorem tested (R:Run G){N p u b k:ℕ}(ub:u≤b)(bk:b≤k)(kN:k≤N)(roots:Finset (Site (R.family.side u p)))(w:Site (R.family.side b p) → ℂ)(Y:Site (R.family.side b p) → Config G (R.family.side k p) → ℂ)(stock:∀x,Envelope (Y x)){Z:Config G (R.family.side u p) → ℂ}(e:Envelope Z):
    let I:=preimage R ub p roots
    let X:=fun U=>∑x∈I,w x*Y x U
    (∫U,exterior (C:=R.family) (N:=N) ub (exterior (N:=N) bk X) U*Z U ∂scene R.family.path N p u)=
      ∑z∈roots,∑x∈Finset.univ.filter (fun x=>(R.family.S.toDepth ub p).parent x=z),w x*(∫U,Y x U*backTo R.family.path N p (ub.trans bk) Z U ∂scene R.family.path N p k):=by
  intro I X;let μ:=scene R.family.path N p k;letI:IsProbabilityMeasure μ:=probability R.makes.wilson kN
  let C:=backTo R.family.path N p (ub.trans bk) Z
  have env:Envelope C:=backTo_env R.family.path N p (ub.trans bk) e
  have one (x):Integrable (fun U=>w x*Y x U) μ:=((stock x).integrableC μ).const_mul _
  have mixed (x):Integrable (fun U=>w x*(Y x U*C U)) μ:=(((stock x).mulC env).integrableC μ).const_mul _
  have live:Integrable X μ:=integrable_finsetSum I (fun x _=>one x)
  rw [through R ub bk kN X]
  have read:(∫U,exterior (C:=R.family) (N:=N) (ub.trans bk) X U*Z U ∂scene R.family.path N p u)=∫U,X U*C U ∂μ:=WilsonMacroscopicForwardTransfer.joint R.makes (ub.trans bk) kN X live Z e
  let cost:=fun x=>w x*(∫U,Y x U*C U ∂μ)
  calc
    _=(∫U,X U*C U ∂μ):=read
    _=(∫U,∑x∈I,w x*(Y x U*C U) ∂μ):=by
      apply integral_congr_ae;apply ae_of_all;intro U;simp only [X,Finset.sum_mul,mul_assoc]
    _=∑x∈I,cost x:=by
      rw [integral_finsetSum I (fun x _=>mixed x)];simp only [integral_const_mul];rfl
    _=_:=(Finset.sum_fiberwise_eq_sum_filter Finset.univ roots (R.family.S.toDepth ub p).parent cost).symm

end YM.Integration.WilsonMacroscopicRichCaptureRoots

