import YM.Integration.WilsonConditionalTaylorFieldReset
import YM.Integration.WilsonConditionalTaylorUnresetForest
import YM.Integration.WilsonConditionalTaylorCourseLedger
import YM.Integration.WilsonMutableVacuumWickCubature
import YM.Integration.WilsonMeasuredVacuumGerm

/-! A pre-reset physical field on the issued forest, compared with its
own varying earlier finite torus action on all angular fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorRawAttachment
open Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorBulkHistory WilsonConditionalTaylorFieldBalance WilsonConditionalTaylorSceneCalibration
open WilsonMovingPolynomialPull WilsonMovingNormalizedBank
open scoped Classical Matrix
variable {G : Gauge} (R : Run G) (u : G.ColorIndex)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

def stored {n : Side} (Z : Pap (wire G n)) := splitV (place (WilsonMovingGaussianCoordinates.link G n).symm Z)

variable {N per k cap : ℕ} {S : Scene R.family.path.levels per cap}
variable (scene : Realized R.alloy.B.kin N per k cap (Lis.sun G u) S) (j : ℕ) (lo : k≤j) (hi : j<N)

include scene lo hi in
private theorem paid (F : Forest (R.family.path.levels.clock.op j per).ratio)
    (t : (R.family.path.levels.clock.op j per).Choices) :
    (Push.Uniform.block (priced F t (R.family.path.levels.params (j+1)).clip (R.alloy.B.kin.path N (j+1))) 0).PosDef :=by
  let K:=RunFormalChain.fromRun R
  have fit:=(scene.budget (j+1) hi (lo.trans (Nat.le_succ j))).1
  exact blueprint F t (R.alloy.B.kin.path N (j+1)) (R.family.path.levels.params (j+1)).clip
    (R.family.path.levels.blocks j per).branches fit.quiet (K.post.price _) (K.planned.gap N j per hi F)

private theorem coordinates (F : Forest (R.family.path.levels.clock.op j per).ratio)
    (t : (R.family.path.levels.clock.op j per).Choices)
    (U : Pap (wire G (R.family.side (j+1) per))) (x : Positions (Primary (R.family.side j per) G)) :
    let K:=(RunFormalChain.fromRun R).step N j per hi
    let bank(v : Positions (Primary (R.family.side j per) G)):=WilsonRunVacuumWickCubature.bank K F t v U
    view x (colorCut F t (R.alloy.B.kin.path N (j+1)) (R.family.path.levels.params (j+1)).clip R.metals.O (stored U) (K.b F)) =
      covelog (bank x)-covelog (bank 0):=by
  intro K bank
  let D:=R.family.path.rep N per (j+1)
  let act (X : PathData G) (p : Clip):=view x (colorCut F t X p R.metals.O (stored U) (K.b F))
  have ep : D.path=R.alloy.B.kin.path N (j+1):=(RunFormalChain.fromRun R).selected N per (j+1) hi
  have cp : D.clip=(R.family.path.levels.params (j+1)).clip:=(RunFormalChain.fromRun R).clips N per (j+1) hi
  exact (congrArg₂ act ep.symm cp.symm).trans (WilsonMeasuredVacuumGerm.centered K F t U x)

theorem step (supply : Fields cap (S.Poly (j+1)) (stored (course R u wood tags N (j+1) (R.family.side (j+1) per)))) :
    Fields cap (untuned R scene j lo hi) (stored (raw R wood tags N j (course R u wood tags N (j+1)) (R.family.side j per))) :=by
  let V:=R.family.path.levels
  let n:=R.family.side j per
  let fine:=R.family.side (j+1) per
  let P:=destination V N j
  let U:=course R u wood tags N (j+1)
  let Z:=raw R wood tags N j U n
  let L:=place (WilsonMovingGaussianCoordinates.link G n).symm Z
  let T:=untuned R scene j lo hi
  let B:=stored (U fine)
  let H:=Reef.ferry P (V.blocks j 0).branches (wood j) n
  let K:=(RunFormalChain.fromRun R).step N j per hi
  have pre := (admitted R u wood tags N (j+1) hi (n*P.L)).1
  obtain ⟨F,t,_,_,finite⟩:=WilsonMutableVacuumWickCubature.filed R N j per hi (tags j n) wood U pre
  let bank (x : Positions (Primary n G)) := WilsonRunVacuumWickCubature.bank K F t x (U fine)
  let Q:=R.alloy.B.kin.path N (j+1)
  let q:=(V.params (j+1)).clip
  let action(A : Nesting G fine):=colorCut F t Q q R.metals.O A (K.b F)
  have original:=WilsonConditionalTaylorUnresetForest.actual R j lo hi scene F t
  have donor:=(scene.budget (j+1) hi (lo.trans (Nat.le_succ j))).1
  have book:=RunFormalChain.fromRun R
  have room := paid R u scene j lo hi F t
  obtain ⟨s,hs,accounted⟩:=account supply donor.bond (splitK _)
  have taken := WilsonConditionalTaylorVacuumPrefix.received F t Q q R.metals.O (K.b F) room donor.bond (splitK _) s hs accounted
  have cut : Through cap T (action B):=fun e he=>(original e he).trans (taken e he)
  have center (x : Positions (Primary n G)) : view x (action B)=covelog (bank x)-covelog (bank 0) :=
    coordinates R j hi F t (U fine) x
  intro e he r live
  by_cases nil : e=0
  · subst e;rw [(received R scene j lo hi).2.1,show coeff 0 (stored Z)=0 from splitK _]
  have pos : 0<e:=by omega
  have label (x : Positions (Primary n G)) :
      MvPolynomial.eval x (coeff e L)=MvPolynomial.eval x (coeff e T)+coeff e (covelog (bank 0)):=by
    have measured := congrArg (coeff e) (center x)
    change MvPolynomial.eval x (coeff e (action B))= _ at measured
    rw [←cut _ he,map_sub] at measured
    have free:=congrArg (coeff e) ((WilsonMeasuredVacuumGerm.gauge Z x).trans (finite x))
    change MvPolynomial.eval x (coeff e L)=coeff e (C (traceP _ H.main)+covelog (bank x)) at free
    rw [map_add,PowerSeries.coeff_C,if_neg nil,zero_add] at free
    linarith
  have priced : coeff e L=coeff e T+MvPolynomial.C (coeff e (covelog (bank 0))):=by
    apply MvPolynomial.funext
    intro x
    simpa only [map_add,MvPolynomial.eval_C] using label x
  change MvPolynomial.homogeneousComponent r (coeff e T)=MvPolynomial.homogeneousComponent r (coeff e (splitV L))
  rw [WilsonConditionalTaylorFieldReset.positive L pos,priced,map_add,
    MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_C _ _),if_neg live.ne',add_zero]

end YM.Integration.WilsonConditionalTaylorRawAttachment

