import YM.Integration.WilsonIndependentMatchedElectedSection
import YM.Integration.WilsonIndependentRawNamedProduct
import YM.Integration.WilsonIndependentGroupedOrbit

/-! Co-issue the true conventional orbit test and its angular symbol
from precisely the section filed by the independent master. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedElectedOrbit
open Lattice Matrix RG Source Labels PertExtension Orb XSpace XSpace.Rose XSpace.Cirrus
open Wilson Tree WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer.Patrol
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Halo
open RegulatorIR.Profiles RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Step RegulatorIR.Prim RegulatorIR.Cluster RegulatorIR.Diagram FVA2
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge Gauge Orb.SlotEvaluation
open WilsonIndependentSpoutOrdinaryPlate (sample)
open PertExtension.Series.Tested
open scoped Classical BigOperators
variable {G:Gauge}

structure Letter (G:Gauge) where
  d:ℕ
  F:Labels.Frame G d
  T:SectionData F
  H:Hol G
  sound:T.Sound H
  order:Bid.pop T
  key:F.Index
  root:Cover

def chosen {H:Hol G}(M:Master H)(h:ℕ)(a:(M.F h).Index)(o:Cover):Letter G:=
  ⟨h,M.F h,M.T h,H,M.spec h,M.pop h,a,o⟩

def filed (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(s:Bool)(h:ℕ)
    (a:(R.family.labels.level h).Index)(o:Cover):Letter G:=by
  cases s with
  | false=>exact ⟨h,_,R.family.localSection h,R.family.params,R.makes.sections h,FVAAlt2.Block.clothes R h,a,o⟩
  | true=>
    have z:=WilsonOriginalPivotWardSurvey.issued R W h
    exact ⟨h,_,WilsonOriginalPivotWardSurvey.sectionAt R W h,W.hol,z.1,z.2.1,a,o⟩

namespace Letter
variable (B:Letter G)
def grade:= (B.F.grades B.key).2
def print:=convey B.root (Profiles.bare B.T B.key)
def group (n:Side):Config G n→ℝ:=fieldAt B.T B.key (wrap n B.root)
theorem localStamp:LocalStamp (Profiles.bare B.T B.key) B.grade:=authentically _ B.sound B.order B.key
def native:Orders (Foot G):=fun i r=>echo (carryX B.root) ((stamp_symbol B.localStamp).choose i r)
theorem named:BasisT B.grade B.grade B.print B.native ∧ Ranks B.grade B.native:=by
  obtain ⟨H,N⟩:=(stamp_symbol B.localStamp).choose_spec
  refine ⟨H.vayne B.root,?_⟩
  intro i j live
  apply N i j
  intro z
  apply live
  exact (congrArg (echo (carryX B.root)) z).trans echo_zero

theorem proper (n:Side):Orb.PreTest (B.group n):=(pre_field B.T B.sound B.order B.key _).1

theorem onTorus {n:Side}(y:TreeVars G n)(t:ℝ):
    RegulatorIR.Halo.outing G B.print (sample y) t=B.group n (mantle (t • y)):=by
  unfold RegulatorIR.Halo.outing
  rw [←WilsonIndependentSpoutOrdinaryPlate.dilate,WilsonIndependentSpoutOrdinaryPlate.links]
  have eq:translate B.root (expandAt 0 (mantle (t • y)))=
      expandAt (wrap n B.root) (mantle (t • y)):=by
    funext i
    change (mantle (t • y)) (wrap n (i.1+B.root)+0,i.2)=
      (mantle (t • y)) (wrap n i.1+wrap n B.root,i.2)
    rw [add_zero,map_add]
  change (B.T.evaluate _ _).re=_
  rw [eq]
  rfl

theorem quote {n:Side}(y:TreeVars G n):
    PowerSeries.X^B.grade*shelter B.grade B.native (sample y)=
      tale (fun t:ℝ=>B.group n (mantle (t • y))):=by
  rw [←B.named.1.pose]
  exact congrArg tale (funext (B.onTorus y))

theorem onOrbit (n:Side):
    vital n B.print=WilsonIndependentMatchedOrbitReading.insert (B.group n):=by
  funext t v _
  have hp:translate B.root (orbLift v ∘ around n)=expandAt (wrap n B.root) (Orb.liftLinks v):=by
    funext e
    change Orb.liftLinks v (wrap n (e.1+B.root),e.2)=
      Orb.liftLinks v (wrap n e.1+wrap n B.root,e.2)
    rw [map_add]
  change (B.T.evaluate (Pi.single B.key 1) _).re=_
  rw [hp]
  rfl
end Letter

def face {n:Side}(S:Finset (Fin 2))(B:Fin 2→Letter G):Config G n→ℝ:=
  ∏i∈S,(B i).group n

theorem admitted {n:Side}(S:Finset (Fin 2))(B:Fin 2→Letter G):Orb.PreTest (face (n:=n) S B):=by
  induction S using Finset.induction_on with
  | empty=>change Orb.PreTest (∏i∈(∅:Finset (Fin 2)),(B i).group n)
           rw [Finset.prod_empty]
           exact ⟨fun _ _ _=>rfl,⟨continuous_const,contDiffAt_const⟩,continuous_const⟩
  | insert i s hi ih=>
    unfold face at *
    rw [Finset.prod_insert hi]
    exact WilsonIndependentMatchedClosedPlan.product ((B i).proper n) ih

theorem original {Y:Period}{F:Fabric G Y.side}(C:Fabric.Cloth F)
    (z:F.Accounts→PowerSeries ℝ)(pos:∀i,0<PowerSeries.coeff 0 (z i))(unit:z none=1)
    (W:Initialize G)(B:Fin 2→Letter G)(S:Finset (Fin 2)):
    let O:=face (n:=Y.side) S B
    let f:=WilsonIndependentGroupedOrbit.paid C z pos O
    Bare.normalized (W.tree Y) G (FVA2.BareOrb.stencil (W.tree Y) O)=FVA2.TaylorWick.into f ∧
      Aspiration (Orb.preExpectation O) (fun k=>PowerSeries.coeff k f):=
  ⟨WilsonIndependentGroupedOrbit.original C z pos unit _ (admitted S B) W,
    WilsonIndependentGroupedOrbit.before C z pos unit _ (admitted S B)⟩

end YM.Integration.WilsonIndependentMatchedElectedOrbit
