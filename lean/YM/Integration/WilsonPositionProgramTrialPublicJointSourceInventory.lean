import YM.Integration.WilsonPositionProgramTrialPublicJointSourceFaculty
import YM.Integration.WilsonPositionProgramTrialPublicJointSourceProjected
import YM.Integration.WilsonIndependentMatchedOpeningColumn

/-! Literal surveyed own-horizon, common-cap, and null letters at their chosen
Wilson sites. The same compact inputs have their full nonlinear measurement on
the appointed registered court. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceInventory
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace XSpace.Cirrus XSpace.Rose XSpace.Normalize
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedNamedPair (printed sectionAt)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonThermometerPositionTunedSurvey (rates corrected)
open WilsonPositionProgramTrialPublicJointSourceFaculty (coordinate measured)
open WilsonPositionProgramTrialPublicJointFirstSource (site)
open scoped BigOperators Classical Topology
variable {G:Gauge}{h k u e:ℕ}(R:Run G)(W:Initialize G)(Y:Sample 2)
local notation "T" => W.tree Y.F.p
local notation "F_" d:arg => R.family.labels.level d

def lifted (k:ℕ)(v:On.Grade G k):Label G k:=
  On.sectionMap k (Submodule.inclusion (show On.Grade G k≤_ from inf_le_left) v)

def rack (d:ℕ)(z:Lattice.Cover)(p:Label G d):Bare.Series T G:=
  ∑b:(F_ d).Index,rates R W d p b • printed R W Y true d z b

theorem filed (d:ℕ)(z:Lattice.Cover)(p:Label G d):
    Bare.column T (W.surveys d) (wrap Y.F.p.side z) p=rack R W Y d z p:=
  corrected R W d Y.F.p T (wrap Y.F.p.side z) p

theorem owned (d:ℕ)(z:Lattice.Cover)(v:On.Grade G d):
    On.stencil W.hol (W.surveys d) Y.F.p T (wrap Y.F.p.side z) v=
      rack R W Y d z (lifted d v):=filed R W Y d z (lifted d v)

theorem original {n:ℕ}(p:Sec G h)(z:Fin (n+1)→Lattice.Cover)(i:Fin (n+1)):
    regal W h (site Y z) (chartV (site Y z) i) p=
      ∑k:Fin (h+1),(((Y.F.spacing:ℂ)^k.val)⁻¹) •
        rack R W Y k.val (z i) (lifted k.val (part h k.val p)):=by
  unfold regal
  rw [LinearMap.sum_apply]
  apply sum_congr rfl
  intro k _
  change (((Y.F.spacing:ℂ)^k.val)⁻¹) • On.stencil W.hol (W.surveys k.val) Y.F.p T
    (wrap Y.F.p.side (z i)) (part h k.val p)=_
  rw [owned]

def inlet (d:ℕ)(b:(F_ d).Index):Verse (F_ d):=Pi.single (WilsonPositionProgramSubmittedCoordinates.plain (F_ d) b) 1

variable {H:Hol G}{Q:SealR G}{rail:Rails Q.h k u e}{E W' B V:Credit}
theorem register (X:CutsP H Q.ans Q.path rail E W' B V)(d:ℕ)(fit:d<Q.D)(cap:d≤k):
    ∃A:Alma (F_ d)→ℝ,(∀s,0≤A s) ∧ ∃C:Credit,∀b:(F_ d).Index,
      let c:=inlet R d b
      let P:=Shrine (plate (sectionAt R W true d) fit) c
      ∃Y':CutsP H Q.ans Q.path rail E W' B V,
        Y'.L=X.L ∧ Y'.L'=X.L' ∧ Y'.m=X.m ∧ Y'.i=X.i ∧ Y'.N=X.ceilC ∧ Y'.pt=P ∧
        Y'.fuel=charge e c A ∧ Y'.tileP=coordinate Q X P ∧ WilsonPositionProgramTrialAccrued.home Q Y'=measured Q X P ∧
        coordinate Q X P=opal Q.F P+boot X.ax X.tx Q.ans Q.path X.ceilC k X.ceilC X.m X.i (Silt Y'.Ntop P) ∧
        ∀t≤e,∀j≤X.i,∀r,Fruit 0 1 u ((Y'.springP j).2 t r)
          (C.buy Y'.Age*Real.exp (-(X.ax.S.scale X.ceilC-X.ax.S.scale (X.m+j))/4)*charge e c A):=by
  obtain ⟨A,nonneg,C,source⟩:=WilsonPositionProgramTrialPublicJointSourceFaculty.original Q X R W true fit cap
  refine ⟨A,nonneg,C,?_⟩
  intro b c P
  obtain ⟨K,ls,ts,m,i,N,entered,fee,res,home,acct,_,_,_,growth⟩:=source c
  exact ⟨K,ls,ts,m,i,N,entered,fee,res,home,acct,growth⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceInventory
