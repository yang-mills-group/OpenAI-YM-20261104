import YM.Integration.WilsonIndependentConditionalMerReceiver
import YM.Integration.WilsonIndependentConditionalCoordinateVerse
import YM.Integration.WilsonIndependentPublicCoverFields
import YM.RegulatorIR.Oracle.Arrange

/-! Actual fine and coarse link charts of the common Wilson notebook. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalNativeLinks
open Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open RegulatorIR.Oracle RegulatorIR.Quadratic RegulatorIR.Step RegulatorIR.Prim RegulatorIR.Ledger
open RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonIndependentConditionalUnshiftedExit WilsonIndependentConditionalCoordinateHeat
open scoped BigOperators Matrix Classical
variable {G:Gauge}

def fine (G:Gauge)(P:Patch):Foot G≃Cloth (Larvae G P.L):=(blockQ G P.L).toFull
def coarse (G:Gauge):Foot G≃YForest G:=(linksQ G).toFull
def joint (G:Gauge)(P:Patch):KFoot G≃Cloth (Hinge G P.L):=
  ((fine G P).sumCongr (coarse G)).trans (Equiv.prodSumDistrib _ _ _).symm

theorem fine_link (P:Patch)(x:Foot G):panel P.L (Hooks G) (fine G P x)=coarse G x:=by
  let w:=(site_eq G) x
  change ((panel P.L (Hooks G)) ((geological P.L (Hooks G)).toFull w))=w
  rcases w with ⟨v,y⟩
  obtain ⟨⟨j,u⟩,h⟩:=(RegulatorIR.Sources.claims P.L).surjective v
  subst v
  change (panel P.L _) ((geological P.L _).toFull (RegulatorIR.Sources.child P.L j u,y))=_
  rw [landFull]
  rfl

variable {Ω:Type}{M:Ω→ℕ}{n:Page M→Side}
variable {A:Levels G}{C:Circuit M n}{K:KernelChoices}{s:ℕ}{w:Ω}
variable (R:WilsonIndependentPublicFreeTrain.Matches A C K s w)
variable (Y:Program K)(Z:∀P:Patch,P.Branches K G)(t:Page M→RegulatorIR.Binding.Scale)
variable (f:Flap M)(hw:f.volW=w)

include R hw

theorem covariance :
    let m:=s+(M w-(f.offset+1));let P:=loose A m
    (C.devices Y G Z t f).line=line (joint G P)
      (WilsonIndependentConditionalUnshiftedQuiet.kernel P (shuttleM (conditional A (s+M w) m))):=by
  intro m P
  have bills:=WilsonIndependentPublicCoverFields.original R Y Z f hw
  change petals (C.pulses Y G Z f)=_
  rw [bills.1]
  funext a b
  cases a <;> cases b <;> rfl

theorem predictor :
    let m:=s+(M w-(f.offset+1));let P:=loose A m
    (C.devices Y G Z t f).driftL=line (joint G P) (post P (shuttleM (feedA A (s+M w) m))).transpose:=by
  intro m P
  have bills:=WilsonIndependentPublicCoverFields.original R Y Z f hw
  change Function.swap (hoses (C.sails Y G f))=_
  rw [bills.2]
  funext a b
  cases a with
  | inl a=>cases b <;> rfl
  | inr a=>
    cases b with
    | inl b=>rfl
    | inr b=>
      change ID (Foot G) b a=(1:ropes Cover (Hooks G) (Hooks G)) (coarse G b) (coarse G a)
      by_cases h:b=a <;> simp [ID,Matrix.one_apply,(coarse G).injective.eq_iff,h]

omit R hw in
theorem projected (P:Patch){r:ℕ}(F:Packet (Cloth (Hinge G P.L)) r):
    crop (lastChannel (C.opened G f.prev) (C.opened G f.next)).native (row (joint G P) F)=row (coarse G) (scoop F):=rfl

theorem pull {r:ℕ}(F:Packet (Cloth (Hinge G (loose A (s+(M w-(f.offset+1)))).L)) r):
    let m:=s+(M w-(f.offset+1));let P:=loose A m
    (C.devices Y G Z t f).pullI (row (joint G P) F)=row (coarse G) (scoop (Packet.draft (post P (shuttleM (feedA A (s+M w) m))).transpose F)):=by
  intro m P
  unfold GridStep.pullI
  rw [predictor R Y Z t f hw,WilsonIndependentConditionalCoordinateHeat.draft]
  exact projected _ _ _

end YM.Integration.WilsonIndependentConditionalNativeLinks
