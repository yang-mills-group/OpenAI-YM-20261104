import YM.Integration.WilsonOriginalObservedRoseStickerSeries
import YM.Integration.WilsonReceivedCanonicalSocketLevels
import YM.Integration.WilsonReceivedDepositedVerseCensus
import YM.Integration.WilsonIndependentRawPhysicalFaces
import YM.Integration.WilsonIndependentMatchedOpeningFee

/-! The tested fixed-child Rose group and its independently filed complete public source at every finite and covered rank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedRoster
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open IndependentSourcePathFamily
open WilsonIndependentRawRosterWord (degree fold)
open WilsonIndependentMatchedOpeningRoster (seat field)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonReceivedDepositedVerseCensus (ordinary)
open private dark from YM.Integration.IndependentSourcePathFamily
open scoped Classical BigOperators Topology

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(W:Initialize G)(D d:I→ℕ)
    (b:∀i,(R.family.labels.level (d i)).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
local notation "F" i:max => R.family.labels.level (d i)

def cash (A:Case D)(i:I):Cost:=PowerSeries.C (claim (D i) (κ i) (pt i) (A i))*
  (PowerSeries.X:Cost)^((F i).grades (b i)).2

variable {stamps:I→ℕ}(cut:∀i,d i<stamps i)(o:I → Cover)
local notation "col" i:max => column R W false (cut i) (seat (F i) (b i)) (o i)

omit [Fintype I] [DecidableEq I] in
theorem folded (J:Composite I)(n:Side):
    flash ((field R W (fun _:I=>false) d b cut o J).1 n)=fold (fun i=>flash ((col i).1 n)) J:=by
  induction J with
  | atom i=>rfl
  | pair A B ha hb=>
    have pa:=WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _:I=>false) d b cut o A
    have pb:=WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _:I=>false) d b cut o B
    change flash (woad _ _) = _*_
    rw [woadap _ _ (finite_shell (pa.span n)) (finite_shell (pb.span n)),ha,hb]

theorem original (A:Case D)(S:Finset I)[Nonempty S]:
    ordinary (WilsonOlderFreshSoftFigures.stencil R D d b κ pt o) A S=
      affiled (∏i:S,cash R D d b κ pt A i)
        (field R W (fun _:S=>false) (fun i:S=>d i) (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered):=by
  let M:=WilsonOlderFreshSoftFigures.stencil R D d b κ pt o
  obtain ⟨_,_,sold⟩:=WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one
  have good:Eu d M:=(sold b κ pt).1.level' o
  have left:Auth (mass d S) (ordinary M A S):=(placedO _ good S).tuft (touch A S)
  let K:=field R W (fun _:S=>false) (fun i:S=>d i) (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered
  have genuine:=WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _:S=>false) (fun i:S=>d i)
    (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered
  let wage:=∏i:S,cash R D d b κ pt A i
  have right:=WilsonIndependentMatchedOpeningFee.grant K genuine wage
  apply left.ext right
  funext n
  apply by_flash (left.span n) (right.span n) (left.pale n) (right.pale n)
  change readO A (levelsO M S) n=flash (affix wage (K.1 n))
  rw [WilsonReceivedCanonicalSocketLevels.original M good (dark _ _) A n S,←Finset.prod_coe_sort S,
    sponsor _ _ (genuine.span n)]
  have factors:=folded R W (fun i:S=>d i) (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered n
  rw [(entered (I:=S)).product] at factors
  rw [show flash (K.1 n)=∏i:S,flash ((col (i:I)).1 n) from factors]
  dsimp only [wage]
  rw [map_prod,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [show readO A (M {(i:I)}) n=_ from
    WilsonOriginalObservedRoseStickerSeries.original R D d b κ pt W stamps cut o A i n]
  simp [cash,Blue.soil,realS]

end YM.Integration.WilsonOriginalPublicNodalTestedRoster
end
