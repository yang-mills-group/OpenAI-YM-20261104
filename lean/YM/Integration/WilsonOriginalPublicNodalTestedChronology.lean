import YM.Integration.WilsonOriginalPublicNodalTestedCore
import YM.Integration.WilsonOriginalPublicNodalTestedRoster
import YM.Integration.WilsonIndependentMatchedCoverGrade
import YM.Integration.WilsonMaxwellThermometerMaximalHead

/-! The measured source on its original vacuum, with all test amplitudes carried by the dated clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedChronology
open Precision Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider
open WilsonCoeffUV.Winding WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open XSpace XSpace.Rose RegulatorIR RegulatorIR.Cluster PhysicalNext.Repeat.Legato
open WilsonIndependentRawRosterWord (degree fold)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonReceivedFixedDigitHistory (Digits)
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(W:Initialize G)(D d:I→ℕ)
    (b:∀i,(R.family.labels.level (d i)).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)

private theorem accounts {T:Type}[Fintype T][Nonempty T](e:T→ℕ):
    ordered.accounts e=∑i,e i:=by
  classical
  have joined (J:Composite T):fold (fun i=>Multiplicative.ofAdd (e i)) J=Multiplicative.ofAdd (J.accounts e):=by
    induction J with
    | atom i=>rfl
    | pair p q hp hq=>rw [WilsonIndependentRawRosterWord.fold,hp,hq]; rfl
  have tally (s:Finset T):(∏i∈s,Multiplicative.ofAdd (e i))=Multiplicative.ofAdd (∑i∈s,e i):=by
    induction s using Finset.induction_on with
    | empty=>simp
    | insert i s h ih=>rw [prod_insert h,sum_insert h,ih]; rfl
  have seen:=(entered (I:=T)).product (Multiplicative ℕ) (fun i=>Multiplicative.ofAdd (e i))
  rw [joined,tally] at seen
  exact congrArg Multiplicative.toAdd seen

def rank (S:Finset I)[Nonempty S]:ℕ:=ordered.accounts (degree R (fun i:S=>d i) (fun i:S=>b i))

omit [Fintype I] [DecidableEq I] in
theorem funded (S:Finset I)[Nonempty S]:rank R d b S ≤ mass d S:=by
  rw [rank,accounts,mass,←Finset.sum_coe_sort S]
  apply Finset.sum_le_sum
  intro i _
  exact (WilsonMaxwellThermometerMaximalHead.rank _ _).trans (Nat.div_le_self ..)

def tender (A:Case D)(S:Finset I):Cost:=∏i:S,WilsonOriginalPublicNodalTestedRoster.cash R D d b κ pt A i

variable {stamps:I→ℕ}(cut:∀i,d i<stamps i)

def registered (o:I → Cover)(S:Finset I)[Nonempty S]:Era G ℝ:=
  field R W (fun _:S=>false) (fun i:S=>d i) (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered

theorem original (simple:G.Simple)(N:ℕ)(cells:Digits R.family.path.levels I)(v c K:ℕ)(vc:v≤c)(cK:c≤K)(KN:K≤N)
    (y:I → Cover)(S:Finset I)[Nonempty S](A:Case D):
    let L:=R.family.path.levels
    let O:=R.metals.O
    let raw:=registered R W d b cut (roots L cells (K-c) c y) S
    let price:=tender R D d b κ pt A S
    cruises L O N (mass d S) c v
        (WilsonOlderFreshSoftOrdinary.material D d L O (WilsonOlderFreshSoftFigures.stencil R D d b κ pt)
          N cells c K y S (touch A S))=
      affiled (WilsonOlderFreshSoftCoverScalar.clock L O N K v price)
        (cruises L O N (rank R d b S) K v raw):=by
  let L:=R.family.path.levels
  let O:=R.metals.O
  let o:=roots L cells (K-c) c y
  let raw:=registered R W d b cut o S
  let price:=tender R D d b κ pt A S
  let h:=rank R d b S
  have genuine:Auth h raw:=WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _:S=>false)
    (fun i:S=>d i) (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered
  have moved:=WilsonIndependentMatchedOpeningFee.grant _ genuine price
  obtain ⟨_,_,sold⟩:=WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one
  have real:Wellness d (WilsonOlderFreshSoftFigures.stencil R D d b κ pt):=(sold b κ pt).1
  dsimp only
  rw [WilsonOriginalPublicNodalTestedCore.original L O d N cells simple R.alloy.B.ratio _ real v c K vc cK KN]
  rw [show tuftV (touch A S) (levelsO (WilsonOlderFreshSoftFigures.stencil R D d b κ pt o) S)=affiled price raw from
    WilsonOriginalPublicNodalTestedRoster.original R W D d b κ pt cut o A S]
  rw [←WilsonIndependentMatchedCoverGrade.carried L O simple R.alloy.B.ratio (vc.trans cK) KN _ moved (funded R d b S)]
  have filed (n:Side):(affiled price raw).1 n=affix price (raw.1 n):=rfl
  apply Prod.ext
  · funext n
    exact WilsonOlderFreshSoftSocketHistory.finite L O simple R.alloy.B.ratio N h K v (vc.trans cK) KN _ _ price genuine filed n
  · exact WilsonOlderFreshSoftSocketHistory.original L O simple R.alloy.B.ratio N h K v (vc.trans cK) KN _ _ price moved genuine filed

end YM.Integration.WilsonOriginalPublicNodalTestedChronology
end
