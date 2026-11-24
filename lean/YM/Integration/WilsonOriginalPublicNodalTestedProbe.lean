import YM.Integration.WilsonOriginalPublicNodalTestedFunctional
import YM.Integration.WilsonIndependentSpoutDoseBoundary

/-! The real observed charge and its native conversion at the reported K-source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedProbe
open Laurent Bloch Precision Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open XSpace XSpace.Rose RegulatorIR RegulatorIR.Cluster PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOriginalPublicNodalTestedFunctional (deposit power charge)
open WilsonOriginalPublicNodalTestedChronology (registered rank funded)
open private accounts from YM.Integration.WilsonOriginalPublicNodalTestedChronology
open WilsonIndependentRawPhysicalFaces (ordered)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutDoseBoundary (into measure)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(W:Initialize G)(D d:I→ℕ)
    (b:∀i,(R.family.labels.level (d i)).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)

omit [Fintype I] [DecidableEq I] in
theorem bounded (S:Finset I)(test:Pen D S→L[ℝ] ℝ):‖test (deposit D κ pt S)‖≤‖test‖:=by
  have fee:‖deposit D κ pt S‖≤1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul]
    change ‖(x:Pier D) (fun i=>(κ i,pt i))‖ ≤ ‖(x:Pier D)‖
    exact ContinuousMap.norm_coe_le_norm x.val (fun i=>(κ i,pt i))
  simpa only [mul_one] using (test.le_opNorm _).trans (mul_le_mul_of_nonneg_left fee (norm_nonneg _))

omit [Fintype I] [DecidableEq I] in
theorem valuation (S:Finset I)[Nonempty S](test:Pen D S→L[ℝ] ℝ):
    charge R D d b κ pt S test=PowerSeries.C (test (deposit D κ pt S))*(PowerSeries.X:Cost)^(rank R d b S):=by
  let e:=WilsonIndependentRawRosterWord.degree R (fun i:S=>d i) (fun i:S=>b i)
  have total (s:Finset S):(∏i∈s,(PowerSeries.X:Cost)^(e i))=PowerSeries.X^(∑i∈s,e i):=by
    induction s using Finset.induction_on with
    | empty=>simp
    | insert i s h ih=>rw [prod_insert h,sum_insert h,ih,pow_add]
  unfold WilsonOriginalPublicNodalTestedFunctional.charge
  congr 1
  rw [rank,accounts]
  exact total Finset.univ

variable {stamps:I→ℕ}(cut:∀i,d i<stamps i)

theorem original (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(valid:LocalRatio O)
    (N:ℕ)(cells:Digits L I)(v c K:ℕ)(vc:v≤c)(cK:c≤K)(KN:K≤N)
    (y:I → Cover)(S:Finset I)[Nonempty S](test:Pen D S→L[ℝ] ℝ):
    let h:=rank R d b S
    let raw:=registered R W d b cut (roots L cells (K-c) c y) S
    let stake:=charge R D d b κ pt S test
    let observed:=cruises L O N (mass d S) c v
      (WilsonOlderFreshSoftOrdinary.material D d L O (WilsonOlderFreshSoftFigures.stencil R D d b κ pt)
        N cells c K y S test)
    observed=affiled (clock L O N K v stake) (cruises L O N h K v raw) ∧
    into L O N v (ground observed)=into L O N K stake*measure L O N h K v raw:=by
  let h:=rank R d b S
  let o:=roots L cells (K-c) c y
  let raw:=registered R W d b cut o S
  let stake:=charge R D d b κ pt S test
  have genuine:Auth h raw:=WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _:S=>false)
    (fun i:S=>d i) (fun i:S=>b i) (fun i:S=>cut i) (fun i:S=>o i) ordered
  have moved:=WilsonIndependentMatchedOpeningFee.grant raw genuine stake
  obtain ⟨_,_,sold⟩:=WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one
  have real:Wellness d (WilsonOlderFreshSoftFigures.stencil R D d b κ pt):=(sold b κ pt).1
  dsimp only
  rw [WilsonOriginalPublicNodalTestedCore.original L O d N cells simple valid _ real v c K vc cK KN,
    WilsonOriginalPublicNodalTestedFunctional.original R W D d b κ pt cut o S test,
    ←WilsonIndependentMatchedCoverGrade.carried L O simple valid (vc.trans cK) KN _ moved (funded R d b S)]
  have filed (n:Side):(affiled stake raw).1 n=affix stake (raw.1 n):=rfl
  constructor
  · apply Prod.ext
    · funext n
      exact WilsonOlderFreshSoftSocketHistory.finite L O simple valid N h K v (vc.trans cK) KN _ _ stake genuine filed n
    · exact WilsonOlderFreshSoftSocketHistory.original L O simple valid N h K v (vc.trans cK) KN _ _ stake moved genuine filed
  · exact WilsonIndependentSpoutDoseBoundary.earned L O simple valid N h K v (vc.trans cK) KN _ _ _ moved genuine filed

end YM.Integration.WilsonOriginalPublicNodalTestedProbe
end
