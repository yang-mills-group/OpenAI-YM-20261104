import YM.Integration.WilsonIndependentConditionedFolioCoin
import YM.Integration.WilsonIndependentConditionedFolioWeights

/-! The complete signed normalized reading at the old receiver in the actual submitted cutoff basis. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioScalar
open Function Finset Lattice Wilson RG Source Labels Precision Laurent PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open RegulatorIR XSpace XSpace.Rose
open PhysicalNext.Repeat.Legato IndependentSourcePathFamily
open WilsonOlderFreshSoftSocketMeasuredCash (seats ticket)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshSoftSocketRestored (coin rated)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOriginalPublicNodalTestedFunctional (deposit)
open WilsonOriginalPublicNodalTestedChronology (registered rank)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonOriginalPublicNodalTestedRelease (scaled)
open WilsonOlderFreshHybridClock (flat)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonIndependentConditionedFolioWeights (payment)
open scoped Classical BigOperators

private theorem sumValue {J:Type}[Fintype J](u:J→ Cost)(p:ℕ)(x:ℝ):
    value p (∑j,u j) x=∑j,value p (u j) x:=by
  unfold value
  simp only [map_sum,Finset.mul_sum]
  rw [sum_comm]

variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G)(W:Initialize G)(D d:I→ℕ)
    {stamps:I→ℕ}(cut:∀i,d i<stamps i)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
    (N per K c v:ℕ)(track:Digits R.family.path.levels I)(y:I→ Cover)(S:Finset I)[Nonempty S]
    (f:Pen D S→L[ℝ]ℝ)
local notation "A_" => R.family.path.levels
local notation "O_" => R.metals.O
local notation "B_" b:max => seats R d S b
local notation "w_" b:max => request R d (B_ b) (N:=N) (p:=per) (K:=K)
local notation "old_" => WilsonOlderFreshSoftSocketRestored.stopped R d N K c v track y S f
local notation "Z_" q:max => old_ (start R d κ pt (fill R d S q))
def column (b:(i:S)→(R.family.labels.level (d i)).Index):Era G ℝ:=
  cruises A_ O_ N (WilsonOriginalPublicNodalTestedChronology.rank R d (B_ b) S) K v
    (registered R W d (B_ b) cut (roots A_ track (K-c) c y) S)

theorem basis (b:(i:S)→(R.family.labels.level (d i)).Index)(simple:G.Simple)(ratio:LocalRatio O_)
    (vc:v≤c)(ck:c≤K)(kn:K≤N)(p:ℕ)(x:ℝ):
    ∑q:Selection R d S,ticket R d S (w_ b) N per K q*(flat (Z_ q) p x:ℂ)=
      ((f (deposit D κ pt S)*flat (column R W d cut N K c v track y S b) p x:ℝ):ℂ):=by
  let P:=column R W d cut N K c v track y S b
  have component (L:ℂ→L[ℝ]ℝ):
      L (∑q:Selection R d S,ticket R d S (w_ b) N per K q*(flat (Z_ q) p x:ℂ))=
        L ((f (deposit D κ pt S)*flat P p x:ℝ):ℂ):=by
    have project (z:ℂ)(u:ℝ):L (z*(u:ℂ))=L z*u:=by
      rw [mul_comm z,←Complex.real_smul,L.map_smul,smul_eq_mul,mul_comm]
    have rhs (u:ℝ):L (u:ℂ)=L 1*u:=by simpa using project 1 u
    have exactSource:=WilsonIndependentConditionedFolioCoin.original R W D d cut κ pt N per K c v track y S f b L simple ratio vc ck kn
    have paid:=congrArg (fun U=>value p U x) exactSource
    change value p (∑q:Selection R d S,C (L (ticket R d S (w_ b) N per K q))*coin (Z_ q)) x=
      value p (C (L 1)*C (f (deposit D κ pt S))*coin P) x at paid
    rw [sumValue,mul_assoc] at paid
    simp only [WilsonOriginalPublicNodalTestedRelease.scaled,←rated] at paid
    simpa only [map_sum,project,rhs] using paid
  exact Complex.ext (component Complex.reCLM) (component Complex.imCLM)

theorem original (w:(i:I)→R.family.label (d i))(simple:G.Simple)(ratio:LocalRatio O_)
    (vc:v≤c)(ck:c≤K)(kn:K≤N)(p:ℕ)(x:ℝ):
    WilsonOlderFreshSoftSocketTotal.normalized R d κ pt N per K c v track S w y f p x=
    ∑b:(i:S)→(R.family.labels.level (d i)).Index,payment R d N per K w S b*
      ((f (deposit D κ pt S)*flat (column R W d cut N K c v track y S b) p x:ℝ):ℂ):=by
  classical
  unfold WilsonOlderFreshSoftSocketTotal.normalized
  simp only [WilsonIndependentConditionedFolioWeights.original R d N per K w S kn,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [←Finset.mul_sum,basis R W D d cut κ pt N per K c v track y S f b simple ratio vc ck kn p x]

end YM.Integration.WilsonIndependentConditionedFolioScalar
end
