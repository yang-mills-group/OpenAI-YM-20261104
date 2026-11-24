import YM.Integration.WilsonIndependentConditionedFolioPoles
import YM.Integration.WilsonOriginalPublicNodalTestedProbe
import YM.Integration.WilsonOriginalPublicNodalTestedRelease

/-! The normalized socket and the normalized physical column on their common actual conditional course. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioCoin
open Bloch Precision Marker Function Finset Lattice Wilson RG Source Labels Tree Exterior Laurent PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Cosmos PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose
open PhysicalNext.Repeat.Legato IndependentSourcePathFamily OriginalMarkedSourceComet
open WilsonOlderFreshSoftSocketMeasuredCash (seats ticket packet)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOlderFreshSoftSocketRestored (stopped coin degree)
open WilsonOlderFreshSoftSocketKinetic (reading kinetic valued)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonOriginalPublicNodalTestedFunctional (deposit charge)
open WilsonOriginalPublicNodalTestedChronology (registered rank)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonReceivedFixedDigitHistory
open private accounts from YM.Integration.WilsonOriginalPublicNodalTestedChronology
open scoped Classical BigOperators
variable {G:Gauge}

def meter : Era G ℝ→ₗ[ℝ]Cost where
  toFun:=coin
  map_add' P Q:=by
    ext1 j
    simp [coin,WilsonOlderFreshSoftSocketKinetic.reading]
  map_smul' z P:=by
    ext1 j
    simp [coin,WilsonOlderFreshSoftSocketKinetic.reading]

theorem scalar (z:ℝ)(u:Cost):z • u=C z*u:=by
  ext1 j
  rw [coeff_C_mul]
  simp

theorem nonzero (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N K v h:ℕ)(vk:v≤K)(kn:K≤N):clock A O N K v (X^h)≠0:=by
  have unit:=WilsonOlderFreshSoftSocketKinetic.unit A O simple ratio N K v vk kn
  have live:kinetic A O N K v≠0:=by
    intro zero
    rw [zero,map_zero] at unit
    exact zero_ne_one unit
  rw [WilsonOlderFreshSoftSocketKinetic.pole A O N K v h vk]
  exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ live)

variable {I:Type}[DecidableEq I][Fintype I](R:Run G)(W:Initialize G)(D d:I→ℕ)
    {stamps:I→ℕ}(cut:∀i,d i<stamps i)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
    (N per K c v:ℕ)(track:Digits R.family.path.levels I)(y:I→ Cover)(S:Finset I)[Nonempty S]
    (f:Pen D S→L[ℝ]ℝ)(b:(i:S)→(R.family.labels.level (d i)).Index)(L:ℂ→L[ℝ]ℝ)
local notation "A_" => R.family.path.levels
local notation "O_" => R.metals.O
local notation "B_" => seats R d S b
local notation "w_" => request R d B_ (N:=N) (p:=per) (K:=K)
local notation "h_" => WilsonOriginalPublicNodalTestedChronology.rank R d B_ S
local notation "old_" => WilsonOlderFreshSoftSocketRestored.stopped R d N K c v track y S f
local notation "real_" => cruises A_ O_ N h_ K v (registered R W d B_ cut (roots A_ track (K-c) c y) S)
local notation "toll_" => WilsonOlderFreshSoftCoverScalar.clock A_ O_ N K v (X^h_)
local notation "Z_" q:max => old_ (start R d κ pt (fill R d S q))
local notation "H_" q:max => old_ (raw R d κ pt (fill R d S q))

theorem original (simple:G.Simple)(ratio:LocalRatio O_)(vc:v≤c)(ck:c≤K)(kn:K≤N):
    ∑q:Selection R d S,C (L (ticket R d S w_ N per K q))*coin (Z_ q)=
      C (L 1)*C (f (deposit D κ pt S))*coin real_:=by
  classical
  let P:=old_ (WilsonOlderFreshSoftFigures.stencil R D d B_ κ pt)
  have vk:=vc.trans ck
  have grade:h_=∑i:S,((R.family.labels.level (d i)).grades (B_ i)).2:=by rw [WilsonOriginalPublicNodalTestedChronology.rank,accounts];rfl
  have restricted:(fun i:S=>B_ i)=b:=funext (fun i=>dif_pos i.property)
  have selected (t:(i:S)→(R.family.labels.level (d i)).Index):
      packet R d S w_ N per K t=if t=b then 1 else 0:=by
    rw [WilsonIndependentConditionedFolioPoles.publication R d B_ N per K kn S t,restricted]
  have rawAgreement: (L 1) • P=∑q:Selection R d S,L (ticket R d S w_ N per K q) • H_ q:=by
    have entered:=WilsonOlderFreshSoftSocketHeard.original R d κ pt simple ratio L N per K c v track S w_ vc ck kn y f
    change (∑t:(i:S)→(R.family.labels.level (d i)).Index,L (packet R d S w_ N per K t) •
      old_ (WilsonOlderFreshSoftFigures.stencil R D d (seats R d S t) κ pt)) =
      ∑q:Selection R d S,L (ticket R d S w_ N per K q) • H_ q at entered
    rw [←entered,Finset.sum_eq_single_of_mem b (Finset.mem_univ _)]
    · rw [selected,if_pos rfl]
    · intro t _ other
      rw [selected,if_neg other,map_zero,zero_smul]
  have released:=WilsonOriginalPublicNodalTestedProbe.original R W D d B_ κ pt cut A_ O_ simple ratio N track v c K vc ck kn y S f
  have issued:coin P=C (f (deposit D κ pt S))*toll_*coin real_:=by
    change coin (cruises A_ O_ N (mass d S) c v
      (WilsonOlderFreshSoftOrdinary.material D d A_ O_ (WilsonOlderFreshSoftFigures.stencil R D d B_ κ pt) N track c K y S f))=_
    rw [released.1]
    change WilsonOlderFreshSoftSocketKinetic.reading (affix (clock A_ O_ N K v (charge R D d B_ κ pt S f)) real_.2) _=_
    rw [valued,WilsonOriginalPublicNodalTestedProbe.valuation R D d B_ κ pt,
      WilsonOriginalPublicNodalTestedRelease.motion A_ O_ N K v vk,
      WilsonOriginalPublicNodalTestedRelease.scalar A_ O_ N K v vk]
    rfl
  have ledger:C (L 1)*coin P = ∑q:Selection R d S,C (L (ticket R d S w_ N per K q))*coin (H_ q):=by
    have paid:=congrArg (meter (G:=G)) rawAgreement
    simpa only [map_sum,map_smul,scalar,meter,LinearMap.coe_mk,AddHom.coe_mk] using paid
  apply mul_left_cancel₀ (nonzero A_ O_ simple ratio N K v h_ vk kn)
  calc
    _=∑q:Selection R d S,C (L (ticket R d S w_ N per K q))*coin (H_ q):=by
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      by_cases same:degree R d S (fill R d S q)=h_
      · have arrived:=
          (WilsonOlderFreshSoftSocketRestored.received R d κ pt simple ratio N K c v track S vc ck kn y f (fill R d S q)).2.2
        rw [arrived,same,WilsonOlderFreshSoftSocketKinetic.pole A_ O_ N K v h_ vk]
        ring
      · have absent:degree R d S (fill R d S q)≠∑i:S,((R.family.labels.level (d i)).grades (B_ i)).2:=by rwa [←grade]
        rw [(WilsonIndependentConditionedFolioPoles.marked R d B_ N per K S q absent).2,map_zero,map_zero,zero_mul,zero_mul,mul_zero]
    _=toll_*(C (L 1)*C (f (deposit D κ pt S))*coin real_):=by rw [←ledger,issued];ring

end YM.Integration.WilsonIndependentConditionedFolioCoin
end
