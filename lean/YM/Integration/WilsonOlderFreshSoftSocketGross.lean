import YM.Integration.WilsonOlderFreshSoftSocketTotal
import YM.Integration.WilsonOlderFreshSoftOrdinary
import YM.Integration.WilsonIndependentCollarPointBill
import YM.Integration.WilsonIndependentCollarSeedTariff

/-! The full scalar coefficient mass of the authentic normalized q at the original moving stop, before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketGross
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftOrdinary (material)
open WilsonOlderFreshSoftSocketRestored (stopped coin)
open WilsonIndependentCollarOrdinaryWeak (price)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonCoeffUV.Winding
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(D d:I→ℕ)(p:ℕ)

def seed:ℝ:=(WilsonIndependentCollarSeedTariff.original G D d p).choose*
    (WilsonIndependentCollarPointBill.original R D d p (w:=1) zero_lt_one).choose
def gross (S:Finset I)(A B:ℝ):ℝ:=((p+1:ℕ):ℝ)*((price G (mass d S) p).buy B*
    ((price G (mass d S) p).buy A*(seed R D d p)^S.card))

omit [Fintype I] in
private theorem ward (S:Finset I)(L:Levels G)(O:ChartRatio G)(draw:L=R.family.path.levels)(paid:O=R.metals.O)
    (N K c v:ℕ)(cells:Digits L I)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)(Y:Outerm G D):
    cruises L O N (mass d S) c v (material D d L O Y N cells c K y S f)=
    stopped R d N K c v (cast (congrArg (fun l=>Digits l I) draw) cells) y S f Y:=by subst L O;rfl

theorem original (S:Finset I)(occupied:S.Nonempty)(V:Realm G (p+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
    (dorm:Dormitory V (mass d S) 0 Credit.leanC)(N K c v:ℕ)(first:V.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)
    (A B:ℝ)(front:PadRank V c K A)(march:PadRank V v c B)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:(i:I)→Choice R d i)
    (cells:Digits V.draws I)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)(fn:‖f‖≤1):
    let P:=stopped R d N K c v (cast (congrArg (fun l=>Digits l I) draw) cells) y S f (start R d κ pt q)
    WilsonReportingAbsoluteInletForecastBooks.mass p (coin P)≤gross R D d p S A B:=by
  classical
  let Y:=start R d κ pt q
  let b:=(WilsonIndependentCollarPointBill.original R D d p (w:=1) zero_lt_one).choose
  obtain ⟨one,bank⟩:=(WilsonIndependentCollarPointBill.original R D d p (w:=1) zero_lt_one).choose_spec
  obtain ⟨law,roots⟩:=bank κ pt q
  obtain ⟨sOne,entry⟩:=(WilsonIndependentCollarSeedTariff.original G D d p).choose_spec
  have wage:0≤ seed R D d p:=mul_nonneg (zero_le_one.trans sOne) (zero_le_one.trans one)
  have vacuum:=entry Y law b (zero_le_one.trans one) roots
    (address V.draws cells (K-c) c y) S occupied f fn
  let Z:=material D d V.draws V.paid Y N cells c K y S f
  let J:=(price G (mass d S) p).buy A*(seed R D d p)^S.card
  have same:c+(K-c)=K:=by omega
  have cut:c+(K-c)≤N:=by omega
  have auth:Auth (mass d S) Z:=(placedO _ ((sound V.draws V.paid d N cells V.hG V.green _ law
    (K-c) c cut).level' y) S).tuft f
  have Z0:0≤J:=mul_nonneg (zero_le_one.trans (Credit.purchase _
    (front.pos (oldGuard (first.trans vc) ck)))) (pow_nonneg wage _)
  have initial:Saturation p 0 0 Z.2 0 J:=by
    intro i ie r _
    have cash:=WilsonIndependentCollarOrdinaryWeak.scalar V N cells Y law S (K-c) c y (first.trans vc) cut
      A ((seed R D d p)^S.card) (same.symm ▸ front) (pow_nonneg wage _) dorm f vacuum i r ie
    simpa only [Z,material,J,Shard.Fruit,Shard.Award,hedge,autumn,pow_zero] using cash
  let walk:Escort V v c (fun _=>0):=⟨first,vc,by intros;norm_num,by intros;norm_num,by intro i _ _;simp [thinLevel]⟩
  let H:=cruises V.draws V.paid N (mass d S) c v Z
  have per (i:ℕ)(ie:i≤p):|H.2 i 0 Fin.elim0|≤(price G (mass d S) p).buy B*J:=by
    have cash:=(bulkCert G (mass d S) p 0 Credit.leanC Credit.leanC).choose_spec i ie 0 V dorm v c _ N B
      walk march (ck.trans live) Z J auth Z0 initial
    have line:=cash.2.1.sum_le_tsum ({Fin.elim0}:Finset (dock Cover _ 0)) (fun a _=>cash.1 a)
    rw [sum_singleton] at line
    simpa only [hedge,autumn,pow_zero,one_mul,Real.norm_eq_abs] using line.trans cash.2.2
  dsimp only
  rw [←ward R D d S V.draws V.paid draw paid N K c v cells y f Y]
  simp only [WilsonReportingAbsoluteInletForecastBooks.mass,coin,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
  change (∑i∈range (p+1),|H.2 i 0 Fin.elim0|)≤_
  calc _≤∑_i∈range (p+1),(price G (mass d S) p).buy B*J:=sum_le_sum fun i hi=>per i (by have h:=mem_range.mp hi;omega)
       _=_:=by simp [gross,J]

end YM.Integration.WilsonOlderFreshSoftSocketGross
end
