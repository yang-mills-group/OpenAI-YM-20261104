import YM.Integration.WilsonPositionThermometerStationWallet
import YM.Integration.WilsonMeasuredPublicEntranceGridDebit
import YM.Integration.WilsonMatrixOriginalGermMarket

/-! The actual weak station's signed scalar and derivative coordinates in the public fitted
source, on its original cutoff and period, before the addressed finite inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFiledHead
open Filter Finset Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
  {D:ℕ}(V:Vane R.family D)(j:Fin (D+1))(w:(Bel R.family.book).Field j)

def vote (N p:ℕ):R.family.label j:=
  (((R.family.S.a V.k:ℂ)^j.val)⁻¹) • fitted R j V.k N p (V.wheel.atCut (N,p) j w)

def tagged (N p:ℕ):R.family.label j:=
  (R.family.labels.level j).scaled (shrink R.family V.k N p)⁻¹
    (weightTag R.family j (Next.Rank.Station.mag R.family.path.levels V.b V.k) (Further.CorrectedLift.ladder R.family j w))

def fee (k p:ℕ):ℝ:= invoice (C:=R.family) j k p*stock R.family k+Perch.bill (-1/2) (R.family.path.levels.clock.hatBeta k)

private theorem scalar (z:ℂ)(x:R.family.label j):(R.family.labels.level j).coeffSize (z • x)=‖z‖*(R.family.labels.level j).coeffSize x:=by
  simp [Frame.coeffSize,Finset.mul_sum,Pi.smul_apply]

private theorem triangle (x y:R.family.label j):(R.family.labels.level j).coeffSize (x+y)≤(R.family.labels.level j).coeffSize x+(R.family.labels.level j).coeffSize y:=by
  simpa [Frame.coeffSize,Finset.sum_add_distrib] using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>norm_add_le (x i) (y i))

theorem exact_calibration {N p:ℕ}(checked:V.checked f H D)(top:V.k<N):
    V.R N p j (V.wheel.atCut (N,p) j w)=tagged R V j w N p:=by
  let T:=V.R N p j
  let x:=V.wheel.atCut (N,p) j w
  let b:=Next.Rank.Station.mag R.family.path.levels V.b V.k
  let a:=shrink R.family V.k N p
  have leg:Tested R.family j V.k N p T:=((checked.rate N p top).1 j).1
  have paid:(R.family.labels.level j).scaled a (T x)=weightTag R.family j b (Further.CorrectedLift.ladder R.family j w):=
    poured R.makes (checked.early j) top.le b T leg _
  have pos:0<a:=shrink_pos R.family R.makes top.le p
  have restore:=(R.family.labels.level j).scaled_inv (inv_ne_zero pos.ne') (T x)
  rw [inv_inv,paid] at restore
  exact restore.symm

theorem original {N p:ℕ}(checked:V.checked f H D)(top:V.k<N):
    (R.family.labels.level j).coeffSize (vote R V j w N p-tagged R V j w N p)≤
      fee R j V.k p*(2*(R.family.labels.level j).coeffSize (tagged R V j w N p)):=by
  let Y:=V.wheel.atCut (N,p) j w
  let q:=(R.family.factory j N p).entries V.k ((R.family.factory j N p).terminal.symm Y)
  let g:ℂ:=((R.family.S.a V.k:ℂ)^j.val)⁻¹
  let z:=awake R.family j V.k N p Y
  let T:=V.R N p j
  have leg:Tested R.family j V.k N p T:=((checked.rate N p top).1 j).1
  have exactHead:T Y=tagged R V j w N p:=exact_calibration R V j w checked top
  have rate:(R.family.labels.level j).coeffSize (z-T Y)≤Perch.bill (-1/2) (R.family.path.levels.clock.hatBeta V.k)*(R.family.labels.level j).coeffSize z:=
    (checked.rate N p top).2 j Y
  have cash:(R.family.labels.level j).coeffSize z ≤2*(R.family.labels.level j).coeffSize (T Y):=leg.cost _ _ _
  have change:(R.family.labels.level j).coeffSize (page (C:=R.family) j p V.k q-q.x) ≤ invoice (C:=R.family) j V.k p*(stock R.family V.k*(R.family.labels.level j).coeffSize q.x):=
    measured_diff j N p V.k R.makes (checked.early j) top.le
      (entryOk j N p V.k R.makes (checked.early j) top.le ((R.family.factory j N p).terminal.symm Y))
  have raw:(R.family.labels.level j).coeffSize (vote R V j w N p-z)≤(invoice (C:=R.family) j V.k p*stock R.family V.k)*(R.family.labels.level j).coeffSize z:=by
    change (R.family.labels.level j).coeffSize (g • page (C:=R.family) j p V.k q-g • q.x) ≤ _*(R.family.labels.level j).coeffSize (g • q.x)
    rw [←smul_sub,scalar R j,scalar R j]
    exact (mul_le_mul_of_nonneg_left change (norm_nonneg g)).trans_eq (by ring)
  have nonnegative:0≤fee R j V.k p:=by
    exact add_nonneg (mul_nonneg (invoice_nn (C:=R.family) j p _) ((stage R.family _).columns_ge.trans' zero_le_one)) (Real.exp_pos _).le
  rw [←exactHead]
  calc
    _=(R.family.labels.level j).coeffSize ((vote R V j w N p-z)+(z-T Y)):=by congr 1;abel
    _≤_ :=triangle R j _ _
    _≤fee R j V.k p*(R.family.labels.level j).coeffSize z:=(add_le_add raw rate).trans_eq (by unfold fee;ring)
    _≤_:=mul_le_mul_of_nonneg_left cash nonnegative

end YM.Integration.WilsonPhysicalStationFiledHead
