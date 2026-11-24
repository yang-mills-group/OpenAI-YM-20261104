import YM.Integration.WilsonThermometerCorridorFourFaces
import YM.Integration.WilsonThermometerCorridorCash
import YM.Integration.WilsonThermometerCorridorWalk
/- The cubic face and its three proper pairs on one true earlier filing, at
   the physical compact housing even when the observed pair omits the origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorQuote
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu MergeProof.Ribbons
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open MergeProof.Float
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open scoped Topology BigOperators Classical
 MergeProof.Ribbon Pressure
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput WilsonMixedTaggedPrice
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} {n:Side} {I J:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable (R:Run G)
local notation "A" => R.family.path.levels
local notation "FamilyR" => R.family
open MergeProof.Float
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open scoped Topology BigOperators Classical


open Trace.Physical.GermGraph WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFeed

open WilsonThermometerPepperFace

open RG05Readout.Pantry WilsonThermometerMixedBooked Planned.GuardedAtom Guard MergeProof.Ribbon PhysicalNext.Repeat.Mallow
local notation "V"=>Unit×Fin 3
local notation "β"=>(A).clock.hatBeta

theorem columns (simple:G.Simple):∀ᶠ j:ℕ in atTop,((A).params j).columns ≤ β j:=by
  obtain ⟨M,h⟩:=eventually_atTop.mp (WilsonThermometerOwnOffsetRadii.stage R simple 1 0)
  filter_upwards [eventually_ge_atTop (M+1)] with j late
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
  have bound:=h k (by omega)
  simp only [pow_one,pow_zero,mul_one] at bound
  exact (RG12.Commission.column_priced (A) k).trans bound

theorem original (simple:G.Simple)(cater:Cater R.family R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀ N p f (edge:j+1<N) (_:j+2≤f) (anchor:(V)) (l debt:ℕ),
    let top:=(FamilyR).path.rep N p (j+2)
    let middle:=(FamilyR).path.rep N p (j+1)
    let step:=(A).clock.op (j+1) p
    ∀ (raw:(V)→Three G ((FamilyR).side (j+2) p)) (down:(V)→Three G ((FamilyR).side (j+1) p))
      (o:(V)→Site ((FamilyR).side (j+2) p)) (w cost:(V)→ℝ) (F:Config G ((FamilyR).side (j+2) p)→Poly (Stock.census (V))),
    ∀ a:ℝ,MenuBoard top raw F o w a 1 → ((A).budget (j+2)).supportExponent-4 ≤ a →
    (∀i,0<w i ∧ w i≤1 ∧ (w i)⁻¹≤β f^debt) →
    (∀i,Ride step (o i) (step.ratio.parent (o i)) (R.doors N p (j+1) edge) 1 (raw i) (down i) (cost i)) →
    Occupancy o (apron (A) (j+1)) → Occupancy (step.ratio.parent ∘ o) (apron (A) (j+1)) →
    (∀i,2*w i*cost i≤1) →
    (∀i,coverNumber middle.p.B ({step.ratio.parent (o anchor),step.ratio.parent (o i)}:Support ((FamilyR).side (j+1) p))≤l) →
    ((A).clock.op j p).ratio.parent (step.ratio.parent (o anchor))=0 →
    ∀u:ℕ,(FamilyR).ref 0 ≤ u → ∀ uj:u≤j,Opened (FamilyR) 0 u p → Opened (FamilyR) 0 j p →
    let seen:=fun s:(Stock.census (V)).Mode=>reading R (N:=N) (p:=p) (((A).clock.op j p).push middle.beta
      (fun x=>(step.push top.beta F x).part s)) u uj
    let bill:=21168*β f^(5+3*(4+debt+6*l))
    ‖seen (whole (V))‖≤bill ∧ ∀i,‖seen (rest ((Stock.census (V)).fire i))‖≤bill:=by
  filter_upwards [WilsonThermometerCorridorFourFaces.original (I:=(V)) R simple cater bank wage,columns R simple]
    with j hear col N p f edge span v l debt
  dsimp only
  intro raw down o w cost F a old wide wallets rides load seated cap close home u ref uj ou oj
  let mid:=(FamilyR).path.rep N p (j+1)
  let η:=renal (A) (j+1)
  let hp:=β (j+2)
  let x:=β f
  have hx:1≤x:=((A).fits.delayed f).le
  have hnext:1≤hp:=((A).fits.delayed (j+2)).le
  have height:hp≤x:=Many.beta_le' (C:=(FamilyR)) simple span
  have hp0:0<hp:=zero_lt_one.trans_le hnext
  have eta:η=(hp^2)⁻¹:=by unfold η renal probe;rw [Real.rpow_neg hp0.le];norm_num
  have ep:0<η:=by rw [eta];positivity
  have es:η≤1:=by rw [eta];exact inv_le_one_of_one_le₀ (one_le_pow₀ hnext)
  have income:η⁻¹≤x^2:=by rw [eta,inv_inv];gcongr
  have posw:=fun i=>(wallets i).1
  have priced:=(WilsonThermometerMixedBooked.original R cater edge a raw down o w cost F old wide posw rides load seated cap).2 v
  have parms:mid.p=(A).budget (j+1):=(R.makes.wilson.represents N p (j+1) edge.le).vac
  have strip:Real.exp (mid.p.supportExponent+1/2)≤x^6:=by
    rw [parms]
    exact (WilsonThermometerCorridorCash.aperture hnext (posw v) ep es priced).trans (pow_le_pow_left₀ hp0.le height 6)
  have receipt:=WilsonThermometerCorridorCash.group mid v w l debt hx ep posw (fun i=>(wallets i).2.2) income strip
  have held:=hear N p edge v l raw down o w cost F a old wide posw rides load seated cap close home u ref uj ou oj
  have clock:β j≤x:=Many.beta_le' (C:=(FamilyR)) simple (show j≤f by omega)
  let gross:=(25+24*((A).params j).columns)*β j^4*(4*(1/WilsonThermometerWeakMixedGrouping.radius (atSite v) mid 3 l η (fun i=>η*w i) ()))
  have betaPos:0≤β j:=zero_le_one.trans ((A).fits.delayed j).le
  have feeNon:0≤1/WilsonThermometerWeakMixedGrouping.radius (atSite v) mid 3 l η (fun i=>η*w i) ():=by
    apply one_div_nonneg.mpr
    unfold WilsonThermometerWeakMixedGrouping.radius
    apply Finset.prod_nonneg
    intro i _
    dsimp only [MergeProof.Ribbons.Fibers.Salt.tow]
    have hi:=posw i
    positivity
  have cost: gross≤5292*x^(5+3*(4+debt+6*l)):=by
    have cols:25+24*((A).params j).columns≤49*x:=by linarith only [col.trans clock,hx]
    calc gross ≤ (49*x)*x^4*(4*(27*x^(3*(4+debt+6*l)))) := by
              dsimp only [gross]
              gcongr
         _ = _ := by rw [pow_add];ring
  change ‖_‖≤gross ∧ ∀i,‖_‖≤4*(η*w i)*gross at held
  have non:0≤x^(5+3*(4+debt+6*l)):=pow_nonneg (zero_le_one.trans hx) _
  constructor
  · exact held.1.trans (cost.trans (by linarith only [non]))
  · intro i
    have small:η*w i≤1:=(mul_le_mul es (wallets i).2.1 (posw i).le zero_le_one).trans_eq (one_mul 1)
    have feePos:0≤gross:=(norm_nonneg _).trans held.1
    exact (held.2 i).trans (by nlinarith only [cost,non,mul_nonneg feePos (sub_nonneg.mpr small)])
end YM.Integration.WilsonThermometerCorridorQuote
end
