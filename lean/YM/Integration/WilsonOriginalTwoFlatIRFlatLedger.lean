import YM.Integration.WilsonOriginalTwoFlatIRFlatCopy
import YM.Integration.WilsonOriginalCensusDatedMaterial

/-! The zero angular component of each actual dated physical print is its
prescribed cover scalar. The independent old vacuum, source tensor, chosen
lift and all earlier deposits are those of the printed material. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatLedger

open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathJet (diagonal)

open WilsonGeneralArityCopyAccount WilsonOriginalCensusDatedMaterial WilsonCoeffUV.Blue
open Primitives.TwoWave AllOrder.Haiku Stationary

private theorem atom_at {G:Gauge}{side:Side}{r:ℕ}(A:Atom G r)(o o':Site side):
    A.unmasked (1:Config G side) o=A.unmasked 1 o':=by
  have legs (s:RG.Slot)(y:Site side):s.atSite (1:Config G side) y=0:=by
    rw [Work.F03.atSite_path, show faceValue (1:Config G side) _=1 by simp [faceValue,Lattice.square],
      G.curvature_unit,map_zero]
  simp only [Atom.unmasked,Atom.poly,legs]

theorem group_at {G:Gauge}{side:Side}{d q:ℕ}{σ:ℝ}(T:Copy G d q σ)(o o':Site side)(g:ℝ):
    ∑'a:T.Roster,term T o g (1:Config G side) a=∑'a:T.Roster,term T o' g 1 a:=by
  apply tsum_congr
  intro a
  simp only [term,atom_at _ o o']

theorem scalar {U:Type}[Fintype U](cap:ℕ)(T:Gen ℝ U):
    diagonal cap T (0:Lawn U)=T 0 Fin.elim0:=by
  unfold diagonal
  rw [sum_eq_single (0:ℕ)]
  · rw [Blue.toll,Finset.sum_eq_single (Fin.elim0:Fin 0→U)]
    · simp
    · intro u _ h
      exact (h (Subsingleton.elim u Fin.elim0)).elim
    · intro absent; exact (absent (Finset.mem_univ _)).elim
  · intro r _ other
    rw [Blue.toll]
    apply Finset.sum_eq_zero
    intro a _
    have rr:0<r:=Nat.pos_of_ne_zero other
    rw [Finset.prod_eq_zero (Finset.mem_univ (⟨0,rr⟩:Fin r)) (by rfl),mul_zero]
  · simp

theorem folded_unit {V P:Type}[NormedAddCommGroup V](F:Ten V (Cloth P) 0)(side:Side)
    (a:Fin 0→Site side×P):
    Carp.plume F side a=F Fin.elim0:=by
  have all (x:Fin 0 → Lattice.Cover × P):Carp.peglet F side a x=F Fin.elim0:=by
    unfold Carp.peglet
    rw [if_pos (Subsingleton.elim _ _),Subsingleton.elim x (Fin.elim0:_)]
  unfold Carp.plume
  rw [tsum_eq_single (Fin.elim0:Fin 0→Lattice.Cover × P) (fun x diff=>(diff (Subsingleton.elim x Fin.elim0)).elim)]
  exact all _

variable {G:Gauge}{n:ℕ}{R:Run G}{N i q:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}{B:I → Binder P (Stock.census (Fin n))}
  (H:Material R N i q k σ B)(z:I)

def occupied (e:ℕ):ℝ:=
  WilsonCoeffUV.Wheel.touch (H.source z) (B z).mode.val
    ((FundedMarkedPathSelection.output H.prior (B z).mode.val N
      (toe (B z).mode.val (H.pin z) (H.root z) (H.frill z))).2 e 0 Fin.elim0)

theorem original (g:ℝ):
    ∑'a:(words H z).Roster,term (words H z) (B z).center g (1:Config G side) a=
      Complex.ofReal (∑e:Fin (q+1),g^e.val*occupied H z e):=by
  rw [group_at _ _ (0:Site side),WilsonOriginalTwoFlatIRFlatCopy.original _ H.radius _ _
    (charts H z) (matched H z)]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  rw [matched H z e (by omega)]
  have same:=WilsonNeutralTwoPrintPathRead.register R H.realm H.start H.paid N (H.pin z)
    H.prior (H.included z) (H.marked z) H.nonneg H.lower (H.positive z) H.radius.le (H.root z)
    (H.source z) (H.frill z) H.radius H.closed H.tickets e (by omega) (0:Stationary.Link G side)
  refine same.trans ?_
  rw [scalar]
  unfold WilsonNeutralTwoPrintPathRead.relative occupied
  rw [folded_unit]

end YM.Integration.WilsonOriginalTwoFlatIRFlatLedger
end
