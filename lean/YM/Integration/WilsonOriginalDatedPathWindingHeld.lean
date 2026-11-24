import YM.Integration.WilsonNeutralTwoPrintPathDatedWage

/-! The actual dated winding on a bounded real direction, with the rank-zero term. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalDatedPathWindingHeld
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

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)
variable {G:Gauge}{n:ℕ}{k D:Fin n→ℕ}(R:Run G)(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)

open WilsonNeutralTwoPrintPathBooked (route)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathRankFare (tariff)


open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram
variable {n':Side}{I:Type}[Fintype I]{P:Passport n' (Fin n)}
  (B:I→Binder P (Stock.census (Fin n)))(x:Affinity.Wallet (room (Fin n)))
  (N b j e:ℕ)(cells:Digits R.family.path.levels (Fin n))(q:(v:Fin n)→Choice R k v)
  (c:I→Fin n)(o:I → Cover)(t:I → Case D)(u:∀i,Frill (B i).mode.val (c i))
local notation "J" i:max => (B i).mode.val
local notation "y" i:max => toe (J i) (c i) (o i) (u i)
local notation "old" => fixed R k κ pt N b (j+1) cells q
local notation "target" i:max => fixed R k κ pt N b j cells q (y i) (J i)
local notation "weight" i:max => ∏v∈(B i).mode.val,(x v).val
local notation "cut" i:max h:max => mass k (J i)+h
local notation "σshift" i:max => jog (wrap n' (o i))

open WilsonNeutralTwoPrintPathDatedPolynomial (row entry)
local notation "A" => WilsonNeutralTwoPrintPathDatedPolynomial.row R κ pt B N b j e cells q c o u


open WilsonNeutralTwoPrintPathDatedWage (source)

theorem ranked {E:Type}[Fintype E](F:∀r:ℕ,(Fin r→E)→ℂ)(bound:ℕ)(Y:E→ℝ)(M:ℝ)
    (held:∀z,‖Y z‖≤M)(p:Bool):
    ‖MvPolynomial.eval Y (packed (fun r z=>phase p (F r z)) bound)‖ ≤
      ∑r∈range (bound+1),(∑z,‖F r z‖)*M^r:=by
  rw [WilsonNeutralTwoPrintPathPolynomial.rendered]
  refine (norm_sum_le _ _).trans (sum_le_sum fun r _=>?_ )
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun z _=>?_ )
  have scalar:‖phase p (F r z)‖≤‖F r z‖:=by
    have h:=(WilsonNeutralTwoPrintPeg.allowed p).dist_le_mul (F r z) 0
    simpa only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] using h
  have term:‖∏u,Y (z u)‖ ≤ M^r:=by
    refine (Finset.norm_prod_le _ _).trans ?_
    simpa using (prod_le_prod (s:=univ) (g:=fun _ : Fin r=>M)
      (fun u _=>norm_nonneg (Y (z u))) (fun u _=>held (z u)))
  rw [norm_mul]
  exact mul_le_mul scalar term (norm_nonneg _) (norm_nonneg _)

theorem paid (s:(Stock.census (Fin n)).Mode)(h:ℕ)(p:Bool)(Y:Link G n')(M:ℝ)
    (nn:0≤M)(held:∀z,‖Y z‖≤M)(ν C:I→ℕ→ℝ)(pins:∀i,c i∈(J i))
    (fit:∀i,4*crestCard (y i) (J i)<n'.val)
    (sale:∀i r,r≤cut i h →
       0<ν i r ∧ MarkU (y i) (J i) (spent R k N j e n' old (y i) (cells j) (J i) h r)
           ((target i).2 h r) (ν i r) (C i r)):
    ‖MvPolynomial.eval Y (entry R κ pt B x N b j e cells q c o t u s h p)‖ ≤
      ∑i,if s=(B i).mode then ∑r∈range ((cut i h)+1),
        ((‖weight i‖*‖touch (t i) (J i)‖)*(tariff (Loc G 1) r (ν i r) (C i r)*catchW (ν i r/512) n'))*M^r else 0:=by
  rw [WilsonNeutralTwoPrintPathDatedWage.named,map_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _=>?_ )
  by_cases key:s=(B i).mode
  · simp only [if_pos key]
    refine (ranked _ _ Y M held p).trans (sum_le_sum fun r hr=>?_ )
    have sk:=sale i r (Nat.le_of_lt_succ (mem_range.mp hr))
    exact mul_le_mul_of_nonneg_right
      (WilsonNeutralTwoPrintPathDatedWage.paid R κ pt B x N b j e cells q c o t u i h r
        (ν i r) (C i r) sk.1 (pins i) (fit i) sk.2) (pow_nonneg nn r)
  · simp [key]

end YM.Integration.WilsonOriginalDatedPathWindingHeld
end
