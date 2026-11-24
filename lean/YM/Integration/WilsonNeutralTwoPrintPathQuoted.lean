import YM.Integration.WilsonNeutralTwoPrintPathRead
import YM.Integration.PeriodicMarkedWinding

/-! The issued inherited group word against the independently prescribed finite
output on its actual input. The marked constant is the rank-zero summand. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathQuoted
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
variable {G:Gauge}{n e j:ℕ}{k D:Fin n → ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
variable (R:Run G)(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor ≤ j)(enrolled:Paid R Y lo D k δ σ)
variable (N:ℕ) (c:Fin n)(X:Input Y lo S k D A)(included:J⊆S)(pin:c∈J)(positive:0 ≤ A)
variable (older:j<N)(deep:0 < mass k J)(sw:0 ≤ σ)(o:Cover)(t:Case D)(u:Frill J c)
local notation "M₀" => R.family.path.levels.clock.hatBeta j^δ*A^J.card

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
local notation "T" => WilsonOlderFreshConnectedBirth.issued R Y lo enrolled N c X included pin positive older deep sw o t u
local notation "P₀" => packetH J (output X J N) (mass k J) (e+1) c o u

open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead
local notation "deposit" => output X J N (toe J c o u)
local notation "report" => relative Y lo N c X o t u

def finite {n':Side}(h:ℕ):Gen ℝ (Woods G n'):=fun r v=>
  (touch t J) ((deposit).1 n' h r (jog (wrap n' o) ∘ v))

def bill {n':Side}(r:ℕ)(ν cash:ℝ)(x:Fin r→Woods G n'):ℝ:=
  ‖touch t J‖*((priceM (Hooks G) r ν+tiePay (Hooks G) r (ν/4)+1)*cash+cash)*
    catchW (ν/32/16) n'*Real.exp (-(ν/32/2)*Syn (tor n') (wrap n' ∘ toe J c o u) J (jog (wrap n' o) ∘ x))

include pin in
theorem coefficient {n':Side}(h r:ℕ){ν cash:ℝ}(hs:0<ν)(room:4*crestCard (toe J c o u) J<n'.val)
    (paid:MarkU (toe J c o u) J ((deposit).1 n' h r) ((deposit).2 h r) ν cash)(z:Fin r→Woods G n'):
    |(report h r z)-finite Y lo N c X o t u h r z|≤bill (G:=G) c o t u r ν cash z:=by
  let f:=touch t J
  let v:=jog (wrap n' o) ∘ z
  have charged:=(markOrbit paid ⟨c,pin⟩ room hs).2 v
  change |f _-f _|≤_
  rw [←map_sub,←Real.norm_eq_abs]
  exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left charged (norm_nonneg f)).trans_eq (by
    dsimp only [bill,f,v];ring))

theorem original {n':Side}{pp:Passport n' Unit}{marks:Marker.Census Unit}(site:Binder pp marks)
    (centered:site.center=0)(actors:Unit→Set ℂ)(bounded:∀x,‖value actors x‖≤1)(x:Affinity.Wallet actors)
    (width:0<σ)(closed:Cloze D k Y Credit.leanC)(tickets:Insure n (mass k univ) Y Credit.leanC)
    (layout:Layout G)(tape:Finset Age)(h:ℕ)(through:h≤e)(B:Link G n')
    {ν cash:ℝ}(hs:0<ν)(room:4*crestCard (toe J c o u) J<n'.val)
    (paid:∀r,MarkU (toe J c o u) J ((deposit).1 n' h r) ((deposit).2 h r) ν cash):
    let form:Gen ℝ (Woods G n'):=report h
    let raw:Gen ℝ (Woods G n'):=finite Y lo N c X o t u h
    (peek dvd_rfl ((T).rows site actors) (fun _=>mass k J) layout tape x h B).part (WilsonNeutralRenderedColumn.submitted site).val-
      value actors x*Complex.ofReal (diagonal (mass k J+h) raw B)=
      value actors x*Complex.ofReal (diagonal (mass k J+h) form B-diagonal (mass k J+h) raw B) ∧
    ∀r (w:(Fin r→Woods G n')→ℝ),
      |∑z,w z*(form r z-raw r z)|≤∑z,|w z| * bill (G:=G) c o t u r ν cash z:=by
  intro form raw
  constructor
  · rw [WilsonNeutralTwoPrintPathRead.original R Y lo enrolled N c X included pin positive older deep sw o t u
      site centered actors bounded x width closed tickets layout tape h through B]
    push_cast
    ring
  · intro r w
    change ‖∑z,w z*(form r z-raw r z)‖≤_ 
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _=>?_ )
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left
      (coefficient Y lo N c X pin o t u h r hs room (paid r) z) (abs_nonneg _)

end YM.Integration.WilsonNeutralTwoPrintPathQuoted
end
