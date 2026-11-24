import YM.Integration.WilsonCapturedPrimaryWeakTrialCopyScalar
import YM.Integration.WilsonNeutralTwoPrintPathRoll
import YM.Integration.WilsonOlderFreshConnectedGross

/-! Fieldwise summation of the physical connected copy with the original
thermal powers, including the scalar and every coloured path. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialConnectedScalar
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


open WilsonCapturedPrimaryWeakTrialCopyScalar WilsonNeutralTwoPrintPathRoll
local notation "pt₀" => WilsonNeutralTwoPrintPathRoll.locate R Y lo enrolled N c X included pin positive older deep sw o t u

def number {n' : Side} (site : Site n') (g : ℝ) (U : Config G n') : ℂ :=
  ∑ a : Fin (e+1), ∑ r : Fin (mass k J+a.val+1), (g:ℂ)^((a.val:ℤ)-r.val) *
    (∑' z : RadP G r.val, ((Rolls.dip (P₀ a.val r z) (touch t J)).unmasked U site : ℂ))

theorem thermal {n' : Side} (a : Fin (e+1)) (site : Site n') (g : ℝ) (U : Config G n') :
    (∑' v : ((T).roll a).Ty, loan (T) site g U a v) =
      ∑ r : Fin (mass k J+a.val+1), (g:ℂ)^((a.val:ℤ)-r.val) *
        (∑' z : RadP G r.val, ((Rolls.dip (P₀ a.val r z) (touch t J)).unmasked U site : ℂ)) := by
  let f := loan (T) site g U a
  have fromRoll := (entire (T) site g U sw a).1.hasSum
  have ordered := (pt₀ a).hasSum_iff.mpr fromRoll
  have sums : Summable (fun v => f (pt₀ a v)) := ordered.summable
  rw [←ordered.tsum_eq]
  change (∑' v : Labels (G:=G) (k:=k) (J:=J) a, f (pt₀ a v)) = _
  rw [sums.tsum_sigma,tsum_fintype]
  refine sum_congr rfl fun r _ => ?_
  rw [(sums.sigma_factor r).tsum_sigma,←tsum_mul_left]
  apply tsum_congr
  intro z
  rw [tsum_fintype]
  have height (b:Stationary.Ink G r.val) : (((T).roll a).leg (pt₀ a ⟨r,z,b⟩)).r = r.val := rfl
  simp only [f,loan,height,Complex.ofReal_mul,Complex.ofReal_zpow,←Finset.mul_sum,←Complex.ofReal_sum]
  have filed := WilsonOlderFreshConnectedBirth.heard R Y lo enrolled N c X included pin positive older deep sw o t u
    a.val (Nat.le_of_lt_succ a.isLt) r z U site
  rw [show (∑ b:Stationary.Ink G r.val, (((T).roll a).leg (pt₀ a ⟨r,z,b⟩)).atom.unmasked U site) =
       (Rolls.dip (P₀ a.val r z) (touch t J)).unmasked U site from filed]

theorem original {n' : Side} (place : Site n') (actors : Unit → Set ℂ) (x : Wallet actors)
    (g : ℝ) (U : Config G n') :
    WilsonOlderFreshLocatedBook.word (T) place actors x g U =
      value actors x * number Y lo N c X o t u place g U := by
  rw [WilsonCapturedPrimaryWeakTrialCopyScalar.original (T) place g U actors x sw]
  exact congrArg (fun z => value actors x*z) (sum_congr rfl fun a _ =>
    thermal R Y lo enrolled N c X included pin positive older deep sw o t u a place g U)

include enrolled included pin positive older deep sw in
theorem priced {n' : Side} (place : Site n') (actors : Unit → Set ℂ) (x : Wallet actors)
    {g : ℝ} (pos : 0 < g) (small : g ≤ 1) (U : Config G n') :
    ‖value actors x * number Y lo N c X o t u place g U‖ ≤
      (‖value actors x‖ * WilsonOlderFreshConnectedGross.tariff (mass k J) e g) *
        ((e+1:ℕ) * ((mass k J+e+1:ℕ)*((∏v∈J,‖t v‖)*M₀))) := by
  rw [←original R Y lo enrolled N c X included pin positive older deep sw o t u place actors x g U]
  exact (WilsonOlderFreshConnectedGross.original R Y lo enrolled N c X included pin positive older deep sw o t u
    place actors x pos small U).2 ((Stock.census Unit).fire ())

end YM.Integration.WilsonCapturedPrimaryWeakTrialConnectedScalar
