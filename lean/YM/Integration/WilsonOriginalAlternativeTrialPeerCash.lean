import YM.Integration.WilsonOriginalMicroscopicEntranceHeldOwnerCoupon
import YM.Integration.WilsonMeasuredPublicEntranceTrialPeerOnset
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialPeerCash
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Source Labels WilsonOriginalAlternativeHearing WilsonMeasuredCoefficientTransport
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

open Ac Push.AbsoluteSums PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFieldRange
open WilsonMeasuredPublicEntranceCropClock
local notation "C₀" => R.family

def clock (d:V→ℕ)(n t p:ℕ)(ceiling gap:ℝ):ℝ:=
  gap+2*capital n p t (WilsonMeasuredPublicEntranceTrialPeerOnset.wide d t ceiling)+1

omit [DecidableEq V] in
private theorem clock_nonneg (d:V→ℕ)(n t p:ℕ){ceiling gap:ℝ}(cp:0 ≤ ceiling)(gp:0 ≤ gap):
    0 ≤ clock d n t p ceiling gap:=by
  have large:0 ≤ WilsonMeasuredPublicEntranceTrialPeerOnset.wide d t ceiling:=cp.trans (le_max_left ..)
  unfold clock capital limit
  positivity

include simple in
/-- The crop uses only the genuine P-side coefficient salaries. The full h and
the alternative uncut regular leaves remain on the original received course. -/
theorem original (d:V→ℕ)(n t p:ℕ)(np:0<n)(many:Fintype.card V ≤ n)
    (pace:WilsonWindowReportingPace.Slow R.kit)(book:WilsonReportLampForecast.Ready (C₀).path.levels)
    (ceiling gap e:ℝ)(cp:0 ≤ ceiling)(gp:0 ≤ gap)(ep:0<e):
    ∃start:ℕ,∀ᶠ k:ℕ in atTop,∀ (N per m school b:ℕ),let f:=k+1
    ∀(_cut:f ≤ N)(bt:b ≤ f),start ≤ b → m ≤ b →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per school Ψ → TicketP R.alloy R.kit D Q →
    ((C₀).path.levels.params f).supportExponent=100 →
    ∀(o:V→Site (R.family.side f per))(q:∀i,Coefficient (R.family.labels.level (d i)) (R.family.side f per))
      (w B:V→ℝ)(X I:Type) [Countable I] (Y:Lamps X I G (Ψ f).p o marks)(x:X)(trial:Finset V),
    let P:=R.family.path.rep N per f
    let raw:=WilsonMeasuredPublicEntranceTrialPeerBoard.field (N:=N) R marks d o (Ψ f) q Y x trial
    (∀v,0<w v ∧ w v ≤ 1) → (∀v,0 ≤ B v) → (∀v,(C₀).ref (d v) ≤ f) →
    (∀v,(q v).Format (o v) (C₀).params P) → (∀v,(q v).remBound (o v) P (κ f) (B v)) →
    (∀v,WilsonSeparatedPrefixCanonicalMounted.salary R d f per q B v ≤ (H f)^t) →
    (∀v,(w v)⁻¹ ≤ Real.exp (ceiling*span (H f))) → Y.Paid w (Ψ f).p.B ((Ψ f).p.supportExponent+2) 1 →
    ((f-b:ℕ):ℝ) ≤ gap*(1+Real.log (H f))^4 →
    ∀(v:V)(s:marks.Mode),v∈s.val →
    ∀(h:Coefficient (R.family.labels.level (d v)) (R.family.side f per)) {M:ℝ},
    h.Format (o v) R.family.params (Ψ f) → h.remBound (o v) (Ψ f) (κ f) M → h.x=0 → h.regular=0 →
    (∀Z,‖h.density (o v) (R.family.localSection (d v)) (Ψ f) Z/((Ψ f).eval Z:ℂ)‖ ≤ Real.exp (ceiling*span (H f))) →
    2*(w v*M) ≤ Real.exp 1 →
    ∀ Z:Config G (R.family.side b per),flags (Ψ b).p.threshold Z=∅ →
    ‖held R.family N per (fun U=>account h (Ψ f) U * ∏j∈s.val.erase v,raw j U) bt Z‖ ≤
      ((H f)^p)⁻¹ + (e*(regulatorRun R.family N per f)^p)*(shards marks s).card:=by
  have modes(s:marks.Mode):s.val.card ≤ n:=by exact (show s.val.card ≤ Fintype.card V by simpa using s.val.card_le_univ).trans many
  obtain ⟨start,heard⟩:=WilsonOriginalMicroscopicEntranceHeldOwnerCoupon.original R simple marks n 4 0 p np modes
    (clock d n t p ceiling gap) e (clock_nonneg d n t p cp gp) ep
  obtain ⟨startFee,fees⟩:=eventually_atTop.mp (WilsonMeasuredPublicEntranceTrialPeerOnset.original R d simple pace book
    n t p many ceiling cp)
  refine ⟨start,?_⟩
  filter_upwards [heard,eventually_ge_atTop startFee] with k listen settled
  intro N per m school b f cut bt after mb way D Q π Γ Ψ course ticket placed o q w B X I ci Y x trial P raw
    wp bp refs fit remn salaries widths paid time owner s present h M fmt fare x0 empty observed tested Z clear
  let c':=WilsonMeasuredPublicEntranceTrialPeerOnset.wide d t ceiling
  let U:=c'*span (H f)
  let Vmax:=fee n p t c' (H f)
  have mf:=mb.trans bt
  obtain ⟨restored,up,big,spent,charge,period⟩:=fees f (settled.trans (Nat.le_succ k)) N per m school mf cut
    π Γ Ψ course placed o q B w trial bp wp salaries widths
  have target:(Ψ f).p=P.p:=(WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course mf cut).1.symm
  have exponent:(Ψ f).p.supportExponent=100:=by rw [(course.1.walk f mf cut).truep.point];exact placed
  have room:1 ≤ P.p.supportExponent:=by rw [←target,exponent];norm_num
  exact listen N per m school b cut bt after mb way D Q π Γ Ψ course ticket d o q w B X I Y x trial 1 U Vmax
    (fun j=>(wp j).1) bp refs fit remn room target paid up (zero_le_one.trans big) (fun j=>(spent j).1)
    (fun j=>(spent j).2.1) (fun j=>(spent j).2.2) charge (period b gap time) owner s present (d owner) h
    fmt fare x0 empty observed (tested.trans (Real.exp_le_exp.mpr big)) (Real.exp_le_exp.mpr restored) Z clear

end YM.Integration.WilsonOriginalAlternativeTrialPeerCash
end
