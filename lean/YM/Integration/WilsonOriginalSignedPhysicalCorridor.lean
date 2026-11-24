import YM.Integration.WilsonOriginalMountedRegular
import YM.Integration.WilsonOriginalOccupiedModeTrial

/-! Complete signed ordinary telescope at the original fixed flat or clear physical decoder. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedPhysicalCorridor
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open Source Labels
open Pert.Asymptotics WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

include simple in
theorem original (n d a p:ℕ)(np:0<n)(load:∀s:marks.Mode,s.val.card ≤ n)(C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀(b N per m k L:ℕ),start ≤ b → m ≤ b+1 → ∀(live:b+1+L ≤ N),
    (∀j:Fin L,(j.val:ℝ) ≤ C*(1+Real.log (H (b+j.val+1)))^d) →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(physical:Config G (R.family.side N per)→Poly marks),
    Integrable physical (prior G _) →
    ∀(trial:∀j,Config G (R.family.side j per)→Poly marks),
    (∀i,b+1 ≤ i → i ≤ b+1+L → Integrable (trial i) (prior G _)) →
    ∀(P:∀j:Fin L,Slice R marks (Ψ (b+j.val+1))),
    (∀j:Fin L,(P j).A.density (P j).x=LocalComparison.actualPush R.family N per (b+j.val+1) (trial (b+j.val+1+1))) →
    ∀(s:marks.Mode)(S:Fin L → V → ℝ),(∀j v,0 < S j v) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (P j).regular (P j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*(Poly.toll (S j) s*Poly.toll (P j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),flags (Ψ (b+1)).p.threshold W=∅ →
    ∀{d₀:ℕ}{frame:Frame G d₀}(section_:SectionData frame)(group:Hol G)
    (F:∀j:Fin L,WilsonOriginalMountedRegular.Filing R (Ψ (b+j.val+1)) (P j) (trial (b+j.val+1)) s),
    let enter:=read R N per W (show b+1 ≤ b+1+L by omega)
      (gust R.family.path N per N physical (b+1+L) live-trial (b+1+L)) s
    let spring:=WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op (b+1) per)
      (R.family.path.β N per (b+1+1)) W
    let regular:=∑j:Fin L,(F j).bill (b+1) e (R.alloy.B.a.clock.hatBeta (b+j.val+1)) spring p
    ‖read R N per W (show b+1 ≤ N by omega) physical s-
      (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(trial (b+1) W).part s‖ ≤
      ‖enter‖+regular+((e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card)*
        ∑j:Fin L,Poly.toll (S j) s/WilsonOriginalOccupiedDateShare.weight j.val:=by
  obtain ⟨h,hard⟩:=WilsonOriginalOccupiedModeTrial.original R simple marks n d a p np load C e cp ep
  let kin:=(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p ep)).choose
  refine ⟨max (max h kin) (max (WilsonSingleHardRadius.first R simple) (WilsonCenteredCaptureClock.first R simple)),?_⟩
  intro b N per m k L age mb live span way D Q π Γ Ψ course ticket physical hp trial ht P source s S sp wage W clear
    d₀ frame section_ group F
  have ah:h ≤ b:=le_trans (le_trans (le_max_left ..) (le_max_left ..)) age
  have late:kin ≤ b:=le_trans (le_trans (le_max_right ..) (le_max_left ..)) age
  have fixed:WilsonSingleHardRadius.first R simple ≤ b:=le_trans (le_trans (le_max_left ..) (le_max_right ..)) age
  have captured:WilsonCenteredCaptureClock.first R simple ≤ b:=le_trans (le_trans (le_max_right ..) (le_max_right ..)) age
  let enter:=read R N per W (show b+1 ≤ b+1+L by omega) (gust R.family.path N per N physical (b+1+L) live-trial (b+1+L)) s
  let total:=read R N per W (show b+1 ≤ N by omega) physical s-
    (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(trial (b+1) W).part s
  let rest (j:Fin L):=WilsonOriginalOccupiedJointEdge.ordinary R marks Ψ (N:=N) (show b+1 ≤ b+j.val+1 by omega)
    (P j) (trial (b+j.val+1)) s W
  let spring:=WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op (b+1) per) (R.family.path.β N per (b+1+1)) W
  let reg (j:Fin L):=(F j).bill (b+1) e (R.alloy.B.a.clock.hatBeta (b+j.val+1)) spring p
  let forced:=((e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card)*
    ∑j:Fin L,Poly.toll (S j) s/WilsonOriginalOccupiedDateShare.weight j.val
  have occ:‖total-enter-∑j:Fin L,rest j‖ ≤ forced:=
    hard b N per m k L ah mb live span way D Q π Γ Ψ course ticket physical hp trial ht P source s S sp wage W clear
  have due (j:Fin L):‖rest j‖ ≤ reg j:=by
    have cut:b+j.val+1<N:=by have jh:=j.isLt;omega
    exact WilsonOriginalMountedRegular.Filing.original π Γ Ψ course section_ group simple way D Q ticket
      mb (by omega) cut (by omega) (by omega) p ep (late.trans (by omega)) (F j) W clear
  have all:‖∑j:Fin L,rest j‖ ≤ ∑j:Fin L,reg j:=
    (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>due j)
  change ‖total‖ ≤ ‖enter‖+(∑j:Fin L,reg j)+forced
  calc
    ‖total‖=‖(enter+∑j:Fin L,rest j)+(total-enter-∑j:Fin L,rest j)‖:=by congr 1;abel
    _ ≤ (‖enter‖+‖∑j:Fin L,rest j‖)+‖total-enter-∑j:Fin L,rest j‖:=
      (norm_add_le ..).trans (add_le_add (norm_add_le ..) le_rfl)
    _ ≤ _:=add_le_add (add_le_add le_rfl all) occ

end YM.Integration.WilsonOriginalSignedPhysicalCorridor
end
