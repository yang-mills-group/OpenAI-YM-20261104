import YM.Integration.WilsonOriginalOccupiedProfileWindow
import YM.Integration.WilsonOriginalOccupiedJointEdge

/-! Joint microscopic hearing after every occupied original gallery in the optical interval is withdrawn. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedChargedTrial
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
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
    ∀(s:marks.Mode)(S:Fin L → ℝ),(∀j,0 ≤ S j) → (∀j:Fin L,(WilsonOriginalOccupiedSalary.debit (P j).regular (P j).hard)^s.val.card ≤
      (H (b+j.val+1))^a*((S j)^s.val.card*Poly.toll (P j).w s)) →
    ∀W:Config G (R.family.side (b+1) per),flags (Ψ (b+1)).p.threshold W=∅ →
    let enter:=read R N per W (show b+1 ≤ b+1+L by omega) (gust R.family.path N per N physical (b+1+L) live-trial (b+1+L)) s
    let rest:=∑j:Fin L,WilsonOriginalOccupiedJointEdge.ordinary R marks Ψ (N:=N)
      (show b+1 ≤ b+j.val+1 by omega) (P j) (trial (b+j.val+1)) s W
    ‖(read R N per W (show b+1 ≤ N by omega) physical s-
      (((R.family.path.rep N per (b+1)).eval W:ℂ)⁻¹)*(trial (b+1) W).part s)-enter-rest‖ ≤
      ((e*(regulatorRun R.family N per (b+1))^p)*(shards marks s).card)*
        ∑j:Fin L,(S j)^s.val.card/WilsonOriginalOccupiedDateShare.weight j.val:=by
  obtain ⟨start,settle⟩:=WilsonOriginalOccupiedProfileWindow.original R simple marks n d a p np load C e cp ep
  refine ⟨start,?_⟩
  intro b N per m k L age birth live span way D Q π Γ Ψ course ticket physical hp trial ht P source s S sp wage W clear enter rest
  let h:Fin L → ℂ:=fun j=>credit R marks (N:=N) (show b+1 ≤ b+j.val+1 by omega) Ψ (P j) s W
  let y:Fin L → ℂ:=fun j=>WilsonOriginalOccupiedJointEdge.ordinary R marks Ψ (N:=N)
    (show b+1 ≤ b+j.val+1 by omega) (P j) (trial (b+j.val+1)) s W
  have ready:∀j:Fin L,b+j.val+1 < b+1+L:=fun _=>by omega
  have origin:=WilsonOriginalJointTrialHearing.original R N per W (show b+1 ≤ b+1+L by omega) live physical hp trial ht s
  have ratio:∑i∈Ico (b+1) (b+1+L),fee R N per W trial i s=∑j:Fin L, fee R N per W trial (b+j.val+1) s:=by
    rw [sum_Ico_eq_sum_range,Fin.sum_univ_eq_sum_range (fun i:ℕ=>fee R N per W trial (b+i+1) s) L]
    rw [show b+1+L-(b+1)=L by omega];simp only [add_right_comm b 1]
  have terms:∀j:Fin L,fee R N per W trial (b+j.val+1) s=h j+y j:=fun j=>
    WilsonOriginalOccupiedJointEdge.original R marks π Γ Ψ course birth (by omega) ((ready j).trans_le live)
      (P j) trial (source j) (ht _ (by omega) (by omega)) (ht _ (by omega) (ready j).le) s W
  rw [ratio] at origin
  simp only [terms,sum_add_distrib] at origin
  rw [origin]
  change ‖enter+((∑j:Fin L,h j)+∑j:Fin L,y j)-enter-∑j:Fin L,y j‖ ≤ _
  rw [show enter+((∑j:Fin L,h j)+∑j:Fin L,y j)-enter-∑j:Fin L,y j=∑j:Fin L,h j by abel]
  exact settle b N per m k L age birth (fun j=>(ready j).le.trans live) span way D Q π Γ Ψ course ticket P s S sp wage W clear

end YM.Integration.WilsonOriginalOccupiedChargedTrial
