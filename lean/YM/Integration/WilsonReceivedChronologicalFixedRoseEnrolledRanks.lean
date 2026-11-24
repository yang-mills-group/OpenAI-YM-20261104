import YM.Integration.WilsonAddressedPublicFirstRoseTerms
import YM.Integration.WilsonReceivedChronologicalFixedRosePhysicalRanks
import YM.Integration.WilsonReceivedChronologicalFixedRoseOriginalAccount
import YM.Integration.WilsonOriginalObservedRosePublicConnected
import YM.Integration.WilsonReceivedChronologicalFixedRoseHeldCofactor
import YM.Integration.WilsonAddressedPublicFirstOrigin

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseEnrolledRanks
open Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Finset Function RG QuadraticLocal.Earn
open Extra.Multi Extra.Trajectories FVA1Physical Next.Rank Marker
open WilsonReceivedChronologicalFixedReserve (terms charges)
open WilsonReceivedChronologicalFixedRoseOriginalAccount (budget)
open WilsonReceivedChronologicalFixedRoseFittedDebit (Plan)
open WilsonOriginalObservedRosePublicConnected (cut)
open WilsonOriginalObservedRosePublicMesh (aperture)
open WilsonPositionThermometerGradedSource (grade)
open WilsonReceivedChronologicalFixedRoseHeldCofactor (demand)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "d" => (fun i:Fin 3=>(grade i).val)
local notation "fees" => fun _:Fin 3=>(0:ℕ)
local notation "count" => Fintype.card (Multi.Hot (Stock.census (Fin 3)))

open WilsonReceivedChronologicalFixedRosePhysicalRanks (entrance terminal print)

def start (target physical bank debt mesh cash:ℕ):ℕ:=
  max (WilsonReceivedChronologicalFixedRosePhysicalRanks.start R target physical bank debt mesh cash)
    (WilsonAddressedPublicFirstRoseTerms.order R 0)
def middle (target physical bank debt mesh cash pole:ℕ):ℕ:=start R target physical bank debt mesh cash+2*pole*3

private theorem printed {n:ℕ}{grades wages:Fin n→ℕ}{P:ℕ}
    (office:WilsonReceivedChronologicalFixedReserve.Terms grades wages P):P≤office.order:=by
  have cash:=office.cash
  have deep:=office.deep
  unfold WilsonOriginalFullRosterCouplingClock.work at cash
  omega

private theorem payable {n:ℕ}(grades wages:Fin n→ℕ){t bank mesh p h q pole:ℕ}
    (base:t+2+2*pole*n≤h)(atDate:h≤p)(last:t+2+bank+(mesh*14+1)≤q)
    (clock switch cash:ℕ){B:ℝ}(bp:0≤B)(C α η C₁:ℝ):
    (budget grades wages p clock pole h (t+2) h switch q cash B C α η η C₁).Affords t bank mesh 14:=
  ⟨bp,le_rfl,base.trans atDate,base,base,last⟩

theorem original (target physical bank debt mesh cash pole switch:ℕ)(B:ℝ)(bp:0≤B):
    let cutAt:=entrance target physical
    let goal:=terminal target physical bank mesh
    let Q:=print target physical bank debt mesh cash
    let head:=start R target physical bank debt mesh cash
    let earned:=middle R target physical bank debt mesh cash pole
    let P₀:=earned+1
    WilsonAddressedPublicFirstRoseTerms.order R earned=earned ∧ cut target bank debt mesh+9≤Q ∧ goal+WilsonOriginalTwoFlatIRSocketPower.debt 3 cash (count)≤Q+1 ∧
    Q≤(terms (d) (fees) P₀).order ∧ WilsonAddressedPublicFirstOrigin.ceiling R (d)≤(terms (d) (fees) P₀).order ∧
    earned=head+2*pole*3 ∧ ∀clock:ℕ,∀C α η C₁:ℝ,
      (budget (d) (fees) P₀ clock pole earned cutAt earned switch goal cash B C α η η C₁).Affords
        (demand target physical) (2*bank) (aperture mesh) 14:=by
  intro cutAt goal Q head earned P₀
  let issued:=terms (d) (fees) P₀
  have floor:Q≤head:=((le_max_left ..).trans (le_max_left ..)).trans (le_max_left ..)
  have ranked:WilsonAddressedPublicFirstOrigin.ceiling R (d)≤head:=((le_max_right ..).trans (le_max_left ..)).trans (le_max_left ..)
  have born:cutAt≤head:=(le_max_right ..).trans (le_max_left ..) 
  have span:head≤earned:=Nat.le_add_right .. 
  have sits:=printed issued
  have paid:earned≤ issued.order:=(Nat.le_succ _).trans sits
  have initial:cut target bank debt mesh+9≤Q:=Nat.le_max_left _ _
  have finish:goal+WilsonOriginalTwoFlatIRSocketPower.debt 3 cash count≤Q:=Nat.le_max_right _ _
  have receipt:WilsonAddressedPublicFirstRoseTerms.order R earned=earned:=by
    apply max_eq_left
    exact (le_max_right 0 _).trans ((le_max_right ..).trans span)
  refine ⟨receipt,initial,finish.trans (Nat.le_succ Q),floor.trans (span.trans paid),ranked.trans (span.trans paid),rfl,?_⟩
  intro clock C α η C₁
  exact payable (d) (fees) (Nat.add_le_add_right born _) (Nat.le_succ earned) (Nat.le_refl goal)
    clock switch cash bp C α η C₁
end YM.Integration.WilsonReceivedChronologicalFixedRoseEnrolledRanks
end
