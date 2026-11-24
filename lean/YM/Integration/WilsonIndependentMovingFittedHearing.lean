import YM.Integration.WilsonIndependentMovingFittedMask
import YM.Integration.WilsonIndependentMovingFittedWindow
import YM.Integration.WilsonIndependentMovingRosterUnitCourse

/-! Each unit slot is the actual older two-home reading on the chosen
reporting course. The fitted numerical amplitudes do not enter its
income. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedHearing
open Filter Function Finset Matrix Lattice RG RG.Supply Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose XSpace.Cirrus Source Source.Drops Labels Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.AuxPlates
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentFittedExteriorRung (Seated)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMatchedCoverDate (age)
open WilsonIndependentMovingRosterNormalizedWallet (amount rent)
open WilsonIndependentMovingRosterNormalizedPortfolio (returned)
open WilsonIndependentMovingRosterNormalizedEarnings (contract edge)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open scoped Classical Topology BigOperators
open WilsonIndependentMovingRosterNormalizedEarnings (contract)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterCuts (ranks counts)
open WilsonIndependentMovingRosterStableSale (centers)
open WilsonIndependentFittedRosterFilms (Vote)
open WilsonIndependentMovingFittedRoster (unitRow row)
open WilsonIndependentMovingFittedCash (factors)
open WilsonIndependentMovingRosterUnitCourse (Heard)
open WilsonIndependentMatchedPivotSeat (axis ticket)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentFittedRosterCash (numerical reserve)
variable {G:Gauge}(R:Run G)(W:Initialize G){n h D k e u₀:ℕ}(p:h<D)(v:Rails h k u₀ e)
local notation "T₀" => sectionAt R W false h
local notation "C" => Credit.leanC
local notation "slots" => Fin ((n+1)+1)
local notation "F₀" => (R.family.labels.level h)
variable (X:Fin ((n+1)+1) → CutsP (hol G) (sectionAt R W false h) p v Credit.leanC Credit.leanC Credit.leanC Credit.leanC)(L:Torch (hol G) (sectionAt R W false h) p v Credit.leanC Credit.leanC Credit.leanC)(t m s N:ℕ)
    (same:∀i,(X i).L=L)(last:∀i,(X i).N=N)(upper:∀i,(X i).m+(X i).i=N)
    (mask:Bits (n+1))(a fee amp:Fin ((n+1)+1) → ℝ)(φ:Fin ((n+1)+1) → Rarity D)
    (y z gap:ℝ)(o:CellR)(ε η:ℝ)(out u b:ℕ)
local notation "zoom" => paceT L.L.V.draws.S m t
local notation "flag" => choose (n+1) mask
def charge (n k out e u b h:ℕ)(mask:Bits (n+1))(gap z mag:ℝ)(amp fee:Fin ((n+1)+1) → ℝ)(ε η:ℝ):ℝ:=
  contract n k out e u b h mask gap z mag amp*
    (∏j,if choose (n+1) mask j then fee j else 1)*ε^((counts (choose (n+1) mask):ℝ)/4-η)

local notation "rent" => charge n k out e u b h mask gap z zoom amp fee ε η
variable (axes:∀dir:Fin ((n+1)+1) → Alma (R.family.labels.level h),
  Heard R W p v out u b L.L.V X a fee t m s N (fun j=>axis (dir j) 0) φ amp y z gap o ε η)

include same last upper axes in
theorem purchased (Q:ℕ)(cap:Q ≤ e)(x:Fin 0 → YForest G)(fallback:Alma F₀):
    ∀w:(i:slots) → Vote F₀ (flag i),belt Q (embed (unitRow X L N N s flag a φ (centers y zoom)
      (fun _=>o) w x)) ≤ ((Q+1:ℕ):ℝ)*rent:=by
  apply WilsonIndependentMovingFittedMask.purchased X L N
    (fun i=>congrArg (fun T=>T.L.V) (same i)) last upper mask a φ (centers y zoom) (fun _=>o) s Q x fallback rent
  intro dir q hq
  have paid:=((axes dir) mask).2 q (hq.trans cap) x
  have costed (j:slots):WilsonIndependentMatchedProxyIncome.cost e (axis (dir j) 0)=1:=
    WilsonIndependentMatchedPivotSeat.ticket _ _ (Nat.zero_le _)
  simpa only [charge,WilsonIndependentMovingRosterNormalizedPortfolio.returned,costed] using paid

include same last upper axes in
theorem original (Q J:ℕ)(cap:Q ≤ e)(low:J ≤ Q)(g:ℝ)(small:|g| ≤ 1)(older:∀i,s ≤ (X i).m)
    (d:slots → Verse F₀)(x:Fin 0 → YForest G)(fallback:Alma F₀):
    ‖cash Q g (embed (row X L N N s flag a d φ (centers y zoom) (fun _=>o) x))-
      ∑w:(j:slots) → Vote F₀ (flag j),
        (∏j,cash Q g (embed (factors X L N s flag d j (w j))))*
        cash J g (embed (unitRow X L N N s flag a φ (centers y zoom) (fun _=>o) w x))‖ ≤
      ((((n+1)+1:ℕ):ℝ)+1)*|g|^(Q+1)*reserve Q (factors X L N s flag d)*(((Q+1:ℕ):ℝ)*rent)+
        numerical Q g (factors X L N s flag d)*|g|^(J+1)*(((Q+1:ℕ):ℝ)*rent):=by
  exact WilsonIndependentMovingFittedWindow.original X L N N s le_rfl same last upper older flag a d φ
    (centers y zoom) (fun _=>o) x Q J low g small _ (purchased R W p v X L t m s N
      same last upper mask a fee amp φ y z gap o ε η out u b axes Q cap x fallback)

end YM.Integration.WilsonIndependentMovingFittedHearing
