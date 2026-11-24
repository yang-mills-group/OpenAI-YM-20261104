import YM.Integration.WilsonIndependentMovingFittedHearing
import YM.Integration.WilsonIndependentMovingFittedOptics
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedSale
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
open WilsonIndependentMovingFittedHearing (charge)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMovingFittedEpoch (debit)
local notation "rent" => charge n k out e u b h mask gap z zoom amp fee ε η
variable (axes:∀dir:Fin ((n+1)+1) → Alma (R.family.labels.level h),
  Heard R W p v out u b L.L.V X a fee t m s N (fun j=>axis (dir j) 0) φ amp y z gap o ε η)

def experiment (Q J:ℕ)(g:ℝ)(x:Fin 0 → YForest G):ℝ:=
  let d:=fun i=>dose (X i) (a i)
  let D:=factors X L N s flag d
  ‖cash Q g (embed (row X L N N s flag a d φ (centers y zoom) (fun _=>o) x))-
    ∑w:(j:slots) → Vote F₀ (flag j),(∏j,cash Q g (embed (D j (w j))))*
      cash J g (embed (unitRow X L N N s flag a φ (centers y zoom) (fun _=>o) w x))‖

def gross (Q:ℕ):ℝ:=∏j,if flag j then 1 else debit F₀ Q (paceT L.L.V.draws.S (X j).m N) (fee j)

def Sold:Prop:=∀(Q J:ℕ),Q ≤ e → J ≤ Q → ∀(g:ℝ),|g| ≤ 1 → ∀(x:Fin 0 → YForest G),Alma F₀ →
  experiment R W p v X L t m s N mask a φ y o Q J g x ≤
    ((((n+1)+1:ℕ):ℝ)+1)*|g|^(Q+1)*(gross R W p v X L N mask fee Q*ε^(-η))*(((Q+1:ℕ):ℝ)*rent)+
    numerical Q g (factors X L N s flag (fun j=>dose (X j) (a j)))*|g|^(J+1)*(((Q+1:ℕ):ℝ)*rent)

include same last upper axes in
theorem original (older:∀i,s ≤ (X i).m)
    (price:∀Q≤e,reserve Q (factors X L N s flag (fun j=>dose (X j) (a j))) ≤
      gross R W p v X L N mask fee Q*ε^(-η)):
    Sold R W p v X L t m s N mask a fee amp φ y z gap o ε η out u b:=by
  intro Q J top low g small x fallback
  let d:=fun j=>dose (X j) (a j)
  have paid:=WilsonIndependentMovingFittedHearing.original R W p v X L t m s N same last upper
    mask a fee amp φ y z gap o ε η out u b axes Q J top low g small older d x fallback
  apply paid.trans
  refine add_le_add ?_ le_rfl
  have dir:(i:slots) → Vote F₀ (flag i):=fun i=>Bool.recOn (motive:=Vote F₀) (flag i) fallback ()
  have beltFee:=WilsonIndependentMovingFittedHearing.purchased R W p v X L t m s N same last upper
    mask a fee amp φ y z gap o ε η out u b axes Q top x fallback dir
  have nn:0 ≤ (((Q+1:ℕ):ℝ)*rent):=(Finset.sum_nonneg (fun _ _=>norm_nonneg _)).trans beltFee
  apply mul_le_mul_of_nonneg_right _ nn
  exact mul_le_mul_of_nonneg_left (price Q top) (by positivity)

end YM.Integration.WilsonIndependentMovingFittedSale
