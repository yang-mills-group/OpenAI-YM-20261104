import YM.Integration.WilsonIndependentMovingFittedSale
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedScales
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
open WilsonIndependentMovingFittedEpoch (debit)
open WilsonIndependentMovingRosterStableSale (homes)
open WilsonIndependentMovingFittedSale (gross)
variable {I:Type}[Fintype I]{G:Gauge}{h:ℕ}

def used (flag:I→Bool):ℕ:=(Finset.univ.filter fun j=>¬ flag j).card
def amount (flag:I→Bool)(fee:I→ℝ):ℝ:=∏j,if flag j then 1 else fee j

theorem scalar (flag:I→Bool)(fee:I→ℝ)(x:ℝ):
    (∏j,if flag j then 1 else x*fee j)=x^used flag*amount flag fee:=by
  classical
  have cut (j:I):(if flag j then 1 else x*fee j)=(if flag j then 1 else x)*(if flag j then 1 else fee j):=by
    cases flag j <;> simp
  simp only [cut,Finset.prod_mul_distrib,amount]
  congr 1
  rw [Finset.prod_ite]
  simp [used]

theorem exterior (F:Labels.Frame G h)(q:ℕ)(S:Schedule)(t m N:ℕ)(fee:ℝ):
    debit F q (paceT S t N) fee=(paceT S m t)^h*debit F q (paceT S m N) fee:=by
  have pos (r:ℕ):0<paceT S r N:=div_pos (S.a_pos _) (S.a_pos _)
  unfold WilsonIndependentMovingFittedEpoch.debit
  rw [Real.rpow_neg (pos t).le,Real.rpow_neg (pos m).le,Real.rpow_natCast,Real.rpow_natCast]
  simp only [paceT,div_pow]
  field_simp [(S.a_pos t).ne',(S.a_pos m).ne',(S.a_pos N).ne']

theorem paid {n:ℕ}(F:Labels.Frame G h)(q:ℕ)(S:Schedule)(t m N:ℕ)(flag:Fin ((n+1)+1)→Bool)
    (fee:Fin ((n+1)+1)→ℝ):
    (∏j,if flag j then 1 else debit F q (paceT S (homes t m j) N) (fee j))=
      (if flag 0 then 1 else (paceT S m t)^h)*
      (((Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*(paceT S m N)^(-(h:ℝ)))^used flag*amount flag fee):=by
  rw [←scalar flag fee]
  change _=(if flag 0 then 1 else (paceT S m t)^h)*(∏j,if flag j then 1 else debit F q (paceT S m N) (fee j))
  conv_lhs => rw [Fin.prod_univ_succ]
  conv_rhs => right;rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,homes]
  rw [exterior F q S t m N]
  cases flag 0 <;> simp [mul_assoc]

variable (R:Run G)(W:Initialize G){n D k e u:ℕ}(p:h<D)(v:Rails h k u e)
local notation "T₀" => sectionAt R W false h
local notation "C" => Credit.leanC
local notation "slots" => Fin ((n+1)+1)
local notation "F₀" => (R.family.labels.level h)

theorem original (X:slots → CutsP (hol G) T₀ p v C C C C)(L:Torch (hol G) T₀ p v C C C)
    (t m N:ℕ)(mask:Bits (n+1))(fee:slots→ℝ)(q:ℕ)(stations:∀j,(X j).m=homes t m j):
    let flag:=choose (n+1) mask
    let ε:=paceT L.L.V.draws.S m N
    let view:=paceT L.L.V.draws.S m t
    gross R W p v X L N mask fee q=(if flag 0 then 1 else view^h)*
      (((Fintype.card (Alma F₀):ℝ)*((q+1:ℕ):ℝ)*ε^(-(h:ℝ)))^used flag*amount flag fee):=by
  intro flag ε view
  simp only [gross,stations]
  exact paid F₀ q L.L.V.draws.S t m N flag fee

end YM.Integration.WilsonIndependentMovingFittedScales
