import YM.Integration.WilsonIndependentMovingFittedScales
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedPower
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

open WilsonIndependentMovingFittedScales (amount used)

theorem thermal (g A η toll fee view:ℝ)(h n Q:ℕ)(hot:0<g):
    g^(Q+1)*(view*((toll*(g^A)^(-(h:ℝ)))^n*fee)*(g^A)^(-η))=
    view*(toll^n*fee)*g^(((Q+1:ℕ):ℝ)-A*((h:ℝ)*n+η)):=by
  have slots:((g^A)^(-(h:ℝ)))^n=g^(A*(-(h:ℝ))*(n:ℝ)):=by
    rw [Real.rpow_mul hot.le,Real.rpow_natCast,Real.rpow_mul hot.le]
  have wages:(g^A)^(-η)=g^(A*(-η)):= (Real.rpow_mul hot.le ..).symm
  rw [mul_pow,slots,wages,← Real.rpow_natCast g (Q+1)]
  calc
    _ = (view*(toll^n*fee))*(g^((Q+1:ℕ):ℝ)*g^(A*(-(h:ℝ))*(n:ℝ))*g^(A*(-η))):=by ring
    _ = _:=by rw [←Real.rpow_add hot,←Real.rpow_add hot];congr 2;ring

theorem distance (flag:Bool)(g mag B:ℝ)(h:ℕ)(hot:0<g)(placed:0 ≤ mag)(limit:mag ≤ g^(-B)):
    (if flag then 1 else mag^h) ≤ g^(-(if flag then 0 else B*(h:ℝ))):=by
  cases flag with
  | true=>simp
  | false=>
    change mag^h ≤ g^(-(B*(h:ℝ)))
    rw [←neg_mul,Real.rpow_mul hot.le,Real.rpow_natCast]
    exact pow_le_pow_left₀ placed limit _

variable (R:Run G)(W:Initialize G){n D k e u:ℕ}(p:h<D)(v:Rails h k u e)
local notation "T₀" => sectionAt R W false h
local notation "C" => Credit.leanC
local notation "slots" => Fin ((n+1)+1)
local notation "F₀" => (R.family.labels.level h)

theorem original (X:slots → CutsP (hol G) T₀ p v C C C C)(L:Torch (hol G) T₀ p v C C C)
    (t m N:ℕ)(mask:Bits (n+1))(fee:slots→ℝ)(q:ℕ)(stations:∀j,(X j).m=homes t m j)
    (g A B η:ℝ)(hot:0 < g)(scale:paceT L.L.V.draws.S m N=g^A)(aperture:paceT L.L.V.draws.S m t ≤ g^(-B))
    (nn:∀j,0 ≤ fee j):
    let flag:=choose (n+1) mask
    |g|^(q+1)*(gross R W p v X L N mask fee q*(paceT L.L.V.draws.S m N)^(-η)) ≤
      (((Fintype.card (Alma F₀):ℝ)*((q+1:ℕ):ℝ))^used flag*amount flag fee)*
        g^(((q+1:ℕ):ℝ)-A*((h:ℝ)*(used flag:ℝ)+η)-(if flag 0 then 0 else B*(h:ℝ))):=by
  intro flag
  let view:=paceT L.L.V.draws.S m t
  let toll:ℝ:=(Fintype.card (Alma F₀):ℝ)*((q+1:ℕ):ℝ)
  let cost:=toll^used flag*amount flag fee
  let upper:ℝ:=((q+1:ℕ):ℝ)-A*((h:ℝ)*(used flag:ℝ)+η)
  rw [abs_of_pos hot,WilsonIndependentMovingFittedScales.original R W p v X L t m N mask fee q stations,scale,
    thermal _ _ _ _ _ _ _ _ _ hot]
  change (if flag 0 then 1 else view^h)*cost*g^upper ≤ cost*g^(upper-(if flag 0 then 0 else B*(h:ℝ)))
  have viewpos:0 ≤ view:=(div_pos (L.L.V.draws.S.a_pos _) (L.L.V.draws.S.a_pos _)).le
  have far:=distance (flag 0) g view B h hot viewpos aperture
  have income:0 ≤ amount flag fee:=Finset.prod_nonneg (fun j _=>by split <;> simp_all [nn j])
  have pos:0 ≤ cost:=mul_nonneg (pow_nonneg (by dsimp [toll];positivity) _) income
  rw [sub_eq_add_neg,Real.rpow_add hot]
  calc
    _ ≤ g^(-(if flag 0 then 0 else B*(h:ℝ)))*cost*g^upper:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right far pos) (Real.rpow_nonneg hot.le _)
    _ = _:=by ring

end YM.Integration.WilsonIndependentMovingFittedPower
