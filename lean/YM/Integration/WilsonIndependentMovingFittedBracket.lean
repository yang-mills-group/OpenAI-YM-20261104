import YM.Integration.WilsonIndependentMovingFittedPower
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedBracket
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

open WilsonIndependentMovingFittedPower (thermal distance)

theorem monotone (g A η toll fee mag ε:ℝ)(h f Q:ℕ)(hot:0<g)(sign:0 ≤ η)(band:g^A ≤ ε)
    (paid:0 ≤ fee)(pos:0 ≤ toll)(size:0 ≤ mag):
    g^(Q+1)*(mag*((toll*ε^(-(h:ℝ)))^f*fee)*ε^(-η)) ≤
      mag*(toll^f*fee)*g^(((Q+1:ℕ):ℝ)-A*((h:ℝ)*f+η)):=by
  rw [←thermal g A η toll fee mag h f Q hot]
  have inlet:=Real.rpow_pos_of_pos hot A
  have εpos:=inlet.trans_le band
  have arm:=Real.rpow_le_rpow_of_nonpos inlet band (neg_nonpos.mpr (Nat.cast_nonneg h:0 ≤ (h:ℝ)))
  have term:=mul_le_mul_of_nonneg_left arm pos
  have group:=pow_le_pow_left₀ (mul_nonneg pos (Real.rpow_nonneg εpos.le _)) term f
  have passed:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right group paid) size
  have price:=Real.rpow_le_rpow_of_nonpos inlet band (neg_nonpos.mpr sign)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hot.le _)
  apply mul_le_mul passed price (Real.rpow_nonneg εpos.le _)
  exact mul_nonneg size (mul_nonneg (pow_nonneg (mul_nonneg pos (Real.rpow_nonneg inlet.le _)) _) paid)

variable (R:Run G)(W:Initialize G){n D k e u:ℕ}(p:h<D)(v:Rails h k u e)
local notation "T₀" => sectionAt R W false h
local notation "C" => Credit.leanC
local notation "slots" => Fin ((n+1)+1)
local notation "F₀" => (R.family.labels.level h)

theorem original (X:slots → CutsP (hol G) T₀ p v C C C C)(L:Torch (hol G) T₀ p v C C C)
    (t m N:ℕ)(mask:Bits (n+1))(fee:slots→ℝ)(q:ℕ)(stations:∀j,(X j).m=homes t m j)
    (g A B η:ℝ)(hot:0 < g)(ηpos:0 ≤ η)(band:g^A ≤ paceT L.L.V.draws.S m N)(aperture:paceT L.L.V.draws.S m t ≤ g^(-B))
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
  have viewpos:0 ≤ view:=(div_pos (L.L.V.draws.S.a_pos _) (L.L.V.draws.S.a_pos _)).le
  have far:=distance (flag 0) g view B h hot viewpos aperture
  have income:0 ≤ amount flag fee:=Finset.prod_nonneg (fun j _=>by split <;> simp_all [nn j])
  have pos:0 ≤ cost:=mul_nonneg (pow_nonneg (by dsimp [toll];positivity) _) income
  have fr:0 ≤ (if flag 0 then 1 else view^h):=ite_nonneg zero_le_one (pow_nonneg viewpos _)
  rw [abs_of_pos hot,WilsonIndependentMovingFittedScales.original R W p v X L t m N mask fee q stations]
  apply (monotone g A η toll (amount flag fee) (if flag 0 then 1 else view^h) (paceT L.L.V.draws.S m N)
    h (used flag) q hot ηpos band income (by dsimp [toll];positivity) fr).trans
  change (if flag 0 then 1 else view^h)*cost*g^upper ≤ cost*g^(upper-(if flag 0 then 0 else B*(h:ℝ)))
  rw [sub_eq_add_neg,Real.rpow_add hot]
  calc
    _ ≤ g^(-(if flag 0 then 0 else B*(h:ℝ)))*cost*g^upper:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right far pos) (Real.rpow_nonneg hot.le _)
    _ = _:=by ring

end YM.Integration.WilsonIndependentMovingFittedBracket
