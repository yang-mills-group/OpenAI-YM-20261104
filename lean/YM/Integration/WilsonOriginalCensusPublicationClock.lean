import YM.Integration.WilsonMeasuredSemesterSubpower
import YM.Integration.WilsonOriginalOccupiedRaffleIndependent
import YM.Integration.WilsonOriginalOccupiedModeFactors
import YM.Integration.WilsonFirstReceivedEarnedFee
import YM.Integration.WilsonReceivedClosePhysicalBirths

/-! The ordinary finite roster's enrolment and both adjacent opening dates, before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPublicationClock
open Filter Finset AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Mentor
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {n k q order shelf p:ℕ}
  (grades:Fin n→ℕ)(pieces stages:ℕ)

structure Load (k q order shelf p:ℕ)(grades:Fin n→ℕ)(pieces stages:ℕ) : Prop where
  qfit : q ≤ order
  occupied : 1 ≤ pieces
  slots : n ≤ pieces
  count : pieces ≤ Burn.horizon k+2
  fit : (∑v,grades v) ≤ shelf
  stage : order+1 ≤ stages
  expense : order+(∑v,grades v) ≤ Burn.horizon k+2
  deep : 2*(p+1)+8 ≤ order
  aged : p+4 ≤ 3*k+2

variable (load:Load k q order shelf p grades pieces stages)
local notation "clock" => R.alloy.B.a.clock
local notation "D₀" => ((∑v,grades v)+1)

structure Open (i:ℕ) : Prop where
  level : shelf ≤ (clock).J i
  hard : 6*pieces ≤ (clock).J i
  halo : (eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose  ≤  i+1
  onset : WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ))  ≤  i
  opened : WilsonFirstReceivedEarnedFee.opening R simple pieces p order k load.deep load.aged
    (by norm_num:0<(1:ℝ))  ≤  i
  more : WilsonMeasuredSemesterSubpower.onset R pieces (by norm_num:0<(1:ℝ))  ≤  i
  cooled : (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose  ≤  i+1
  fresh : (eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple
    (Fintype.card (Fin n)) (order+shelf+1+D₀) (D₀+2))).choose  ≤  i

theorem original : ∀ᶠ i:ℕ in atTop,Open R simple grades pieces stages load i:=by
  filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop shelf,
    R.alloy.B.a.fits.deep.eventually_ge_atTop (6*pieces),
    eventually_ge_atTop (eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose,
    eventually_ge_atTop (WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ))),
    eventually_ge_atTop (WilsonFirstReceivedEarnedFee.opening R simple pieces p order k load.deep
      load.aged (by norm_num:0<(1:ℝ))),
    eventually_ge_atTop (WilsonMeasuredSemesterSubpower.onset R pieces (by norm_num:0<(1:ℝ))),
    eventually_ge_atTop (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose,
    eventually_ge_atTop (eventually_atTop.mp (WilsonOriginalOccupiedModeFactors.original R simple
      (Fintype.card (Fin n)) (order+shelf+1+D₀) (D₀+2))).choose] with i level hard halo onset opened more cool fresh
  exact ⟨level,hard,halo.trans (Nat.le_succ i),onset,opened,more,cool.trans (Nat.le_succ i),fresh⟩

theorem both : ∀ᶠ m:ℕ in atTop,∀i≥m,Open R simple grades pieces stages load i ∧
    Open R simple grades pieces stages load (i+1):=by
  obtain ⟨start,done⟩:=eventually_atTop.mp (original R simple grades pieces stages load)
  filter_upwards [eventually_ge_atTop start] with m hm
  intro i hi
  exact ⟨done i (hm.trans hi),done (i+1) ((hm.trans hi).trans (Nat.le_succ i))⟩

end YM.Integration.WilsonOriginalCensusPublicationClock
end
