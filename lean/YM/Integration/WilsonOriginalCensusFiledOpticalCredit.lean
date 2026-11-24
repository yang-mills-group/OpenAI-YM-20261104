import YM.Integration.WilsonOriginalCensusFiledTwoFlatCredit

/-! Coupling-power income of the emitted occupied gallery through both older flat receivers. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledOpticalCredit
open Filter MeasureTheory Multi
open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors AnalyticBridge.SectorAffine.Offset
open MeasureTheory Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m   ≤   i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "lamps" => rendered student (Ψ i).p oldG
local notation "gauge" => Tint.Patrol.report student P.output oldG
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "cash" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G*
  ((fig).produce (sheet).ratio.count*P.cost)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "marks" => Stock.census V

open WilsonRootedKioskOccupiedSlip WilsonOriginalFlatFiledMask


open WilsonOriginalOrdinaryFlatHulls WilsonCapturedPrimarySoftPartition
open WilsonThermometerUnitFilingCoarse WilsonOriginalFlatOccupiedRate WilsonOriginalFlatFiledMask
open WilsonReceivedQuietCrownOwner OPE.Therm
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "β" => R.alloy.B.a.clock.hatBeta i

private abbrev rowsOf {G : Gauge} {n : Side} {V X I : Type} [DecidableEq V] {o : V→Site n} {p : BudgetPoint}
    {U : Census V} (_ : Lamps X I G p o U) := I

open WilsonOriginalOccupiedCorridor WilsonOriginalOccupiedStencil
open private weaker from YM.Integration.WilsonOriginalOccupiedCorridor


variable (tariff:(Stock.census V).Mode→ℝ)
  (book:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead actors pieces grades
    order shelf seats physical P tariff)

private theorem roof_nonneg {n:Side}(b:BudgetPoint)(Z:Support n)(k t:ℕ)(fee H forced:ℝ)
    (hf:0≤fee)(hh:0≤H)(hk:0≤forced):
    0≤(t:ℝ)+4*(fee+WilsonOriginalFlatOccupiedRate.bill b Z 1 k)*H*forced:=by
  have h:0≤WilsonOriginalFlatOccupiedRate.bill b Z 1 k:=by
    unfold WilsonOriginalFlatOccupiedRate.bill WilsonOriginalFlatOccupiedRate.roof
    positivity
  exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hf h)) hh) hk)

private theorem restore {w A fee E val h forced roof:ℝ}
    (a:0 ≤ A)(e:0 ≤ E)(v:0 ≤ val)(r:0 ≤ roof)
    (one:w ≤ E*fee)(two:fee*val ≤ forced*roof)(three:A*E*forced ≤ h):
    (A*w)*val ≤ h*roof:=calc
  _ ≤ (A*(E*fee))*val:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left one a) v
  _ = (A*E)*(fee*val):=by ring
  _ ≤ (A*E)*(forced*roof):=mul_le_mul_of_nonneg_left two (mul_nonneg a e)
  _ = (A*E*forced)*roof:=by ring
  _ ≤ _:=mul_le_mul_of_nonneg_right three r

include cut in
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (ticket:TicketP R.alloy R.kit D Q){u b:ℕ}(floor:m ≤ u)(ub:u ≤ b)(bc : b < i)
    (fixed:WilsonSingleHardRadius.first R simple ≤ u)(capture:WilsonCenteredCaptureClock.first R simple ≤ b)
    (pole q:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(q+1)+8 ≤ order)(aged:q+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count q order k deep aged ep ≤ i)
    (x:Wallet actors)(s:(marks).Mode)(n:ℕ)(np:0<n)
    (stage:∀l,b ≤ l → n ≤ R.alloy.B.a.clock.J l)(load_ok:∀t:(marks).Mode,t.val.card ≤ n)
    (cap:∀l,b ≤ l → LocalComparison.forcedDivisor R.family l ≤ 1)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(home:center∈Z)
    (resident:∀a∈s.val,sites R (homes) bc.le a∈Z)
    (d a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep₀:0<e)
    (late:(eventually_atTop.mp (WilsonOriginalOccupiedOpticalRate.original R simple n d a p C cp e ep₀)).choose ≤ i-1)
    (span:((i-b:ℕ):ℝ) ≤ C*(1+Real.log (R.family.path.levels.clock.hatBeta i))^d):
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^q
    let src:=Stoop.radius P.w (max 1 (cash+debt))
    let fee:=Poly.toll (wallet R src bc.le) s
    let roof:=((shards (marks) s).card:ℝ)+4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b
    ∀{v:ℕ},u ≤ v → ∀(vb:v ≤ b),
      let amount:=‖WilsonOriginalOccupiedWindow.credit R (marks) (N:=N)
        (vb.trans bc.le) Ψ (book.row x) s (1:Config G (R.family.side v per))‖
      let restored:=(R.family.path.levels.clock.hatBeta i)^a*Poly.toll src s
      let limit:=e*(Pert.Asymptotics.regulatorRun R.family N per i)^p*roof
      restored*amount ≤ limit ∧ (1 ≤ restored → amount ≤ limit):=by
  intro debt src fee roof v uv vb amount restored limit
  have tick:i-1+1=i:=by omega
  have income:=(eventually_atTop.mp (WilsonOriginalOccupiedOpticalRate.original R simple n d a p C cp e ep₀)).choose_spec (i-1) late N per
  rw [tick] at income
  obtain ⟨tiny,paid⟩:=income cut.le (i-b) span
  have withdrawal:=WilsonOriginalCensusFiledTwoFlatCredit.original R hk D Q π Γ Ψ books hi cut ahead actors
    pieces grades order shelf seats physical P tariff book simple way course ticket floor ub bc fixed capture
    pole q sourced hardFloor deep aged ep opened x s n np stage load_ok cap tiny Z center home resident uv vb
  let height:=R.family.path.levels.clock.hatBeta i
  let z:=WilsonThermometerMixedCollarSubpower.scale height
  let dates:=i-b
  let growth:=Real.exp (n*(dates:ℝ)*z^3)
  have hp:0 ≤ height:=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have zp:0 ≤ z:=by dsimp [z,WilsonThermometerMixedCollarSubpower.scale];linarith only [le_max_left 0 (Real.log (Real.log height))]
  have fp:∀l,0<src l:=fun l=>div_pos (P.issued.earning.positive l) (zero_lt_one.trans_le (le_max_left ..))
  have f0:0 ≤ fee:=(Poly.worth (positive R src fp bc.le) s).le
  have earlier:=WilsonOriginalOccupiedClock.restored R simple bc.le (f:=i-1) (Nat.le_of_eq tick.symm) src fp s
  rw [tick] at earlier
  have meter:Real.exp (s.val.card*(dates:ℝ)*z^3) ≤ growth:=by
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast load_ok s) (Nat.cast_nonneg dates)) (pow_nonneg zp _)
  have price:Poly.toll src s ≤ growth*fee:=earlier.trans (mul_le_mul_of_nonneg_right meter f0)
  have r0:0 ≤ roof:=roof_nonneg (Ψ b).p Z _ _ fee _ _ f0
    (zero_le_one.trans (R.family.path.levels.fits.delayed b).le) (Real.sqrt_nonneg _)
  have bounded:restored*amount ≤ limit:=restore (pow_nonneg hp _) (Real.exp_pos _).le
    (norm_nonneg _) r0 price withdrawal paid
  exact ⟨bounded,fun h=>(le_mul_of_one_le_left (norm_nonneg _) h).trans bounded⟩

end YM.Integration.WilsonOriginalCensusFiledOpticalCredit
end
